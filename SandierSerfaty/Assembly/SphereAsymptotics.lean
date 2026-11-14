/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Assembly.Statements
public import SandierSerfaty.Sphere.Bridge.LogEnergy
public import SandierSerfaty.Sphere.Bridge.Input63
public import SandierSerfaty.Sphere.Bridge.RingConstant
public import SandierSerfaty.Sphere.Lower.LowerBound
public import SandierSerfaty.Sphere.Ring.RingBound

/-!
# The sphere asymptotics from the square-torus bound (paper Corollary 1.3)

`sphereAsymptotics_of_torusBound : TorusBoundStatement → SphereAsymptoticsStatement` has *exactly* the conclusion of `sphereLogEnergy_asymptotics`
(paper Corollary 1.3); `SphereAsymptoticsStatement` is that statement written out as a `Prop`.

Route (`Sphere.Bridge.sphereLogEnergyAsymptotics_iff`): the asymptotics are equivalent to
`𝔎(Y) = C_tri n + o(n)` for the minimizers `Y` of `n ≥ 2` points. All minimizers of the same `n` have the
same energy (`Sphere.IsSphereMinimizer.normalizedEnergy_eq`). For a chosen minimizer `Y_n`, the remainder
`r n = 𝔎(Y_n) - C_tri n` satisfies `|r n| ≤ ε n` for large `n`, by the lower bound
(`Sphere.Lower.lower_bound`, Theorem 6.14, from the square-torus bound, Input 6.3 and the ring bound; both of the latter are
proved: `Sphere.Bridge.input63Statement`, `Sphere.Lower.ringBoundStatement`) and the upper bound
(`Sphere.IsSphereMinimizer.normalizedEnergy_le_eventually`, with `C_ring = C_tri`).
-/

open Filter Asymptotics

public section

namespace SandierSerfaty

namespace Assembly

/-- The statement of `sphereLogEnergy_asymptotics` (paper Corollary 1.3), as a `Prop`. -/
@[expose] def SphereAsymptoticsStatement : Prop :=
  ∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
    sphereLogEnergy n =
      ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + bhsConstant * n +
        r n : ℝ) : EReal)

end Assembly

namespace Sphere

/-- All minimizers of the same number of points have the same normalized energy. -/
theorem IsSphereMinimizer.normalizedEnergy_eq {n : ℕ} {Y Z : Fin n → R3} (hY : IsSphereMinimizer Y)
    (hZ : IsSphereMinimizer Z) : normalizedEnergy Y = normalizedEnergy Z := by
  have h1 := hY.le Z hZ.norm_eq hZ.injective
  have h2 := hZ.le Y hY.norm_eq hY.injective
  unfold normalizedEnergy
  linarith

end Sphere

namespace Assembly

open Sphere

/-- **The sphere asymptotics from the square-torus bound** (paper Corollary 1.3; exactly the statement of
`sphereLogEnergy_asymptotics`). -/
theorem sphereAsymptotics_of_torusBound (h : TorusBoundStatement) : SphereAsymptoticsStatement := by
  refine Bridge.sphereLogEnergyAsymptotics_iff.2 ?_
  classical
  let K : ℕ → ℝ := fun n =>
    if hn : 2 ≤ n then normalizedEnergy (Classical.choose (exists_isSphereMinimizer n)) else 0
  refine ⟨fun n => K n - Lower.cTri * n, ?_, fun n hn Y hY => ?_⟩
  · rw [isLittleO_iff]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := Lower.lower_bound h Bridge.input63Statement Lower.ringBoundStatement ε hε
    obtain ⟨N₀, hN₀⟩ := IsSphereMinimizer.normalizedEnergy_le_eventually hε
    filter_upwards [eventually_ge_atTop (max (max n₀ N₀) 2)] with n hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hnn₀ : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN₀ : N₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hmin := Classical.choose_spec (exists_isSphereMinimizer n)
    have hK : K n = normalizedEnergy (Classical.choose (exists_isSphereMinimizer n)) := by
      simp [K, hn2]
    have hlo := hn₀ n hnn₀ _ hmin
    have hup := hN₀ n hnN₀ _ hmin
    rw [Bridge.ringConstant_eq_cTri] at hup
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, abs_le]
    rw [← hK] at hlo hup
    constructor <;> nlinarith
  · have hmin := Classical.choose_spec (exists_isSphereMinimizer n)
    have hK : K n = normalizedEnergy (Classical.choose (exists_isSphereMinimizer n)) := by
      simp [K, hn]
    simp only [hK, IsSphereMinimizer.normalizedEnergy_eq hY hmin]
    ring

end Assembly

end SandierSerfaty

end
