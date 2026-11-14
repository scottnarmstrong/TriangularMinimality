/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.CellData
public import SandierSerfaty.Sphere.Lower.RestCount
public import SandierSerfaty.Sphere.Lower.ChartPartition
public import SandierSerfaty.Sphere.Lower.GridSelect

/-!
# The family of quantized squares of a chart: specification and energy sums (sphere note, Theorem 6.14)

* `Lower.CellSpec`: the data `(tⱼ, n̄ⱼ, vⱼ)` attached to each cell `j ∈ cellFin R θ ρ` (`Lower.exists_cellSpec`).
* `Lower.gradDensity`: `E = |∇H_{1/4}|²` on `closedBall 0 (ρ - 1)` (zero outside), integrable with `∫ E ≤ truncDirichlet X ρ`.
* `Lower.sum_setIntegral_le`: the integrals of a nonnegative integrable function over disjoint sets add up to at most
  the total integral.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The per-cell data (side `tⱼ`, integer mass `n̄ⱼ`, density correction `vⱼ`). -/
@[expose] def CellSpec (n : ℕ) (R : ℝ) (θ : ℝ × ℝ) (ρ : ℝ) (t : ℤ × ℤ → ℝ) (nb : ℤ × ℤ → ℕ)
    (v : ℤ × ℤ → ℂ → ℝ) : Prop :=
  ∀ j ∈ cellFin R θ ρ, R - 1 ≤ t j ∧ t j ≤ R - 1 / 2 ∧
    (nb j : ℝ) = ∫ x in sqAt (cellAt R θ j) (t j), blowupDens n x ∧
    ContDiff ℝ ∞ (v j) ∧ (∀ x, Δ (v j) x = 2 * Real.pi * (blowupDens n x - nb j / t j ^ 2)) ∧
    ∫ x in sqAt (cellAt R θ j) (t j), ‖gradC (v j) x‖ ^ 2 ≤
      121 * Real.pi ^ 2 * mPlus ^ 2 * R ^ 6 / blowupScale n ^ 2 ∧
    mMinus ≤ nb j / t j ^ 2 ∧ nb j / t j ^ 2 ≤ mPlus ∧
    (∀ x ∈ sqAt (cellAt R θ j) (t j), |blowupDens n x - nb j / t j ^ 2| ≤ 4 * mPlus * R / blowupScale n) ∧
    1 ≤ nb j

theorem exists_cellSpec {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 2 ≤ R) (hbig : 1 ≤ mMinus * (R - 3 / 4))
    (θ : ℝ × ℝ) {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2 * blowupScale n) :
    ∃ (t : ℤ × ℤ → ℝ) (nb : ℤ × ℤ → ℕ) (v : ℤ × ℤ → ℂ → ℝ), CellSpec n R θ ρ t nb v := by
  have hR0 : 0 < R := by linarith
  have h : ∀ j ∈ cellFin R θ ρ, ∃ (t : ℝ) (nb : ℕ) (v : ℂ → ℝ), R - 1 ≤ t ∧ t ≤ R - 1 / 2 ∧
      (nb : ℝ) = ∫ x in sqAt (cellAt R θ j) t, blowupDens n x ∧
      ContDiff ℝ ∞ v ∧ (∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - nb / t ^ 2)) ∧
      ∫ x in sqAt (cellAt R θ j) t, ‖gradC v x‖ ^ 2 ≤
        121 * Real.pi ^ 2 * mPlus ^ 2 * R ^ 6 / blowupScale n ^ 2 ∧
      mMinus ≤ nb / t ^ 2 ∧ nb / t ^ 2 ≤ mPlus ∧
      (∀ x ∈ sqAt (cellAt R θ j) t, |blowupDens n x - nb / t ^ 2| ≤ 4 * mPlus * R / blowupScale n) ∧
      1 ≤ nb := by
    intro j hj
    refine exists_cell_data hn hR hbig _ fun x hx => ?_
    have := ((mem_cellFin hR0 hρ1).1 hj) hx
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  choose! t nb v ht using h
  exact ⟨t, nb, v, ht⟩

/-- `E = |∇H_{1/4}|²` on `closedBall 0 (ρ - 1)`, extended by zero. -/
@[expose] noncomputable def gradDensity {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) (x : ℂ) : ℝ :=
  (closedBall (0 : ℂ) (ρ - 1)).indicator (fun x => ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) x

theorem gradDensity_nonneg {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) (x : ℂ) : 0 ≤ gradDensity X ρ x := by
  unfold gradDensity
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

theorem measurable_gradDensity {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) : Measurable (gradDensity X ρ) := by
  unfold gradDensity
  exact ((measurable_norm.comp (measurable_gradC _)).pow_const 2).indicator measurableSet_closedBall

theorem gradDensity_eq {n : ℕ} (X : Fin n → ℂ) {ρ : ℝ} {x : ℂ} (hx : ‖x‖ ≤ ρ - 1) :
    gradDensity X ρ x = ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 := by
  unfold gradDensity
  rw [Set.indicator_of_mem (by simpa using hx)]

theorem integrable_gradDensity {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {ρ : ℝ}
    (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ) : Integrable (gradDensity X ρ) := by
  unfold gradDensity
  exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_E_closedBall hn X hX hsep hρ)

theorem integral_gradDensity_le {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {ρ : ℝ}
    (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ) :
    ∫ x, gradDensity X ρ x ≤ truncDirichlet X ρ := by
  unfold gradDensity
  rw [integral_indicator measurableSet_closedBall]
  exact integral_E_le_truncDirichlet hn X hX hsep hρ

theorem sum_setIntegral_le {ι : Type*} {J : Finset ι} {S : ι → Set ℂ} (hS : ∀ j ∈ J, MeasurableSet (S j))
    (hd : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (S j) (S j')) {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f) : ∑ j ∈ J, ∫ x in S j, f x ≤ ∫ x, f x := by
  rw [← integral_biUnion_finset J hS hd (fun j _ => hf.integrableOn)]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hf0)

end Lower

end Sphere

end SandierSerfaty

end
