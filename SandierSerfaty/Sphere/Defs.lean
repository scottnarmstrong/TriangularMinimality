/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Complex.Basic

/-!
# The sphere route: setting (sphere note, §2, Definitions 2.1 and 2.2)

The unit sphere `S² ⊂ ℝ³` is carried by `EuclideanSpace ℝ (Fin 3)` (Euclidean norm), the plane by `ℂ`.

* `Sphere.sphereEnergy`: the logarithmic energy `E(Y) = ∑_{i ≠ j} -log ‖yᵢ - yⱼ‖` over ordered pairs
  (Definition 2.1). It is real valued; on a configuration with a coincident pair the value of the
  corresponding term is the junk value `0` of `Real.log`, while the paper's `E` is `+∞` there. Every
  statement of the sphere route concerns configurations of pairwise distinct points, where the two
  agree.
* `Sphere.normalizedEnergy`: `𝔎(Y) = E(Y) - (½ - log 2) n² + (n/2) log n`.
* `Sphere.stereo` (`T`), `Sphere.lam` (`λ`), `Sphere.dens` (`µ`), `Sphere.potV` (`V`),
  `Sphere.invC` (`ι`), `Sphere.mercator` (`ℳ`) (Definition 2.2).
-/

open Complex

public section

namespace SandierSerfaty

namespace Sphere

/-- The ambient Euclidean space `ℝ³`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The logarithmic energy of `n` points, summed over ordered pairs `i ≠ j` (Definition 2.1). -/
@[expose] noncomputable def sphereEnergy {n : ℕ} (Y : Fin n → R3) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, -Real.log ‖Y i - Y j‖

/-- The normalized energy `𝔎(Y) = E(Y) - (½ - log 2) n² + (n/2) log n` (Definition 2.1). -/
@[expose] noncomputable def normalizedEnergy {n : ℕ} (Y : Fin n → R3) : ℝ :=
  sphereEnergy Y - (1 / 2 - Real.log 2) * (n : ℝ) ^ 2 + (n : ℝ) / 2 * Real.log n

/-- The stereographic chart `T` from the north pole `(0, 0, 1)`, `ℂ → S² ∖ {north}` (Definition 2.2). -/
@[expose] noncomputable def stereo (x : ℂ) : R3 :=
  !₂[2 * x.re / (1 + ‖x‖ ^ 2), 2 * x.im / (1 + ‖x‖ ^ 2), (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)]

/-- The conformal factor `λ(x) = 2 / (1 + |x|²)`. -/
@[expose] noncomputable def lam (x : ℂ) : ℝ := 2 / (1 + ‖x‖ ^ 2)

/-- The density `µ(x) = λ(x)² / (4π) = 1 / (π (1 + |x|²)²)`. -/
@[expose] noncomputable def dens (x : ℂ) : ℝ := lam x ^ 2 / (4 * Real.pi)

/-- The potential `V(x) = log (1 + |x|²)`. -/
@[expose] noncomputable def potV (x : ℂ) : ℝ := Real.log (1 + ‖x‖ ^ 2)

/-- The inversion `ι(x) = 1 / x̄` (`ι(0) = 0` by the Lean convention for `⁻¹`). -/
@[expose] noncomputable def invC (x : ℂ) : ℂ := (starRingEnd ℂ x)⁻¹

theorem stereo_apply_zero (x : ℂ) : stereo x 0 = 2 * x.re / (1 + ‖x‖ ^ 2) := by simp [stereo]

theorem stereo_apply_one (x : ℂ) : stereo x 1 = 2 * x.im / (1 + ‖x‖ ^ 2) := by simp [stereo]

theorem stereo_apply_two (x : ℂ) : stereo x 2 = (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2) := by simp [stereo]

/-- The Mercator map `ℳ(s, t) = (sech t cos s, sech t sin s, tanh t)`. -/
@[expose] noncomputable def mercator (s t : ℝ) : R3 :=
  !₂[Real.cos s / Real.cosh t, Real.sin s / Real.cosh t, Real.tanh t]

end Sphere

end SandierSerfaty

end
