/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.RemovableCutoff
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The capacity estimate in the plane

For the logarithmic cutoff `eta k c` (see `SandierSerfaty.Analysis.RemovableCutoff`), the profile
`Lam k` bounding `|Δ eta|` and `|∂ eta|` satisfies
`∫_ℂ Lam k ‖z - c‖ dz = polarConst * (k / 2)`, where `polarConst = 2 * area (unit disk) = 2π`.
In particular it tends to zero with `k`: a point has zero capacity in two dimensions.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- The constant `2 * area (unit disk)` of the polar-coordinate formula on `ℂ`. -/
@[expose] noncomputable def polarConst : ℝ := 2 * volume.real (ball (0 : ℂ) 1)

theorem integral_comp_norm_sub (c : ℂ) (f : ℝ → ℝ) :
    ∫ z : ℂ, f ‖z - c‖ = polarConst * ∫ y in Ioi (0 : ℝ), y * f y := by
  rw [integral_sub_right_eq_self (fun z : ℂ => f ‖z‖) c, integral_fun_norm_addHaar volume f]
  simp [polarConst, Complex.finrank_real_complex, smul_eq_mul]
  ring

theorem integrable_comp_norm_sub (c : ℂ) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun y => y * f y) (Ioi (0 : ℝ))) :
    Integrable (fun z : ℂ => f ‖z - c‖) := by
  have h : Integrable (fun z : ℂ => f ‖z‖) volume := by
    rw [integrable_fun_norm_addHaar volume]
    simpa [Complex.finrank_real_complex, smul_eq_mul] using hf
  exact h.comp_sub_right c

theorem lam_mul_integrableOn (k : ℝ) :
    IntegrableOn (fun y => y * Lam k y) (Ioi (0 : ℝ)) := by
  have ha := Real.exp_pos (-1 / k)
  have h1 : (fun y => y * Lam k y) = (Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))).indicator
      (fun y => y * (k ^ 2 * (y ^ 2)⁻¹)) := by
    funext y
    unfold Lam
    by_cases hy : y ∈ Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  rw [h1]
  refine Integrable.integrableOn ?_
  rw [integrable_indicator_iff measurableSet_Icc]
  refine ContinuousOn.integrableOn_Icc ?_
  intro y hy
  have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
  exact (continuousAt_id.mul (continuousAt_const.mul ((continuousAt_id.pow 2).inv₀
    (pow_ne_zero 2 hy0)))).continuousWithinAt

theorem integral_lam {k : ℝ} (hk : 0 < k) :
    ∫ y in Ioi (0 : ℝ), y * Lam k y = k / 2 := by
  have ha := Real.exp_pos (-1 / k)
  have hab : Real.exp (-1 / k) ≤ Real.exp (-1 / (2 * k)) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ hk (by positivity)]; nlinarith
  have h1 : (fun y => y * Lam k y) = (Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))).indicator
      (fun y => k ^ 2 * y⁻¹) := by
    funext y
    unfold Lam
    by_cases hy : y ∈ Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))
    · have hy0 : y ≠ 0 := (ha.trans_le hy.1).ne'
      simp only [Set.indicator_of_mem hy]
      field_simp
    · simp [Set.indicator_of_notMem hy]
  have hI : Ioi (0 : ℝ) ∩ Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k))) =
      Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k))) :=
    Set.inter_eq_right.2 (fun y hy => ha.trans_le hy.1)
  rw [h1, setIntegral_indicator measurableSet_Icc, hI, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const_mul,
    integral_inv_of_pos ha (Real.exp_pos _), Real.log_div (Real.exp_pos _).ne' ha.ne',
    Real.log_exp, Real.log_exp]
  field_simp
  ring

theorem integrable_lam_comp (c : ℂ) (k : ℝ) :
    Integrable (fun z : ℂ => Lam k ‖z - c‖) :=
  integrable_comp_norm_sub c (lam_mul_integrableOn k)

theorem integral_lam_comp (c : ℂ) {k : ℝ} (hk : 0 < k) :
    ∫ z : ℂ, Lam k ‖z - c‖ = polarConst * (k / 2) := by
  rw [integral_comp_norm_sub, integral_lam hk]

end SandierSerfaty.Weyl

end
