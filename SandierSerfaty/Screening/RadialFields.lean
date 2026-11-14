/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Pairing
public import SandierSerfaty.Screening.LipschitzApprox
public import SandierSerfaty.Screening.TruncDiff
public import SandierSerfaty.Analysis.PolarMean
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial fields `W^r`, `u^r`, `K^r` (screening note, Lemma 4.5)

The screening note, Lemma 4.5 (`lem:radial`), book sign. For `r > 0`:

* `radialU r = (π r²)⁻¹ 1_{B(0,r)}` (`u^r`), `radialW r y = y r⁻² 1_{B(0,r)}(y)` (`W^r`);
* `radialK r = ∇f_r + W^r` (`K^r`), so `K^r(y) = -y |y|⁻² (1 - |y|²/r²)₊` (`radialK_eq_zero_of_lt`), and `K^r - ∇f_r = W^r` holds pointwise by definition.

Main results, for every Lipschitz `φ` (the screening note asks for compact support; it is not needed since
`W^r`, `∇f_r` and `u^r` are integrable) and every centre `q`:

* (a) `integral_inner_radialW`: `∫ ⟪W^r(x - q), ∇φ(x)⟫ = 2π (⨍_{∂B(q,r)} φ - ∫ u^r(x - q) φ(x))`;
* (b) `integral_inner_radialK`: `∫ ⟪K^r(x - q), ∇φ(x)⟫ = 2π (φ(q) - ∫ u^r(x - q) φ(x))`, i.e.
  `-div K^r = 2π (δ₀ - u^r)`; `integral_inner_gradient_truncLog_lipschitz`:
  `∫ ⟪∇f_r(x - q), ∇φ(x)⟫ = 2π (φ(q) - ⨍_{∂B(q,r)} φ)`;
* (c) `norm_radialW_le` (`|W^r| ≤ 1/r`), `integral_norm_sq_radialW` (`∫ |W^r|² = π/2`),
  `integral_radialU` (`∫ u^r = 1`),
  `radialK_eq_zero_of_lt` (`supp K^r ⊆ B̄(0, r)`); for `r = ¼`: `norm_radialW_quarter_le`
  (`|W| ≤ 4`), `radialU_quarter_of_mem`
  (`u = 16/π` on `B(0, ¼)`).

Note: when the test function is `F_p = f_{α_p,¼}(· - p)`, use the continuous representative
`truncDiff`.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal ContDiff Real

public section

namespace SandierSerfaty.Screening

/-- `u^r = (π r²)⁻¹ 1_{B(0,r)}` (screening note, Lemma 4.5). -/
@[expose] noncomputable def radialU (r : ℝ) (y : ℂ) : ℝ :=
  (ball (0 : ℂ) r).indicator (fun _ => (π * r ^ 2)⁻¹) y

/-- `W^r(y) = y r⁻² 1_{B(0,r)}(y)` (screening note, Lemma 4.5). -/
@[expose] noncomputable def radialW (r : ℝ) (y : ℂ) : ℂ :=
  (ball (0 : ℂ) r).indicator (fun y => (r ^ 2)⁻¹ • y) y

/-- `K^r = ∇f_r + W^r`, i.e. `K^r(y) = -y |y|⁻² (1 - |y|²/r²)₊` (screening note, Lemma 4.5). -/
@[expose] noncomputable def radialK (r : ℝ) (y : ℂ) : ℂ :=
  gradient (truncLog r) y + radialW r y

/-! ### Elementary properties (Lemma 4.5(c)) -/

section Basic

variable {r : ℝ}

theorem radialK_sub_gradient (r : ℝ) (y : ℂ) : radialK r y - gradient (truncLog r) y = radialW r y := by
  simp [radialK]

theorem radialW_of_mem {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) : radialW r y = (r ^ 2)⁻¹ • y :=
  indicator_of_mem hy _

theorem radialW_of_notMem {y : ℂ} (hy : y ∉ ball (0 : ℂ) r) : radialW r y = 0 :=
  indicator_of_notMem hy _

theorem radialU_of_mem {y : ℂ} (hy : y ∈ ball (0 : ℂ) r) : radialU r y = (π * r ^ 2)⁻¹ :=
  indicator_of_mem hy _

theorem radialU_of_notMem {y : ℂ} (hy : y ∉ ball (0 : ℂ) r) : radialU r y = 0 :=
  indicator_of_notMem hy _

theorem radialU_nonneg (r : ℝ) (y : ℂ) : 0 ≤ radialU r y :=
  indicator_nonneg (fun _ _ => by positivity) _

theorem norm_radialW_eq (hr : 0 < r) (y : ℂ) :
    ‖radialW r y‖ = (Iio r).indicator (fun t => t / r ^ 2) ‖y‖ := by
  by_cases hy : y ∈ ball (0 : ℂ) r
  · have hy' : ‖y‖ ∈ Iio r := by simpa using hy
    rw [radialW_of_mem hy, indicator_of_mem hy', norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  · have hy' : ‖y‖ ∉ Iio r := by simpa using hy
    rw [radialW_of_notMem hy, indicator_of_notMem hy', norm_zero]

/-- `|W^r| ≤ 1/r`. -/
theorem norm_radialW_le (hr : 0 < r) (y : ℂ) : ‖radialW r y‖ ≤ r⁻¹ := by
  rw [norm_radialW_eq hr]
  by_cases hy : ‖y‖ ∈ Iio r
  · rw [indicator_of_mem hy, div_le_iff₀ (by positivity)]
    have : ‖y‖ < r := hy
    calc ‖y‖ ≤ r := this.le
      _ = r⁻¹ * r ^ 2 := by field_simp
  · rw [indicator_of_notMem hy]; positivity

theorem measurable_radialW (r : ℝ) : Measurable (radialW r) :=
  show Measurable fun y => (ball (0 : ℂ) r).indicator (fun y => (r ^ 2)⁻¹ • y) y from
    (measurable_id.const_smul ((r ^ 2)⁻¹ : ℝ)).indicator measurableSet_ball

theorem integrable_radialW (hr : 0 < r) : Integrable (radialW r) := by
  have h : IntegrableOn (radialW r) (closedBall (0 : ℂ) r) :=
    Measure.integrableOn_of_bounded (M := r⁻¹) (measure_closedBall_lt_top).ne
      (measurable_radialW r).aestronglyMeasurable
      (Eventually.of_forall fun y => norm_radialW_le hr y)
  exact h.integrable_of_forall_notMem_eq_zero fun y hy =>
    radialW_of_notMem fun h' => hy (ball_subset_closedBall h')

theorem integrable_radialU (r : ℝ) : Integrable (radialU r) :=
  (integrable_indicator_iff measurableSet_ball).2
    (integrableOn_const measure_ball_lt_top.ne)

theorem integrable_radialK (hr : 0 < r) : Integrable (radialK r) :=
  (integrable_gradient_truncLog_zero hr).add (integrable_radialW hr)

/-- `∫ u^r = 1`. -/
theorem integral_radialU (hr : 0 < r) : ∫ y, radialU r y = 1 := by
  unfold radialU
  rw [integral_indicator_const _ measurableSet_ball, Measure.real, Complex.volume_ball,
    smul_eq_mul]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  field_simp

/-- `K^r(y) = 0` for `|y| > r`, so `supp K^r ⊆ B̄(0, r)`. -/
theorem radialK_eq_zero_of_lt (hr : 0 < r) {y : ℂ} (hy : r < ‖y‖) : radialK r y = 0 := by
  rw [radialK, gradient_truncLog_of_gt hr hy, radialW_of_notMem (by simpa using hy.le), add_zero]

/-- Radial integrals: `∫ F(|y|) dy = 2π ∫₀^∞ t F(t) dt`. -/
theorem integral_fun_norm_complex (F : ℝ → ℝ) :
    ∫ y : ℂ, F ‖y‖ = 2 * π * ∫ t in Ioi (0 : ℝ), t * F t := by
  rw [integral_fun_norm_addHaar volume F, Complex.finrank_real_complex, Measure.real,
    Complex.volume_ball]
  simp [smul_eq_mul, mul_assoc]

theorem integral_Ioi_indicator_Iio (hr : 0 < r) (G : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), t * (Iio r).indicator G t = ∫ t in (0 : ℝ)..r, t * G t := by
  have h : (fun t => t * (Iio r).indicator G t) = (Iio r).indicator fun t => t * G t := by
    ext t; by_cases ht : t ∈ Iio r <;> simp [ht]
  rw [h, setIntegral_indicator measurableSet_Iio, intervalIntegral.integral_of_le hr.le,
    integral_Ioc_eq_integral_Ioo, Ioi_inter_Iio]

/-- `∫ |W^r|² = π/2`. -/
theorem integral_norm_sq_radialW (hr : 0 < r) : ∫ y, ‖radialW r y‖ ^ 2 = π / 2 := by
  have h : (fun y => ‖radialW r y‖ ^ 2) =
      fun y => (Iio r).indicator (fun t => (t / r ^ 2) ^ 2) ‖y‖ := by
    ext y
    rw [norm_radialW_eq hr]
    by_cases hy : ‖y‖ ∈ Iio r <;> simp [hy]
  rw [h, integral_fun_norm_complex, integral_Ioi_indicator_Iio hr]
  have : (fun t : ℝ => t * (t / r ^ 2) ^ 2) = fun t => (r ^ 4)⁻¹ * t ^ 3 := by
    ext t; field_simp
  rw [this, intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  ring

/-- For `r = ¼`: `|W| ≤ 4`. -/
theorem norm_radialW_quarter_le (y : ℂ) : ‖radialW (1 / 4) y‖ ≤ 4 := by
  have := norm_radialW_le (r := 1 / 4) (by norm_num) y
  norm_num at this ⊢; exact this

/-- For `r = ¼`: `u = 16/π` on `B(0, ¼)`. -/
theorem radialU_quarter_of_mem {y : ℂ} (hy : y ∈ ball (0 : ℂ) (1 / 4)) :
    radialU (1 / 4) y = 16 / π := by
  rw [radialU_of_mem hy]; field_simp; norm_num

end Basic

/-! ### The weak identities (Lemma 4.5(a), (b)) -/

section Weak

open Torus

variable {r : ℝ}

/-- The integrand of `∫ ⟪W^r, ∇φ⟫` as an indicator of the punctured disc. -/
theorem inner_radialW_eq_indicator (φ : ℂ → ℝ) (x : ℂ) :
    inner ℝ (radialW r x) (gradient φ x) =
      {x : ℂ | ‖x‖ ∈ Ioo 0 r}.indicator (fun x => (r ^ 2)⁻¹ * fderiv ℝ φ x x) x := by
  by_cases hx : x ∈ ball (0 : ℂ) r
  · by_cases hx0 : x = 0
    · subst hx0
      have h0 : (0 : ℂ) ∉ {x : ℂ | ‖x‖ ∈ Ioo 0 r} := by simp
      rw [radialW_of_mem hx, smul_zero, inner_zero_left, indicator_of_notMem h0]
    · have hm : x ∈ {x : ℂ | ‖x‖ ∈ Ioo 0 r} := ⟨norm_pos_iff.2 hx0, by simpa using hx⟩
      rw [radialW_of_mem hx, indicator_of_mem hm, real_inner_smul_left, real_inner_comm,
        inner_gradient_left]
  · have hm : x ∉ {x : ℂ | ‖x‖ ∈ Ioo 0 r} := fun h => hx (by simpa using h.2)
    rw [radialW_of_notMem hx, inner_zero_left, indicator_of_notMem hm]

theorem ae_eq_ball_punctured (hr : 0 < r) :
    {x : ℂ | ‖x‖ ∈ Ioo 0 r} =ᵐ[volume] (ball (0 : ℂ) r : Set ℂ) := by
  have h : ball (0 : ℂ) r = {x : ℂ | ‖x‖ ∈ Ioo 0 r} ∪ {0} := by
    ext x
    by_cases hx : x = 0
    · subst hx; simp [hr]
    · simp [hx, norm_pos_iff]
  rw [h]
  exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (measure_singleton 0))).symm

/-- **Lemma 4.5(a), smooth case, centre `0`**: `∫ ⟪W^r, ∇φ⟫ = 2π (⨍_{∂B(0,r)} φ - ∫ u^r φ)`. -/
theorem integral_inner_radialW_zero_of_contDiff (hr : 0 < r) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ x, inner ℝ (radialW r x) (gradient φ x) =
      2 * π * (Real.circleAverage φ 0 r - ∫ x, radialU r x * φ x) := by
  set S : Set ℂ := {x : ℂ | ‖x‖ ∈ Ioo 0 r} with hS
  have hSm : MeasurableSet S := measurable_norm measurableSet_Ioo
  have hD : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hDc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  -- `f₃ = r⁻² ∂φ(x)[x] + 2 r⁻² φ`; `ρ f₃(ρ e^{iθ}) = r⁻² d/dρ (ρ² φ(ρ e^{iθ}))`
  set f₃ : ℂ → ℝ := fun x => (r ^ 2)⁻¹ * fderiv ℝ φ x x + 2 * (r ^ 2)⁻¹ * φ x with hf₃
  have hf₃c : Continuous f₃ := by
    have : Continuous fun x => fderiv ℝ φ x x := hDc.clm_apply continuous_id
    simp only [hf₃]; fun_prop
  have hcomp : IsCompact (closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
  have hSsub : S ⊆ closedBall 0 r := fun x hx => by simpa using hx.2.le
  have hint3 : IntegrableOn f₃ S := (hf₃c.continuousOn.integrableOn_compact hcomp).mono_set hSsub
  have hintφ : IntegrableOn (fun x => 2 * (r ^ 2)⁻¹ * φ x) S :=
    ((by fun_prop : Continuous fun x => 2 * (r ^ 2)⁻¹ * φ x).continuousOn.integrableOn_compact
      hcomp).mono_set hSsub
  have hsplit : ∀ x, (r ^ 2)⁻¹ * fderiv ℝ φ x x = f₃ x - 2 * (r ^ 2)⁻¹ * φ x := fun x => by
    simp only [hf₃]; ring
  rw [integral_congr_ae (Eventually.of_forall (inner_radialW_eq_indicator φ)),
    integral_indicator hSm]
  simp only [hsplit]
  rw [integral_sub hint3 hintφ, integral_const_mul]
  -- the `f₃` term in polar coordinates
  have hpolar : ∫ x in S, f₃ x = ∫ θ in Ioo (-π) π, φ ((r : ℂ) * dir θ) := by
    rw [integral_polar_radial measurableSet_Ioo (fun _ h => h.1)]
    · refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
      have hder : ∀ ρ : ℝ, HasDerivAt (fun ρ : ℝ => ρ ^ 2 * φ ((ρ : ℂ) * dir θ))
          (ρ * f₃ ((ρ : ℂ) * dir θ) * r ^ 2) ρ := by
        intro ρ
        have h1 := (hasDerivAt_pow 2 ρ).mul (hasDerivAt_ray_of_differentiableAt (θ := θ) (r := ρ) rfl (hD _))
        convert h1 using 1
        have hlin : fderiv ℝ φ ((ρ : ℂ) * dir θ) ((ρ : ℂ) * dir θ) =
            ρ * fderiv ℝ φ ((ρ : ℂ) * dir θ) (dir θ) := by
          rw [show ((ρ : ℂ) * dir θ) = ρ • dir θ from (Complex.real_smul).symm, map_smul,
            smul_eq_mul]
        simp only [hf₃, hlin]
        field_simp
        ring
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
      have hcont : Continuous fun ρ : ℝ => ρ * f₃ ((ρ : ℂ) * dir θ) * r ^ 2 := by
        have : Continuous fun ρ : ℝ => (ρ : ℂ) * dir θ := by fun_prop
        exact (continuous_id.mul (hf₃c.comp this)).mul continuous_const
      have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ => hder ρ)
        (hcont.intervalIntegrable 0 r)
      have hF' : (∫ ρ in (0 : ℝ)..r, ρ * f₃ ((ρ : ℂ) * dir θ)) * r ^ 2 =
          r ^ 2 * φ ((r : ℂ) * dir θ) := by
        rw [← intervalIntegral.integral_mul_const, hF]; simp
      have hr2 : r ^ 2 ≠ 0 := by positivity
      calc ∫ ρ in (0 : ℝ)..r, ρ * f₃ ((ρ : ℂ) * dir θ)
          = (∫ ρ in (0 : ℝ)..r, ρ * f₃ ((ρ : ℂ) * dir θ)) * r ^ 2 / r ^ 2 :=
            (mul_div_cancel_right₀ _ hr2).symm
        _ = φ ((r : ℂ) * dir θ) := by rw [hF']; exact mul_div_cancel_left₀ _ hr2
    · have hc : Continuous fun p : ℝ × ℝ => p.1 * f₃ ((p.1 : ℂ) * dir p.2) :=
        continuous_fst.mul (hf₃c.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
          (continuous_dir.comp continuous_snd)))
      exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [hpolar]
  -- the circle average
  have hcirc : ∫ θ in Ioo (-π) π, φ ((r : ℂ) * dir θ) = 2 * π * Real.circleAverage φ 0 r := by
    have h := integral_Ioo_circleMap_eq φ r
    simp only [circleMap_zero_eq] at h
    rw [h, Real.circleAverage_def, smul_eq_mul]
    simp only [circleMap_zero_eq]
    field_simp
  -- the `u^r` term
  have hu : ∫ x, radialU r x * φ x = (π * r ^ 2)⁻¹ * ∫ x in S, φ x := by
    have : (fun x => radialU r x * φ x) = (ball (0 : ℂ) r).indicator fun x => (π * r ^ 2)⁻¹ * φ x := by
      ext x
      by_cases hx : x ∈ ball (0 : ℂ) r
      · rw [radialU_of_mem hx, indicator_of_mem hx]
      · rw [radialU_of_notMem hx, indicator_of_notMem hx, zero_mul]
    rw [this, integral_indicator measurableSet_ball, integral_const_mul,
      setIntegral_congr_set (ae_eq_ball_punctured hr)]
  rw [hcirc, hu]
  field_simp

/-- **Lemma 4.5(a), centre `0`**, Lipschitz test functions. -/
theorem integral_inner_radialW_zero (hr : 0 < r) {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (radialW r x) (gradient φ x) =
      2 * π * (Real.circleAverage φ 0 r - ∫ x, radialU r x * φ x) := by
  obtain ⟨ψ, δ, hδ, hψ, hψφ, hψB, hlim⟩ := exists_smooth_approx_lipschitz hφ
  have hL := tendsto_integral_inner_gradient MeasurableSet.univ (integrable_radialW hr).integrableOn
    (fun n x hx => absurd (mem_univ x) hx) hψB hlim
  have hEq : ∀ n, ∫ x, inner ℝ (radialW r x) (gradient (ψ n) x) =
      2 * π * (Real.circleAverage (ψ n) 0 r - ∫ x, radialU r x * ψ n x) := fun n =>
    integral_inner_radialW_zero_of_contDiff hr ((hψ n).of_le (by simp))
  simp only [hEq] at hL
  refine tendsto_nhds_unique hL (tendsto_const_nhds.mul
    ((tendsto_circleAverage_of_approx (fun n => (hψ n).continuous) hφ.continuous hδ hψφ 0 r).sub
      ?_))
  -- `∫ u^r ψₙ → ∫ u^r φ`
  have hset : ∀ g : ℂ → ℝ, ∫ x, radialU r x * g x = ∫ x in closedBall (0 : ℂ) r, radialU r x * g x :=
    fun g => (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [radialU_of_notMem fun h => hx (ball_subset_closedBall h), zero_mul]).symm
  simp only [hset]
  exact tendsto_setIntegral_mul_of_approx (isCompact_closedBall 0 r)
    (integrable_radialU r).integrableOn (fun n => (hψ n).continuous) hφ.continuous hδ hψφ

/-- Translating a Lipschitz test function. -/
theorem lipschitzWith_comp_add_right {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (q : ℂ) :
    LipschitzWith K fun y => φ (y + q) := by
  have h := hφ.comp (isometry_add_right q).lipschitzWith
  rw [mul_one] at h
  exact h

/-- **Lemma 4.5(a)** (`lem:radial`): for every Lipschitz `φ` and centre `q`,
`∫ ⟪W^r(x - q), ∇φ(x)⟫ = 2π (⨍_{∂B(q,r)} φ - ∫ u^r(x - q) φ(x))`. -/
theorem integral_inner_radialW (hr : 0 < r) (q : ℂ) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (radialW r (x - q)) (gradient φ x) =
      2 * π * (Real.circleAverage φ q r - ∫ x, radialU r (x - q) * φ x) := by
  have h := integral_inner_radialW_zero hr (lipschitzWith_comp_add_right hφ q)
  simp only [gradient_comp_add_right, Real.circleAverage_map_add_const] at h
  have e1 : ∫ x, inner ℝ (radialW r (x - q)) (gradient φ x) =
      ∫ y, inner ℝ (radialW r y) (gradient φ (y + q)) := by
    rw [← integral_sub_right_eq_self (fun y => inner ℝ (radialW r y) (gradient φ (y + q))) q]
    simp only [sub_add_cancel]
  have e2 : ∫ x, radialU r (x - q) * φ x = ∫ y, radialU r y * φ (y + q) := by
    rw [← integral_sub_right_eq_self (fun y => radialU r y * φ (y + q)) q]
    simp only [sub_add_cancel]
  rw [e1, e2]
  exact h

/-- **`-Δ f_r(· - q) = 2π (δ_q - σ_{q,r})`** tested against Lipschitz functions (screening note, Lemma 2.1(c)
for a single truncation radius; no support condition). -/
theorem integral_inner_gradient_truncLog_lipschitz (hr : 0 < r) (q : ℂ) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (gradient (truncLog r) (x - q)) (gradient φ x) =
      2 * π * (φ q - Real.circleAverage φ q r) := by
  obtain ⟨ψ, δ, hδ, hψ, hψφ, hψB, hlim⟩ := exists_smooth_approx_lipschitz hφ
  have hL := tendsto_integral_inner_gradient MeasurableSet.univ
    (integrable_gradient_truncLog hr q).integrableOn
    (fun n x hx => absurd (mem_univ x) hx) hψB hlim
  have hEq : ∀ n, ∫ x, inner ℝ (gradient (truncLog r) (x - q)) (gradient (ψ n) x) =
      2 * π * (ψ n q - Real.circleAverage (ψ n) q r) := fun n =>
    integral_inner_gradient_truncLog ((hψ n).of_le (by simp)) hr q
  simp only [hEq] at hL
  refine tendsto_nhds_unique hL (tendsto_const_nhds.mul (Tendsto.sub ?_
    (tendsto_circleAverage_of_approx (fun n => (hψ n).continuous) hφ.continuous hδ hψφ q r)))
  exact tendsto_of_abs_sub_le hδ fun n => hψφ n q

/-- **Lemma 4.5(b)** (`lem:radial`): for every Lipschitz `φ` and centre `q`,
`∫ ⟪K^r(x - q), ∇φ(x)⟫ = 2π (φ(q) - ∫ u^r(x - q) φ(x))`, i.e. `-div K^r = 2π (δ₀ - u^r)`. -/
theorem integral_inner_radialK (hr : 0 < r) (q : ℂ) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (radialK r (x - q)) (gradient φ x) =
      2 * π * (φ q - ∫ x, radialU r (x - q) * φ x) := by
  have hb : ∀ x, ‖gradient φ x‖ ≤ K := fun x => norm_gradient_le_of_lipschitz hφ x
  have hi1 : Integrable fun x => inner ℝ (gradient (truncLog r) (x - q)) (gradient φ x) :=
    integrable_inner_of_integrableOn MeasurableSet.univ
      (integrable_gradient_truncLog hr q).integrableOn (aestronglyMeasurable_gradient _) hb
      (fun x hx => absurd (mem_univ x) hx)
  have hi2 : Integrable fun x => inner ℝ (radialW r (x - q)) (gradient φ x) :=
    integrable_inner_of_integrableOn MeasurableSet.univ
      ((integrable_radialW hr).comp_sub_right q).integrableOn (aestronglyMeasurable_gradient _) hb
      (fun x hx => absurd (mem_univ x) hx)
  simp only [radialK, inner_add_left]
  rw [integral_add hi1 hi2, integral_inner_gradient_truncLog_lipschitz hr q hφ,
    integral_inner_radialW hr q hφ]
  ring

end Weak

end SandierSerfaty.Screening

end
