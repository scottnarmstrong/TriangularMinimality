/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Defs
public import SandierSerfaty.Screening.TruncDiff
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The density `µ` and its integrals (sphere note, Lemma 3.2, first part)

* `Sphere.integral_radial`, `Sphere.integrable_radial_iff`: integrals of radial functions on `ℂ`;
* `Sphere.integral_potV_dens`: `∫_ℂ V µ = 1`;
* `Sphere.integrable_log_dens`: `y ↦ log |x - y| µ(y)` is integrable, for every `x`;
* `Sphere.integral_log_max`: `∫_0^∞ r µ(r) log max(r, R) dr = log (1 + R²) / (4π)` (`R ≥ 0`).
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty

namespace Sphere


theorem integral_radial (f : ℝ → ℝ) :
    ∫ x : ℂ, f ‖x‖ = 2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * f r := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) f
  simp only [Complex.finrank_real_complex, smul_eq_mul, nsmul_eq_mul] at h
  have hb : volume.real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    rw [Measure.real, Complex.volume_ball]; simp
  rw [h, hb]
  simp
  ring

theorem integrable_radial_iff (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun r : ℝ => r * f r) (Ioi 0) := by
  have h := integrable_fun_norm_addHaar (volume : Measure ℂ) (f := f)
  simpa using h

theorem dens_eq (x : ℂ) : dens x = 1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2) := by
  have h : 0 < 1 + ‖x‖ ^ 2 := by positivity
  unfold dens lam
  have := Real.pi_pos
  field_simp
  ring

/-- The radial profile of `µ`. -/
@[expose] noncomputable def densR (r : ℝ) : ℝ := 1 / (Real.pi * (1 + r ^ 2) ^ 2)

theorem dens_eq_densR (x : ℂ) : dens x = densR ‖x‖ := dens_eq x

theorem tendsto_inv_one_add_sq : Tendsto (fun r : ℝ => (1 + r ^ 2)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num)))

theorem hasDerivAt_inv_one_add_sq (r : ℝ) :
    HasDerivAt (fun r : ℝ => (1 + r ^ 2)⁻¹) (-(2 * r) / (1 + r ^ 2) ^ 2) r := by
  have h : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have := h.inv (by positivity)
  convert this using 1

theorem tendsto_log_one_add_sq_div : Tendsto (fun r : ℝ => Real.log (1 + r ^ 2) / (1 + r ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))
  have h2 : Tendsto (fun s : ℝ => Real.log s / s) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  exact h2.comp h1

theorem integral_potV_densR_aux :
    IntegrableOn (fun r : ℝ => r * (Real.log (1 + r ^ 2) * densR r)) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), r * (Real.log (1 + r ^ 2) * densR r) = 1 / (2 * Real.pi) := by
  have hpi := Real.pi_pos
  set F : ℝ → ℝ := fun r => -(2 * Real.pi)⁻¹ * ((Real.log (1 + r ^ 2) + 1) * (1 + r ^ 2)⁻¹) with hF
  have hd : ∀ r : ℝ, HasDerivAt F (r * (Real.log (1 + r ^ 2) * densR r)) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add 1
    have hp : (1 + r ^ 2) ≠ 0 := by positivity
    have h2 := (h1.log hp).add_const 1
    have h3 := h2.mul (hasDerivAt_inv_one_add_sq r)
    have h4 := h3.const_mul (-(2 * Real.pi)⁻¹)
    convert h4 using 1
    unfold densR
    field_simp
    ring
  have hc : Continuous F := continuous_iff_continuousAt.2 fun r => (hd r).continuousAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h5 : Tendsto (fun r : ℝ => (Real.log (1 + r ^ 2) + 1) * (1 + r ^ 2)⁻¹) atTop (𝓝 0) := by
      have : (fun r : ℝ => (Real.log (1 + r ^ 2) + 1) * (1 + r ^ 2)⁻¹) =
          fun r => Real.log (1 + r ^ 2) / (1 + r ^ 2) + (1 + r ^ 2)⁻¹ := by
        funext r; field_simp
      rw [this]
      simpa using tendsto_log_one_add_sq_div.add tendsto_inv_one_add_sq
    simpa [hF] using h5.const_mul (-(2 * Real.pi)⁻¹)
  have hnn : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * (Real.log (1 + r ^ 2) * densR r) := fun r hr => by
    unfold densR
    have : 0 < r := hr
    have : 0 ≤ Real.log (1 + r ^ 2) := Real.log_nonneg (by nlinarith)
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hc.continuousWithinAt
    (fun r _ => hd r) hnn hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt (fun r _ => hd r) hint hlim]
  simp [hF]

theorem integral_potV_dens : ∫ x : ℂ, potV x * dens x = 1 := by
  have : (fun x : ℂ => potV x * dens x) =
      fun x : ℂ => (fun r : ℝ => Real.log (1 + r ^ 2) * densR r) ‖x‖ := by
    funext x; simp [potV, dens_eq_densR]
  rw [this, integral_radial (fun r : ℝ => Real.log (1 + r ^ 2) * densR r), integral_potV_densR_aux.2]
  have := Real.pi_pos
  field_simp

theorem integrable_potV_dens : Integrable fun x : ℂ => potV x * dens x := by
  have : (fun x : ℂ => potV x * dens x) =
      fun x : ℂ => (fun r : ℝ => Real.log (1 + r ^ 2) * densR r) ‖x‖ := by
    funext x; simp [potV, dens_eq_densR]
  rw [this]
  exact (integrable_radial_iff (fun r : ℝ => Real.log (1 + r ^ 2) * densR r)).2
    integral_potV_densR_aux.1

theorem dens_pos (x : ℂ) : 0 < dens x := by rw [dens_eq]; have := Real.pi_pos; positivity

theorem dens_le (x : ℂ) : dens x ≤ 1 / Real.pi := by
  rw [dens_eq]
  have := Real.pi_pos
  have h : 1 ≤ (1 + ‖x‖ ^ 2) ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  rw [div_le_div_iff₀ (by positivity) this]
  nlinarith

theorem measurable_dens : Measurable dens := by
  unfold dens lam; fun_prop

theorem dens_le_pow (y : ℂ) : dens y ≤ (4 / Real.pi) * (1 + ‖y‖) ^ (-4 : ℝ) := by
  rw [dens_eq]
  have hpi := Real.pi_pos
  have h1 : (1 + ‖y‖) ^ 2 ≤ 2 * (1 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖y‖)]
  have h2 : (1 + ‖y‖) ^ 4 ≤ 4 * (1 + ‖y‖ ^ 2) ^ 2 := by
    calc (1 + ‖y‖) ^ 4 = ((1 + ‖y‖) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + ‖y‖ ^ 2)) ^ 2 := by gcongr
      _ = 4 * (1 + ‖y‖ ^ 2) ^ 2 := by ring
  have hp : 0 < (1 + ‖y‖) := by positivity
  have e : (4 / Real.pi) * (1 + ‖y‖) ^ (-4 : ℝ) = 4 / (Real.pi * (1 + ‖y‖) ^ 4) := by
    rw [Real.rpow_neg hp.le]
    have : (1 + ‖y‖) ^ (4 : ℝ) = (1 + ‖y‖) ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [this]
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hpi.le]

theorem integrable_log_dens (x : ℂ) : Integrable (fun y : ℂ => Real.log ‖x - y‖ * dens y) := by
  have hdec : (fun y : ℂ => Real.log ‖x - y‖ * dens y) =
      fun y => max (Real.log ‖x - y‖) 0 * dens y - truncLog 1 (x - y) * dens y := by
    funext y
    have : Real.log ‖x - y‖ = max (Real.log ‖x - y‖) 0 - truncLog 1 (x - y) := by
      unfold truncLog
      simp only [Real.log_one, neg_zero, sub_zero]
      rcases le_total 0 (Real.log ‖x - y‖) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [← sub_mul, ← this]
  rw [hdec]
  refine Integrable.sub ?_ ?_
  · -- the far field part
    have hg : Integrable (fun y : ℂ => (4 / Real.pi * (1 + ‖x‖)) * (1 + ‖y‖) ^ (-3 : ℝ)) := by
      refine Integrable.const_mul ?_ _
      exact integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    refine hg.mono' ?_ ?_
    · exact (((Real.measurable_log.comp (measurable_const.sub measurable_id).norm).max
        measurable_const).mul measurable_dens).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
      have hm : 0 ≤ max (Real.log ‖x - y‖) 0 := le_max_right _ _
      rw [Real.norm_of_nonneg (mul_nonneg hm (dens_pos y).le)]
      have h1 : max (Real.log ‖x - y‖) 0 ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
        refine max_le ?_ (by positivity)
        rcases eq_or_lt_of_le hn with h0 | h0
        · rw [← h0, Real.log_zero]; positivity
        · have := Real.log_le_sub_one_of_pos h0
          have h3 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
          nlinarith [norm_nonneg x, norm_nonneg y]
      have hp : 0 < 1 + ‖y‖ := by positivity
      have h4 := dens_le_pow y
      calc max (Real.log ‖x - y‖) 0 * dens y
          ≤ ((1 + ‖x‖) * (1 + ‖y‖)) * ((4 / Real.pi) * (1 + ‖y‖) ^ (-4 : ℝ)) :=
            mul_le_mul h1 h4 (dens_pos y).le (by positivity)
        _ = (4 / Real.pi * (1 + ‖x‖)) * (1 + ‖y‖) ^ (-3 : ℝ) := by
            have : (1 + ‖y‖) * (1 + ‖y‖) ^ (-4 : ℝ) = (1 + ‖y‖) ^ (-3 : ℝ) := by
              calc (1 + ‖y‖) * (1 + ‖y‖) ^ (-4 : ℝ)
                  = (1 + ‖y‖) ^ (1 : ℝ) * (1 + ‖y‖) ^ (-4 : ℝ) := by rw [Real.rpow_one]
                _ = (1 + ‖y‖) ^ ((1 : ℝ) + (-4)) := (Real.rpow_add hp _ _).symm
                _ = (1 + ‖y‖) ^ (-3 : ℝ) := by norm_num
            rw [← this]; ring
  · -- the truncated logarithm part
    have h1 : Integrable (fun y : ℂ => truncLog 1 (x - y)) :=
      (Screening.integrable_truncLog one_pos).comp_sub_left x
    refine h1.mul_bdd (c := 1 / Real.pi) measurable_dens.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_of_nonneg (dens_pos y).le]
    exact dens_le y



/-- The antiderivative of `r µ(r) log r`. -/
@[expose] noncomputable def primLog (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ((1 - (1 + r ^ 2)⁻¹) * Real.log r - Real.log (1 + r ^ 2) / 2)

theorem continuous_primLog : Continuous primLog := by
  have h1 : Continuous fun r : ℝ => r / (1 + r ^ 2) :=
    continuous_id.div (by fun_prop) (fun r => by positivity)
  have h2 : Continuous fun r : ℝ => (1 - (1 + r ^ 2)⁻¹) * Real.log r := by
    have e : (fun r : ℝ => (1 - (1 + r ^ 2)⁻¹) * Real.log r) =
        fun r => (r / (1 + r ^ 2)) * (r * Real.log r) := by
      funext r
      have : (1 + r ^ 2) ≠ 0 := by positivity
      field_simp
      ring
    rw [e]
    exact h1.mul Real.continuous_mul_log
  have h3 : Continuous fun r : ℝ => Real.log (1 + r ^ 2) / 2 :=
    (Continuous.log (by fun_prop) (fun r => by positivity)).div_const 2
  unfold primLog
  exact continuous_const.mul (h2.sub h3)

theorem hasDerivAt_primLog {r : ℝ} (hr : 0 < r) :
    HasDerivAt primLog (r * densR r * Real.log r) r := by
  have hp : (1 + r ^ 2) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have h2 : HasDerivAt (fun r : ℝ => 1 - (1 + r ^ 2)⁻¹) (2 * r / (1 + r ^ 2) ^ 2) r := by
    have := (hasDerivAt_inv_one_add_sq r).const_sub 1
    convert this using 1
    ring
  have h3 := (h2.mul (Real.hasDerivAt_log hr.ne')).sub ((h1.log hp).div_const 2)
  have h4 := h3.const_mul (2 * Real.pi)⁻¹
  have e : primLog = fun y => (2 * Real.pi)⁻¹ * ((1 - (1 + y ^ 2)⁻¹) * Real.log y - Real.log (1 + y ^ 2) / 2) := rfl
  rw [e]
  convert h4 using 1
  unfold densR
  have := Real.pi_pos
  field_simp
  ring

theorem tendsto_primLog : Tendsto primLog atTop (𝓝 0) := by
  have hpi := Real.pi_pos
  have h1 : Tendsto (fun r : ℝ => (1 + r ^ 2)⁻¹ * Real.log r) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_log_one_add_sq_div
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      have : 0 ≤ Real.log r := Real.log_nonneg hr
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      have h0 : 0 < r := by linarith
      have : Real.log r ≤ Real.log (1 + r ^ 2) :=
        Real.log_le_log h0 (by nlinarith)
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_right this (by positivity)
  have h2 : Tendsto (fun r : ℝ => Real.log (1 - (1 + r ^ 2)⁻¹) / 2) atTop (𝓝 0) := by
    have : Tendsto (fun r : ℝ => 1 - (1 + r ^ 2)⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_inv_one_add_sq.const_sub 1
    have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp this).div_const 2
    simpa using h
  have h3 := (h2.sub h1).const_mul (2 * Real.pi)⁻¹
  simp only [mul_zero, sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold primLog
  have hq : 0 < 1 + r ^ 2 := by positivity
  have hq1 : (1 + r ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have e : Real.log (1 - (1 + r ^ 2)⁻¹) = 2 * Real.log r - Real.log (1 + r ^ 2) := by
    have : 1 - (1 + r ^ 2)⁻¹ = r ^ 2 / (1 + r ^ 2) := by field_simp; ring
    rw [this, Real.log_div (by positivity) hq.ne', Real.log_pow]
    norm_num
  rw [e]
  have : (1 - (1 + r ^ 2)⁻¹) * Real.log r = Real.log r - (1 + r ^ 2)⁻¹ * Real.log r := by ring
  rw [this]
  ring


theorem continuous_densR : Continuous densR := by
  unfold densR
  have := Real.pi_pos
  exact continuous_const.div (by fun_prop) (fun r => by positivity)

theorem integrableOn_densR_log : IntegrableOn (fun r : ℝ => r * densR r * Real.log r) (Ioi 0) := by
  have hpi := Real.pi_pos
  have hs : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hs]
  refine IntegrableOn.union ?_ ?_
  · have hc : Continuous fun r : ℝ => densR r * (r * Real.log r) :=
      continuous_densR.mul Real.continuous_mul_log
    have := hc.continuousOn.integrableOn_Icc (μ := volume) (a := 0) (b := 1)
    refine (this.mono_set Ioc_subset_Icc_self).congr_fun (fun r _ => by ring) measurableSet_Ioc
  · refine integrableOn_Ioi_deriv_of_nonneg (g := primLog) continuous_primLog.continuousWithinAt
      (fun r hr => hasDerivAt_primLog (lt_trans zero_lt_one hr)) (fun r hr => ?_) tendsto_primLog
    have : 0 < r := lt_trans zero_lt_one hr
    have : 0 ≤ Real.log r := Real.log_nonneg hr.le
    unfold densR
    positivity

theorem integral_Ioi_densR_log {R : ℝ} (hR : 0 ≤ R) :
    ∫ r in Ioi R, r * densR r * Real.log r = - primLog R := by
  have hint : IntegrableOn (fun r : ℝ => r * densR r * Real.log r) (Ioi R) :=
    integrableOn_densR_log.mono_set (Ioi_subset_Ioi hR)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto continuous_primLog.continuousWithinAt
    (fun r hr => hasDerivAt_primLog (lt_of_le_of_lt hR hr)) hint tendsto_primLog]
  ring

theorem integral_Ioc_densR {R : ℝ} (hR : 0 ≤ R) :
    ∫ r in Ioc 0 R, r * densR r = (2 * Real.pi)⁻¹ * (1 - (1 + R ^ 2)⁻¹) := by
  have hpi := Real.pi_pos
  rw [← intervalIntegral.integral_of_le hR]
  have hd : ∀ r ∈ uIcc (0 : ℝ) R, HasDerivAt (fun r : ℝ => -(2 * Real.pi)⁻¹ * (1 + r ^ 2)⁻¹)
      (r * densR r) r := by
    intro r _
    have := (hasDerivAt_inv_one_add_sq r).const_mul (-(2 * Real.pi)⁻¹)
    convert this using 1
    unfold densR
    field_simp
  have hi : IntervalIntegrable (fun r : ℝ => r * densR r) volume 0 R :=
    (continuous_id.mul continuous_densR).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp
  ring

theorem integral_log_max {R : ℝ} (hR : 0 ≤ R) :
    ∫ r in Ioi (0 : ℝ), r * (densR r * Real.log (max r R)) = Real.log (1 + R ^ 2) / (4 * Real.pi) := by
  have hpi := Real.pi_pos
  have hs : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := (Ioc_union_Ioi_eq_Ioi hR).symm
  have hf1 : IntegrableOn (fun r : ℝ => r * (densR r * Real.log (max r R))) (Ioc 0 R) := by
    have hc : Continuous fun r : ℝ => r * densR r * Real.log R :=
      (continuous_id.mul continuous_densR).mul continuous_const
    have := hc.continuousOn.integrableOn_Icc (μ := volume) (a := 0) (b := R)
    refine (this.mono_set Ioc_subset_Icc_self).congr_fun (fun r hr => ?_) measurableSet_Ioc
    rw [max_eq_right hr.2]; ring
  have hf2 : IntegrableOn (fun r : ℝ => r * (densR r * Real.log (max r R))) (Ioi R) := by
    refine (integrableOn_densR_log.mono_set (Ioi_subset_Ioi hR)).congr_fun (fun r hr => ?_)
      measurableSet_Ioi
    rw [max_eq_left (le_of_lt hr)]; ring
  rw [hs, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hf1 hf2]
  have e1 : ∫ r in Ioc 0 R, r * (densR r * Real.log (max r R)) =
      Real.log R * ((2 * Real.pi)⁻¹ * (1 - (1 + R ^ 2) ⁻¹)) := by
    rw [← integral_Ioc_densR hR, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
    rw [max_eq_right hr.2]; ring
  have e2 : ∫ r in Ioi R, r * (densR r * Real.log (max r R)) = - primLog R := by
    rw [← integral_Ioi_densR_log hR]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [max_eq_left (le_of_lt hr)]; ring
  rw [e1, e2]
  unfold primLog
  have hq : (1 + R ^ 2) ≠ 0 := by positivity
  field_simp
  ring


end Sphere

end SandierSerfaty

end
