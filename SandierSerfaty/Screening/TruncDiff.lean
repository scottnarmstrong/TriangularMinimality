/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.TruncLogPairing
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.DiscreteSubset

/-!
# Integrals and gradients of `f_η` and `f_{α,β}`

* `integrable_truncLog`, `integral_truncLog_eq`: `f_η ∈ L¹` and `∫ f_η = π η² / 2` (book (11.2.6),
  the comparison note's Lemma `lem:f`(c)), by polar coordinates;
* for `F = f_{α,β}(· - i)` (`truncDiff`): it is `α⁻¹`-Lipschitz (`lipschitzWith_truncDiff_sub`), its
  a.e. gradient is `∇f_α(· - i) - ∇f_β(· - i)` (`ae_gradient_truncDiff_sub`), and
  `∫ F = π (α² - β²) / 2` (`integral_truncDiff_sub`);
* `circleAverage_truncLog_sub_eq`: on circles of positive radius, the averages of
  `f_α(· - i) - f_β(· - i)` (the integrand of `SandierSerfaty.truncInteraction`) and of `F` agree
  (they differ only at `i`);
* `truncLog_sub_truncLog_nonpos`: `f_α - f_β ≤ 0` everywhere for `0 < α ≤ β`.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

/-! ### `∫ f_η = π η² / 2` -/

theorem truncLog_eq_of_norm (η : ℝ) (y : ℂ) :
    truncLog η y = max (Real.log η - Real.log ‖y‖) 0 := by
  unfold truncLog; congr 1; ring

theorem measurable_truncLog (η : ℝ) : Measurable (truncLog η) := by
  unfold truncLog
  exact ((Real.measurable_log.comp measurable_norm).neg.sub_const _).max measurable_const

theorem truncLog_le_div_norm {η : ℝ} (hη : 0 < η) {y : ℂ} (hy : y ≠ 0) :
    truncLog η y ≤ η / ‖y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [truncLog_eq_of_norm]
  refine max_le ?_ (by positivity)
  rw [← Real.log_div hη.ne' hn.ne']
  linarith [Real.log_le_sub_one_of_pos (div_pos hη hn)]

theorem integrable_truncLog {η : ℝ} (hη : 0 < η) : Integrable (truncLog η) volume := by
  have hball : IntegrableOn (truncLog η) (ball 0 (η + 1)) volume := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := η) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex]) ?_
      (measurable_truncLog η).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae ((Set.countable_singleton (0 : ℂ)).ae_notMem volume)]
      with y hy
    have hy0 : y ≠ 0 := hy
    rw [Real.rpow_neg_one, Real.norm_of_nonneg (truncLog_nonneg η y), ← div_eq_mul_inv]
    exact truncLog_le_div_norm hη hy0
  refine hball.integrable_of_forall_notMem_eq_zero fun y hy => ?_
  rw [mem_ball, dist_zero_right, not_lt] at hy
  exact truncLog_eq_zero hη (by linarith)

/-- The radial antiderivative: `G(r) = r²/2 (log η - log r) + r²/4`, `G' = r (log η - log r)`. -/
theorem integral_radial_truncLog {η : ℝ} (hη : 0 < η) :
    ∫ r in (0 : ℝ)..η, r * (Real.log η - Real.log r) = η ^ 2 / 4 := by
  set G : ℝ → ℝ := fun r => r ^ 2 / 2 * Real.log η - r * (r * Real.log r) / 2 + r ^ 2 / 4
  have hGc : Continuous G := by
    have := Real.continuous_mul_log
    simp only [G]; fun_prop
  have hder : ∀ r ∈ Ioo 0 η, HasDerivAt G (r * (Real.log η - Real.log r)) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.1.ne'
    have h := ((((hasDerivAt_pow 2 r).div_const 2).mul_const (Real.log η)).sub
      (((hasDerivAt_id r).mul ((hasDerivAt_id r).mul (Real.hasDerivAt_log hr0))).div_const 2)).add
      ((hasDerivAt_pow 2 r).div_const 4)
    convert h using 1
    · funext y
      simp only [G, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
    · simp only [Pi.mul_apply, id]
      field_simp
      norm_num
      ring
  have hcont : Continuous fun r : ℝ => r * (Real.log η - Real.log r) := by
    have := Real.continuous_mul_log
    have e : (fun r : ℝ => r * (Real.log η - Real.log r)) =
        fun r => r * Real.log η - r * Real.log r := by ext r; ring
    rw [e]; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hη.le hGc.continuousOn hder
    (hcont.intervalIntegrable 0 η)]
  simp only [G, Real.log_zero]
  ring

/-- **`∫ f_η = π η² / 2`** (comparison note, Lemma `lem:f`(c)). -/
theorem integral_truncLog_eq {η : ℝ} (hη : 0 < η) :
    ∫ x : ℂ, truncLog η x = Real.pi * η ^ 2 / 2 := by
  set k : ℝ → ℝ := fun r => r * max (Real.log η - Real.log r) 0
  have hk : ∀ q : ℝ × ℝ, q ∈ polarCoord.target →
      q.1 • truncLog η (Complex.polarCoord.symm q) = k q.1 * (1 : ℝ) := by
    intro q hq
    have hq0 : 0 < q.1 := hq.1
    rw [polarCoord_symm_eq_circleMap, truncLog_eq_of_norm, norm_circleMap_zero,
      abs_of_pos hq0, smul_eq_mul, mul_one]
  have htm : MeasurableSet (polarCoord.target) := by
    rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  rw [← Complex.integral_comp_polarCoord_symm, setIntegral_congr_fun htm hk, polarCoord_target]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  rw [hvol, setIntegral_prod_mul (fun r => k r) (fun _ => (1 : ℝ)), setIntegral_const,
    Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
    smul_eq_mul, mul_one]
  have hind : (Ioi (0 : ℝ)).indicator k = (Ioc 0 η).indicator
      (fun r => r * (Real.log η - Real.log r)) := by
    ext r
    by_cases hr : 0 < r
    · by_cases hrη : r ≤ η
      · rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
          indicator_of_mem (show r ∈ Ioc 0 η from ⟨hr, hrη⟩)]
        simp only [k]
        rw [max_eq_left (sub_nonneg.2 (Real.log_le_log hr hrη))]
      · rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
          indicator_of_notMem (show r ∉ Ioc 0 η from fun h => hrη h.2)]
        simp only [k]
        rw [max_eq_right (by linarith [Real.log_le_log hη (not_le.1 hrη).le]), mul_zero]
    · rw [indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
        indicator_of_notMem (show r ∉ Ioc 0 η from fun h => hr h.1)]
  rw [← integral_indicator measurableSet_Ioi, hind, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hη.le, integral_radial_truncLog hη]
  ring

theorem integral_truncLog_sub {η : ℝ} (hη : 0 < η) (p : ℂ) :
    ∫ x : ℂ, truncLog η (x - p) = Real.pi * η ^ 2 / 2 := by
  rw [integral_sub_right_eq_self (fun x => truncLog η x) p, integral_truncLog_eq hη]

/-! ### `f_{α,β}(· - i)` -/

theorem truncLog_sub_truncLog_nonpos {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (y : ℂ) :
    truncLog α y - truncLog β y ≤ 0 := by
  rw [truncLog_eq_of_norm, truncLog_eq_of_norm, sub_nonpos]
  exact max_le_max (by linarith [Real.log_le_log hα hαβ]) le_rfl

theorem lipschitzWith_truncDiff_sub {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (i : ℂ) :
    LipschitzWith (Real.toNNReal α⁻¹) (fun x => truncDiff α β (x - i)) := by
  have h := (lipschitzWith_truncDiff hα hαβ).comp (IsometryEquiv.subRight i).isometry.lipschitzWith
  simpa [Function.comp_def] using h

theorem ae_ne_center_ne_norm (i : ℂ) (η : ℝ) : ∀ᵐ x : ℂ, x - i ≠ 0 ∧ ‖x - i‖ ≠ η := by
  have h1 : ∀ᵐ x : ℂ, x ∉ ({i} : Set ℂ) := (Set.countable_singleton i).ae_notMem volume
  have h2 : ∀ᵐ x : ℂ, x ∉ sphere i η :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume i η)
  filter_upwards [h1, h2] with x hx1 hx2
  refine ⟨sub_ne_zero.2 hx1, fun h => hx2 ?_⟩
  rwa [mem_sphere, dist_eq_norm]

theorem gradient_comp_sub_right (φ : ℂ → ℝ) (i x : ℂ) :
    gradient (fun y => φ (y - i)) x = gradient φ (x - i) := by
  simpa [sub_eq_add_neg] using gradient_comp_add_right φ (-i) x

/-- The a.e. gradient of `f_{α,β}(· - i)` is `∇f_α(· - i) - ∇f_β(· - i)`. -/
theorem ae_gradient_truncDiff_sub {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (i : ℂ) :
    ∀ᵐ x : ℂ, gradient (fun y => truncDiff α β (y - i)) x =
      gradient (truncLog α) (x - i) - gradient (truncLog β) (x - i) := by
  filter_upwards [ae_ne_center_ne_norm i α, ae_ne_center_ne_norm i β] with x h1 h2
  rw [gradient_comp_sub_right, gradient_truncDiff hα hαβ h1.1 h1.2 h2.2]

theorem integral_truncDiff_sub {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (i : ℂ) :
    ∫ x : ℂ, truncDiff α β (x - i) = Real.pi * (α ^ 2 - β ^ 2) / 2 := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hae : (fun x : ℂ => truncDiff α β (x - i)) =ᵐ[volume]
      fun x => truncLog α (x - i) - truncLog β (x - i) := by
    filter_upwards [ae_ne_center_ne_norm i α] with x hx
    exact (truncLog_sub_truncLog hα hαβ hx.1).symm
  rw [integral_congr_ae hae, integral_sub ((integrable_truncLog hα).comp_sub_right i)
    ((integrable_truncLog hβ).comp_sub_right i), integral_truncLog_sub hα,
    integral_truncLog_sub hβ]
  ring

/-- On circles of nonzero radius the averages of `f_α(· - i) - f_β(· - i)` and of `f_{α,β}(· - i)`
agree. -/
theorem circleAverage_truncLog_sub_eq {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (i q : ℂ) {r : ℝ}
    (hr : r ≠ 0) :
    Real.circleAverage (fun x => truncLog α (x - i) - truncLog β (x - i)) q r =
      Real.circleAverage (fun x => truncDiff α β (x - i)) q r := by
  refine Real.circleAverage_congr_codiscreteWithin ?_ hr
  filter_upwards [compl_singleton_mem_codiscreteWithin i] with x hx
  exact truncLog_sub_truncLog hα hαβ (sub_ne_zero.2 hx)

end Screening

end SandierSerfaty

end
