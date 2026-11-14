/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Calculus of the truncated logarithm

For `η > 0`, `f_η = truncLog η = (log η - log ‖·‖)₊` (book (4.1.18)):

* `gradient_truncLog_of_gt`, `gradient_truncLog_of_lt`: `∇f_η(y) = 0` for `‖y‖ > η` and
  `∇f_η(y) = -y/‖y‖²` for `0 < ‖y‖ < η`; `ae_ne_zero_ne_norm`: these cover almost every `y`;
* `integrable_gradient_truncLog`: `∇f_η(· - p)` is integrable on `ℂ`;
* `truncDiff α β y = log (min (max ‖y‖ α) β) - log β`, the continuous representative of
  `f_{α,β} = f_α - f_β` (`truncLog_sub_truncLog`: equal off the centre; `truncLog` takes
  the value `max (log η) 0` at the centre, so `f_α - f_β` itself is discontinuous there);
  `lipschitzWith_truncDiff`: it is `α⁻¹`-Lipschitz; it vanishes for `‖y‖ ≥ β`, is `≤ 0`, and
  `gradient_truncDiff` identifies its gradient off the centre and the two circles.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal

public section

namespace SandierSerfaty

namespace Screening

/-! ### Values of `truncLog` -/

theorem truncLog_nonneg (η : ℝ) (y : ℂ) : 0 ≤ truncLog η y := le_max_right _ _

theorem truncLog_eq_zero {η : ℝ} (hη : 0 < η) {y : ℂ} (hy : η ≤ ‖y‖) : truncLog η y = 0 := by
  unfold truncLog
  have : Real.log η ≤ Real.log ‖y‖ := Real.log_le_log hη hy
  exact max_eq_right (by linarith)

theorem truncLog_eq_log_sub {η : ℝ} {y : ℂ} (hy0 : 0 < ‖y‖) (hy : ‖y‖ ≤ η) :
    truncLog η y = Real.log η - Real.log ‖y‖ := by
  unfold truncLog
  have : Real.log ‖y‖ ≤ Real.log η := Real.log_le_log hy0 hy
  rw [max_eq_left (by linarith)]
  ring

/-! ### Gradients -/

theorem gradient_congr_nhds {f g : ℂ → ℝ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) :
    gradient f x = gradient g x := by
  simp only [gradient, h.fderiv_eq]

/-- `∂φ(x)[v] = ⟪∇φ(x), v⟫`. -/
theorem inner_gradient_left (φ : ℂ → ℝ) (x v : ℂ) :
    inner ℝ (gradient φ x) v = fderiv ℝ φ x v := by
  simp only [gradient, toDual_symm_apply]

theorem toDual_symm_smul_innerSL (c : ℝ) (y : ℂ) :
    (toDual ℝ ℂ).symm (c • innerSL ℝ y) = c • y := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext w
  simp [toDual_apply_apply]
  ring

theorem hasFDerivAt_log_norm {y : ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z : ℂ => Real.log ‖z‖) ((‖y‖ ^ 2)⁻¹ • innerSL ℝ y) y := by
  have hn : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.log hn
  have h2 := h1.const_mul (1 / 2 : ℝ)
  have e : (fun z : ℂ => Real.log ‖z‖) = fun z => (1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) := by
    funext z; rw [Real.log_pow]; push_cast; ring
  rw [e]
  convert h2 using 1
  ext w
  simp [two_smul]
  ring

theorem gradient_truncLog_of_gt {η : ℝ} (hη : 0 < η) {y : ℂ} (hy : η < ‖y‖) :
    gradient (truncLog η) y = 0 := by
  have hev : truncLog η =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact truncLog_eq_zero hη (le_of_lt hz)
  rw [gradient_congr_nhds hev]
  simp [gradient]

theorem truncLog_eventuallyEq_of_lt {η : ℝ} {y : ℂ} (hy0 : 0 < ‖y‖) (hy : ‖y‖ < η) :
    truncLog η =ᶠ[𝓝 y] fun z => Real.log η - Real.log ‖z‖ := by
  filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hy0, hy⟩] with z hz
  exact truncLog_eq_log_sub hz.1 (le_of_lt hz.2)

theorem hasFDerivAt_truncLog_of_lt {η : ℝ} {y : ℂ} (hy0 : 0 < ‖y‖) (hy : ‖y‖ < η) :
    HasFDerivAt (truncLog η) (-((‖y‖ ^ 2)⁻¹ • innerSL ℝ y)) y := by
  have hh : HasFDerivAt (fun z : ℂ => Real.log η - Real.log ‖z‖)
      (0 - (‖y‖ ^ 2)⁻¹ • innerSL ℝ y) y :=
    (hasFDerivAt_const (Real.log η) y).sub (hasFDerivAt_log_norm (norm_pos_iff.1 hy0))
  rw [zero_sub] at hh
  exact hh.congr_of_eventuallyEq (truncLog_eventuallyEq_of_lt hy0 hy)

theorem gradient_truncLog_of_lt {η : ℝ} {y : ℂ} (hy0 : 0 < ‖y‖) (hy : ‖y‖ < η) :
    gradient (truncLog η) y = -((‖y‖ ^ 2)⁻¹ : ℝ) • y := by
  simp only [gradient]
  rw [(hasFDerivAt_truncLog_of_lt hy0 hy).fderiv, map_neg, toDual_symm_smul_innerSL, neg_smul]

theorem differentiableAt_truncLog {η : ℝ} (hη : 0 < η) {y : ℂ} (hy0 : y ≠ 0) (hyη : ‖y‖ ≠ η) :
    DifferentiableAt ℝ (truncLog η) y := by
  rcases hyη.lt_or_gt with h | h
  · exact (hasFDerivAt_truncLog_of_lt (norm_pos_iff.2 hy0) h).differentiableAt
  · have hev : truncLog η =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with z hz
      exact truncLog_eq_zero hη (le_of_lt hz)
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hev

theorem norm_gradient_truncLog_le {η : ℝ} (hη : 0 < η) {y : ℂ} (hy0 : y ≠ 0) (hyη : ‖y‖ ≠ η) :
    ‖gradient (truncLog η) y‖ ≤ ‖y‖⁻¹ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rcases hyη.lt_or_gt with h | h
  · rw [gradient_truncLog_of_lt hn h, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
    field_simp
    exact le_rfl
  · rw [gradient_truncLog_of_gt hη h, norm_zero]; positivity

/-- Almost every point is neither the centre nor on the circle of radius `η`. -/
theorem ae_ne_zero_ne_norm (η : ℝ) : ∀ᵐ y : ℂ, y ≠ 0 ∧ ‖y‖ ≠ η := by
  have h1 : ∀ᵐ y : ℂ, y ∉ ({0} : Set ℂ) := (Set.countable_singleton (0 : ℂ)).ae_notMem volume
  have h2 : ∀ᵐ y : ℂ, y ∉ sphere (0 : ℂ) η :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume 0 η)
  filter_upwards [h1, h2] with y hy1 hy2
  refine ⟨hy1, fun h => hy2 ?_⟩
  simpa [mem_sphere, dist_zero_right] using h

theorem measurable_gradient (h : ℂ → ℝ) : Measurable (gradient h) := by
  borelize (StrongDual ℝ ℂ)
  exact (toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ h)

theorem aestronglyMeasurable_gradient (h : ℂ → ℝ) {μ : Measure ℂ} :
    AEStronglyMeasurable (gradient h) μ :=
  (measurable_gradient h).aestronglyMeasurable

/-- `∇f_η` is integrable on `ℂ`: it is bounded by `‖y‖⁻¹` and vanishes outside `B(0, η)`. -/
theorem integrable_gradient_truncLog_zero {η : ℝ} (hη : 0 < η) :
    Integrable (gradient (truncLog η)) volume := by
  have hball : IntegrableOn (gradient (truncLog η)) (ball 0 (η + 1)) volume := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex]) ?_
      (aestronglyMeasurable_gradient _)
    filter_upwards [ae_restrict_of_ae (ae_ne_zero_ne_norm η)] with y hy
    rw [Real.rpow_neg_one, one_mul]
    exact norm_gradient_truncLog_le hη hy.1 hy.2
  refine hball.integrable_of_forall_notMem_eq_zero fun y hy => ?_
  rw [mem_ball, dist_zero_right, not_lt] at hy
  exact gradient_truncLog_of_gt hη (by linarith)

theorem integrable_gradient_truncLog {η : ℝ} (hη : 0 < η) (p : ℂ) :
    Integrable (fun x => gradient (truncLog η) (x - p)) volume :=
  Integrable.comp_sub_right (integrable_gradient_truncLog_zero hη) p

/-! ### The continuous representative of `f_{α,β}` -/

/-- `f_{α,β}(y) = log (min (max ‖y‖ α) β) - log β`: the continuous representative of
`f_α - f_β` (`truncLog_sub_truncLog`). -/
@[expose] noncomputable def truncDiff (α β : ℝ) (y : ℂ) : ℝ :=
  Real.log (min (max ‖y‖ α) β) - Real.log β

theorem truncLog_sub_truncLog {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {y : ℂ} (hy : y ≠ 0) :
    truncLog α y - truncLog β y = truncDiff α β y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hβ : 0 < β := hα.trans_le hαβ
  unfold truncDiff
  rcases le_total ‖y‖ α with h1 | h1
  · rw [truncLog_eq_log_sub hn h1, truncLog_eq_log_sub hn (h1.trans hαβ), max_eq_right h1,
      min_eq_left hαβ]
    ring
  · rcases le_total ‖y‖ β with h2 | h2
    · rw [truncLog_eq_zero hα h1, truncLog_eq_log_sub hn h2, max_eq_left h1, min_eq_left h2]
      ring
    · rw [truncLog_eq_zero hα h1, truncLog_eq_zero hβ h2, max_eq_left h1,
        min_eq_right h2]
      ring

theorem truncDiff_eq_zero {α β : ℝ} {y : ℂ} (hy : β ≤ ‖y‖) : truncDiff α β y = 0 := by
  unfold truncDiff
  rw [min_eq_right (hy.trans (le_max_left _ _))]
  ring

theorem truncDiff_of_norm_le {α β : ℝ} {y : ℂ} (hy : ‖y‖ ≤ α) (hαβ : α ≤ β) :
    truncDiff α β y = Real.log α - Real.log β := by
  unfold truncDiff
  rw [max_eq_right hy, min_eq_left hαβ]

theorem truncDiff_nonpos {α β : ℝ} (hα : 0 < α) (y : ℂ) : truncDiff α β y ≤ 0 := by
  unfold truncDiff
  have h0 : 0 < min (max ‖y‖ α) β ∨ min (max ‖y‖ α) β = β := by
    rcases min_choice (max ‖y‖ α) β with h | h
    · left; rw [h]; exact hα.trans_le (le_max_right _ _)
    · right; exact h
  rcases h0 with h | h
  · rcases le_or_gt β 0 with hb | hb
    · exact absurd (h.trans_le (min_le_right _ _)) (not_lt.2 hb)
    · have := Real.log_le_log h (min_le_right (max ‖y‖ α) β)
      linarith
  · rw [h]; simp

theorem tsupport_truncDiff_subset (α β : ℝ) (p : ℂ) :
    tsupport (fun x => truncDiff α β (x - p)) ⊆ closedBall p β := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra h
  rw [mem_closedBall, dist_eq_norm, not_le] at h
  exact hx (truncDiff_eq_zero h.le)

theorem hasCompactSupport_truncDiff (α β : ℝ) (p : ℂ) :
    HasCompactSupport (fun x => truncDiff α β (x - p)) :=
  (isCompact_closedBall p β).of_isClosed_subset isClosed_closure (tsupport_truncDiff_subset α β p)

/-- `log` is `α⁻¹`-Lipschitz on `[α, ∞)`. -/
theorem abs_log_sub_log_le {α a b : ℝ} (hα : 0 < α) (ha : α ≤ a) (hb : α ≤ b) :
    |Real.log a - Real.log b| ≤ α⁻¹ * |a - b| := by
  have key : ∀ a b : ℝ, α ≤ a → α ≤ b → b ≤ a → Real.log a - Real.log b ≤ α⁻¹ * (a - b) := by
    intro a b ha hb hba
    have hb0 : 0 < b := hα.trans_le hb
    have h1 : Real.log a - Real.log b = Real.log (a / b) := by
      rw [Real.log_div (hα.trans_le ha).ne' hb0.ne']
    have h2 : Real.log (a / b) ≤ a / b - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hα.trans_le ha) hb0)
    have h3 : a / b - 1 = (a - b) / b := by field_simp
    have h4 : (a - b) / b ≤ α⁻¹ * (a - b) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hα hb) (by linarith)
    linarith
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith [Real.log_le_log (hα.trans_le hb) h]),
      abs_of_nonneg (by linarith)]
    exact key a b ha hb h
  · rw [abs_of_nonpos (by linarith [Real.log_le_log (hα.trans_le ha) h]),
      abs_of_nonpos (by linarith)]
    have := key b a hb ha h
    linarith

theorem lipschitzWith_truncDiff {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    LipschitzWith (Real.toNNReal α⁻¹) (truncDiff α β) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hα.le)]
  unfold truncDiff
  have hcl : ∀ z : ℂ, α ≤ min (max ‖z‖ α) β := fun z => le_min (le_max_right _ _) hαβ
  have h1 := abs_log_sub_log_le hα (hcl x) (hcl y)
  have h2 : |min (max ‖x‖ α) β - min (max ‖y‖ α) β| ≤ |‖x‖ - ‖y‖| :=
    (abs_min_sub_min_le_max _ _ _ _).trans (by
      rw [sub_self, abs_zero]
      exact max_le (abs_max_sub_max_le_abs _ _ _) (abs_nonneg _))
  have h3 : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y
  calc |Real.log (min (max ‖x‖ α) β) - Real.log β - (Real.log (min (max ‖y‖ α) β) - Real.log β)|
      = |Real.log (min (max ‖x‖ α) β) - Real.log (min (max ‖y‖ α) β)| := by ring_nf
    _ ≤ α⁻¹ * |min (max ‖x‖ α) β - min (max ‖y‖ α) β| := h1
    _ ≤ α⁻¹ * dist x y := mul_le_mul_of_nonneg_left (h2.trans h3) (inv_nonneg.2 hα.le)

/-- Off the centre and the two circles, `∇f_{α,β} = ∇f_α - ∇f_β`. -/
theorem gradient_truncDiff {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {y : ℂ} (hy0 : y ≠ 0)
    (hyα : ‖y‖ ≠ α) (hyβ : ‖y‖ ≠ β) :
    gradient (truncDiff α β) y = gradient (truncLog α) y - gradient (truncLog β) y := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hev : truncDiff α β =ᶠ[𝓝 y] fun z => truncLog α z - truncLog β z := by
    filter_upwards [isOpen_ne.mem_nhds hy0] with z hz
    exact (truncLog_sub_truncLog hα hαβ hz).symm
  rw [gradient_congr_nhds hev]
  simp only [gradient]
  rw [fderiv_fun_sub (differentiableAt_truncLog hα hy0 hyα) (differentiableAt_truncLog hβ hy0 hyβ),
    map_sub]

end Screening

end SandierSerfaty

end
