/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.TruncLogCalculus
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The distributional Laplacian of the truncated logarithm

For `η > 0`, a point `p` and a `C¹` function `φ` (book (4.1.21), the comparison note's Lemma `lem:f`(d)):
`∫ ⟪∇f_η(x - p), ∇φ(x)⟫ dx = 2π (φ(p) - ⨍_{∂B(p, η)} φ)`, i.e.
`-Δ f_η(· - p) = 2π (δ_p - δ_p^{(η)})` (`integral_inner_gradient_truncLog`).

The proof is a direct computation in polar coordinates: on `B(0, η)`,
`⟪∇f_η(x), ∇φ(x)⟫ = -‖x‖⁻² ∂φ(x)[x]`, which is `-r⁻¹ ∂_r φ(r e^{iθ})`; the Jacobian `r` cancels the
singularity and the fundamental theorem of calculus in `r ∈ [0, η]` gives `φ(η e^{iθ}) - φ(0)`.

`truncDiff_circleAverage_self_α`, `…_β`: the averages of `f_{α,β}` on its own circles.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

/-- A.e. form of the integrand: `⟪∇f_η(x), ∇φ(x)⟫ = -1_{B(0,η)}(x) ‖x‖⁻² ∂φ(x)[x]`. -/
theorem inner_gradient_truncLog_ae (φ : ℂ → ℝ) {η : ℝ} (hη : 0 < η) :
    (fun x => inner ℝ (gradient (truncLog η) x) (gradient φ x)) =ᵐ[volume]
      fun x => -(ball (0 : ℂ) η).indicator (fun x => (‖x‖ ^ 2)⁻¹ * fderiv ℝ φ x x) x := by
  filter_upwards [ae_ne_zero_ne_norm η] with x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx.1
  rcases hx.2.lt_or_gt with h | h
  · have hxb : x ∈ ball (0 : ℂ) η := by rwa [mem_ball_zero_iff]
    rw [indicator_of_mem hxb, gradient_truncLog_of_lt hn h, real_inner_smul_left,
      real_inner_comm, inner_gradient_left]
    ring
  · have hxb : x ∉ ball (0 : ℂ) η := by rw [mem_ball_zero_iff]; exact not_lt.2 h.le
    rw [indicator_of_notMem hxb, gradient_truncLog_of_gt hη h]
    simp

/-- The ray map `r ↦ r e^{iθ}` has derivative `e^{iθ}`. -/
theorem hasDerivAt_circleMap_radius (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => circleMap 0 s θ) (Complex.exp (θ * Complex.I)) r := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (Complex.exp (θ * Complex.I))
  simpa [circleMap] using h

theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I]
  push_cast
  ring

/-- The integrand in polar coordinates. -/
theorem polar_integrand_eq (φ : ℂ → ℝ) {η : ℝ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    p.1 • (ball (0 : ℂ) η).indicator (fun x => (‖x‖ ^ 2)⁻¹ * fderiv ℝ φ x x)
        (Complex.polarCoord.symm p) =
      (Ioo 0 η ×ˢ univ).indicator
        (fun q : ℝ × ℝ => fderiv ℝ φ (circleMap 0 q.1 q.2) (Complex.exp (q.2 * Complex.I))) p := by
  rw [polarCoord_symm_eq_circleMap]
  have hnorm : ‖circleMap 0 p.1 p.2‖ = p.1 := by
    rw [norm_circleMap_zero, abs_of_pos hp]
  by_cases hb : p.1 < η
  · have h1 : circleMap 0 p.1 p.2 ∈ ball (0 : ℂ) η := by rwa [mem_ball_zero_iff, hnorm]
    have h2 : p ∈ Ioo 0 η ×ˢ (univ : Set ℝ) := ⟨⟨hp, hb⟩, trivial⟩
    rw [indicator_of_mem h1, indicator_of_mem h2, hnorm]
    have hlin : fderiv ℝ φ (circleMap 0 p.1 p.2) (circleMap 0 p.1 p.2) =
        p.1 * fderiv ℝ φ (circleMap 0 p.1 p.2) (Complex.exp (p.2 * Complex.I)) := by
      conv_lhs => rw [show circleMap 0 p.1 p.2 = p.1 • Complex.exp (p.2 * Complex.I) by
        simp [circleMap, Complex.real_smul]]
      rw [map_smul, smul_eq_mul]
      simp [circleMap, Complex.real_smul]
    rw [hlin, smul_eq_mul]
    field_simp
  · have h1 : circleMap 0 p.1 p.2 ∉ ball (0 : ℂ) η := by
      rw [mem_ball_zero_iff, hnorm]; exact hb
    have h2 : p ∉ Ioo 0 η ×ˢ (univ : Set ℝ) := fun h => hb h.1.2
    rw [indicator_of_notMem h1, indicator_of_notMem h2, smul_zero]

/-- The integral of `φ` over a period equals that over `(-π, π)`. -/
theorem integral_Ioo_circleMap_eq (φ : ℂ → ℝ) (η : ℝ) :
    ∫ θ in Ioo (-π) π, φ (circleMap 0 η θ) = ∫ θ in (0 : ℝ)..2 * π, φ (circleMap 0 η θ) := by
  have hper : Function.Periodic (fun θ => φ (circleMap 0 η θ)) (2 * π) :=
    fun θ => by simp [periodic_circleMap 0 η θ]
  have h := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), h]

/-- **The distributional Laplacian of `f_η`**, centre `0`:
`∫ ⟪∇f_η, ∇φ⟫ = 2π (φ(0) - ⨍_{∂B(0,η)} φ)` for `C¹` functions `φ`. -/
theorem integral_inner_gradient_truncLog_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) {η : ℝ}
    (hη : 0 < η) :
    ∫ x, inner ℝ (gradient (truncLog η) x) (gradient φ x) =
      2 * π * (φ 0 - Real.circleAverage φ 0 η) := by
  set D : ℝ × ℝ → ℝ :=
    fun q => fderiv ℝ φ (circleMap 0 q.1 q.2) (Complex.exp (q.2 * Complex.I)) with hD
  have hDc : Continuous D := by
    have h1 : Continuous fun q : ℝ × ℝ => circleMap 0 q.1 q.2 := by
      simp only [circleMap]; fun_prop
    exact ((hφ.continuous_fderiv (by norm_num)).comp h1).clm_apply (by fun_prop)
  rw [integral_congr_ae (inner_gradient_truncLog_ae φ hη), integral_neg,
    ← Complex.integral_comp_polarCoord_symm]
  have htm : MeasurableSet (polarCoord.target) := by
    rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_congr_fun htm (fun p hp => polar_integrand_eq φ (η := η) hp.1),
    polarCoord_target, setIntegral_indicator ((measurableSet_Ioo).prod MeasurableSet.univ)]
  have hset : Ioi (0 : ℝ) ×ˢ Ioo (-π) π ∩ Ioo 0 η ×ˢ univ = Ioo 0 η ×ˢ Ioo (-π) π := by
    ext q; simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_univ, and_true]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.1, h2⟩, h1⟩
  rw [hset]
  have hint : IntegrableOn D (Ioo 0 η ×ˢ Ioo (-π) π)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hDc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  have hsw : ∫ q in Ioo 0 η ×ˢ Ioo (-π) π, D q = ∫ q in Ioo (-π) π ×ˢ Ioo 0 η, D q.swap := by
    rw [hvol]
    exact (setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ioo 0 η) (Ioo (-π) π) D).symm
  rw [hsw, hvol, setIntegral_prod (fun q : ℝ × ℝ => D q.swap) (by exact hint.swap)]
  have hinner : ∀ θ : ℝ, ∫ r in Ioo 0 η, D (r, θ) = φ (circleMap 0 η θ) - φ 0 := by
    intro θ
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hη.le]
    have hder : ∀ r ∈ uIcc 0 η, HasDerivAt (fun s : ℝ => φ (circleMap 0 s θ)) (D (r, θ)) r :=
      fun r _ => ((hφ.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt r
        (hasDerivAt_circleMap_radius θ r)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      ((hDc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 η)]
    simp
  simp only [Prod.swap]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hinner θ)]
  have hcont : Continuous fun θ : ℝ => φ (circleMap 0 η θ) :=
    hφ.continuous.comp (continuous_circleMap 0 η)
  rw [integral_sub (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self) (integrableOn_const
      (by simp)), integral_Ioo_circleMap_eq, setIntegral_const, Measure.real, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), Real.circleAverage_def, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

theorem gradient_comp_add_right (φ : ℂ → ℝ) (p x : ℂ) :
    gradient (fun y => φ (y + p)) x = gradient φ (x + p) := by
  simp only [gradient, fderiv_comp_add_right]

/-- **The distributional Laplacian of `f_η(· - p)`** (comparison note, Lemma `lem:f`(d)):
`∫ ⟪∇f_η(x - p), ∇φ(x)⟫ dx = 2π (φ(p) - ⨍_{∂B(p,η)} φ)` for `C¹` functions `φ`. -/
theorem integral_inner_gradient_truncLog {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) {η : ℝ}
    (hη : 0 < η) (p : ℂ) :
    ∫ x, inner ℝ (gradient (truncLog η) (x - p)) (gradient φ x) =
      2 * π * (φ p - Real.circleAverage φ p η) := by
  have hφp : ContDiff ℝ 1 fun y => φ (y + p) := hφ.comp (contDiff_id.add contDiff_const)
  have h := integral_inner_gradient_truncLog_zero hφp hη
  simp only [gradient_comp_add_right, zero_add, Real.circleAverage_map_add_const] at h
  rw [← h, ← integral_sub_right_eq_self
    (fun y => inner ℝ (gradient (truncLog η) y) (gradient φ (y + p))) p]
  simp only [sub_add_cancel]

/-! ### Circle averages of `f_{α,β}` on its own circles -/

theorem circleAverage_truncDiff_self_α {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (i : ℂ) :
    Real.circleAverage (fun x => truncDiff α β (x - i)) i α = Real.log α - Real.log β := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  rw [mem_sphere, dist_eq_norm, abs_of_pos hα] at hx
  exact truncDiff_of_norm_le hx.le hαβ

theorem circleAverage_truncDiff_self_β {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (i : ℂ) :
    Real.circleAverage (fun x => truncDiff α β (x - i)) i β = 0 := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  rw [mem_sphere, dist_eq_norm, abs_of_pos (hα.trans_le hαβ)] at hx
  exact truncDiff_eq_zero hx.ge

end Screening

end SandierSerfaty

end
