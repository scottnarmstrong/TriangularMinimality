/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.TruncLogGreen
public import SandierSerfaty.Sphere.Bridge.Quadrants
public import SandierSerfaty.Screening.Mollify

/-!
# The data of Input 6.3 as a charge field (screening note, §7)

For the data of the sphere note's Input 6.3 (`w` with `w^♮ = w - ∑_{p ∈ X} f_{1/4}(· - p) ∈ H¹(Q)`, weak gradient `g`,
and `-Δw = 2π(∑_{X ∩ Q^{1/2}} δ_p - m)` in `𝒟'((Q^{1/2})°)`), the field
`E = g + ∑_{p ∈ X} ∇f_{1/4}(· - p)` (`Bridge.input63Field`, "`E = ∇w`") satisfies:

* `Bridge.truncField_input63Field`: `E_{1/4} = g` everywhere;
* `Bridge.isChargeField_input63Field`: `E` is a charge field on `(Q^{1/2})°` with density `m` and charges `X`
  (hypothesis (H2) of the screening theorem I4).

The proof uses the weak gradient against the first derivatives of the test function and Green's identity for
the truncated logarithm (`Bridge.integral_truncLog_mul_laplacian`).
-/

open MeasureTheory Set Filter Topology Metric InnerProductSpace
open scoped ENNReal NNReal Real ContDiff Laplacian

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open Lower Screening

/-- The field `E = g + ∑_{p ∈ X} ∇f_{1/4}(· - p)` of Input 6.3. -/
@[expose] noncomputable def input63Field (X : Finset ℂ) (g : ℂ → ℂ) (x : ℂ) : ℂ :=
  g x + ∑ p ∈ X, gradient (truncLog (1 / 4)) (x - p)

theorem truncField_input63Field (X : Finset ℂ) (g : ℂ → ℂ) (x : ℂ) :
    truncField (↑X) (fun _ => 1 / 4) (input63Field X g) x = g x := by
  rw [truncField, finsum_mem_coe_finset, input63Field, add_sub_cancel_right]

theorem sqShrink_eq_sq (a₀ : ℂ) (t s : ℝ) :
    sqShrink a₀ t s = sq (a₀ + ⟨t / 2, t / 2⟩) (t - 2 * s) := by
  rw [sqShrink, sqAt_eq_sq]
  congr 1
  apply Complex.ext <;> simp <;> ring

theorem sqShrink_subset_sqAt (a₀ : ℂ) {t s : ℝ} (hs : 0 ≤ s) : sqShrink a₀ t s ⊆ sqAt a₀ t := by
  rintro x ⟨h1, h2, h3, h4⟩
  simp only [Complex.add_re, Complex.add_im] at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : ℂ}
    (hx : x ∉ tsupport φ) : Δ φ x = 0 := by
  rw [laplacian_eq_pd_fun hφ]
  simp only
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (tsupport_fderiv_apply_subset ℝ 1 h)),
    fderiv_of_notMem_tsupport ℝ (fun h => hx (tsupport_fderiv_apply_subset ℝ Complex.I h))]
  simp

theorem gradient_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport φ) :
    gradient φ x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

theorem inner_eq_re_mul_add (z : ℂ) (φ : ℂ → ℝ) (x : ℂ) :
    inner ℝ z (gradient φ x) = z.re * fderiv ℝ φ x 1 + z.im * fderiv ℝ φ x Complex.I := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Analysis.gradient_re,
    Analysis.gradient_im, Analysis.pd₁, Analysis.pd₂]
  ring

variable {a₀ : ℂ} {t m : ℝ} {X : Finset ℂ} {w : ℂ → ℝ} {g : ℂ → ℂ}

theorem bounded_of_contDiff {ψ : ℂ → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ∃ B, ∀ x, ‖ψ x‖ ≤ B := hψ.bounded_above_of_compact_support hc

open scoped Classical in
/-- **(H2) for Input 6.3**: `E = g + ∑ ∇f_{1/4}(· - p)` is a charge field on `(Q^{1/2})°`. -/
theorem isChargeField_input63Field
    (hw : HasWeakGradientOn (sqAt a₀ t) (fun x => w x - ∑ p ∈ X, truncLog (1 / 4) (x - p)) g)
    (hΔ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ interior (sqShrink a₀ t (1 / 2)) →
      -(∫ x, w x * Δ φ x) =
        2 * Real.pi * ((∑ p ∈ X.filter (· ∈ sqShrink a₀ t (1 / 2)), φ p) - m * ∫ x, φ x)) :
    IsChargeField (interior (sqShrink a₀ t (1 / 2))) m (↑X) (input63Field X g) := by
  set Ω := sqAt a₀ t with hΩ
  set u : ℂ → ℝ := fun x => w x - ∑ p ∈ X, truncLog (1 / 4) (x - p) with hu
  have hΩm : MeasurableSet Ω := by rw [hΩ, sqAt_eq_sq]; exact measurableSet_sq _ _
  have hΩf : volume Ω < ⊤ := by rw [hΩ, sqAt_eq_sq]; exact (isCompact_sq _ _).measure_lt_top
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by rw [Measure.restrict_apply_univ]; exact hΩf⟩
  have hUΩ : interior (sqShrink a₀ t (1 / 2)) ⊆ interior Ω :=
    interior_mono (sqShrink_subset_sqAt a₀ (by norm_num))
  have hgi : IntegrableOn g Ω := hw.2.1.integrable (by norm_num)
  have hui : IntegrableOn u Ω := hw.1.integrable (by norm_num)
  have hfi : ∀ p, Integrable (fun x => truncLog (1 / 4 : ℝ) (x - p)) := fun p =>
    (integrable_truncLog (by norm_num)).comp_sub_right p
  have hgradi : ∀ p, Integrable (fun x => gradient (truncLog (1 / 4 : ℝ)) (x - p)) := fun p =>
    integrable_gradient_truncLog (by norm_num) p
  refine ⟨?_, fun φ hφ hc hφU => ?_⟩
  · refine (IntegrableOn.locallyIntegrableOn ?_)
    refine (hgi.add (integrable_finsetSum X fun p _ => hgradi p).integrableOn).mono_set ?_
    exact hUΩ.trans interior_subset
  have hφΩ : tsupport φ ⊆ interior Ω := hφU.trans hUΩ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hψ : ∀ v : ℂ, ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) := fun v =>
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hψc : ∀ v : ℂ, HasCompactSupport (fun y => fderiv ℝ φ y v) := fun v =>
    hc.fderiv_apply (𝕜 := ℝ) v
  have hψs : ∀ v : ℂ, tsupport (fun y => fderiv ℝ φ y v) ⊆ interior Ω := fun v =>
    (tsupport_fderiv_apply_subset ℝ v).trans hφΩ
  have hd2c : ∀ v w : ℂ, Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x w) := fun v w =>
    ((hψ v).continuous_fderiv (by simp)).clm_apply continuous_const
  have hlapc := continuous_laplacian_of_contDiff hφ
  obtain ⟨B1, hB1⟩ := bounded_of_contDiff ((hψ 1).continuous) (hψc 1)
  obtain ⟨B2, hB2⟩ := bounded_of_contDiff ((hψ Complex.I).continuous) (hψc Complex.I)
  obtain ⟨B11, hB11⟩ := bounded_of_contDiff (hd2c 1 1) ((hψc 1).fderiv_apply (𝕜 := ℝ) 1)
  obtain ⟨B22, hB22⟩ := bounded_of_contDiff (hd2c Complex.I Complex.I)
    ((hψc Complex.I).fderiv_apply (𝕜 := ℝ) Complex.I)
  obtain ⟨BL, hBL⟩ := bounded_of_contDiff hlapc (hasCompactSupport_laplacian hφ hc)
  obtain ⟨Bg, hBg⟩ := exists_norm_gradient_le hφ1 hc
  -- off `Ω`, the test function and its derivatives vanish
  have hout : ∀ x, x ∉ Ω → x ∉ tsupport φ := fun x hx h => hx (interior_subset (hφΩ h))
  -- (a) the weak gradient against `∂φ`
  have hwg : ∫ x in Ω, inner ℝ (g x) (gradient φ x) = -∫ x in Ω, u x * Δ φ x := by
    have h1 := (hw.2.2 _ (hψ 1) (hψc 1) (hψs 1)).1
    have h2 := (hw.2.2 _ (hψ Complex.I) (hψc Complex.I) (hψs Complex.I)).2
    have i1 : IntegrableOn (fun x => (g x).re * fderiv ℝ φ x 1) Ω :=
      hgi.re.mul_bdd (hψ 1).continuous.aestronglyMeasurable (Eventually.of_forall hB1)
    have i2 : IntegrableOn (fun x => (g x).im * fderiv ℝ φ x Complex.I) Ω :=
      hgi.im.mul_bdd (hψ Complex.I).continuous.aestronglyMeasurable (Eventually.of_forall hB2)
    have i3 : IntegrableOn (fun x => u x * fderiv ℝ (fun y => fderiv ℝ φ y 1) x 1) Ω :=
      hui.mul_bdd (hd2c 1 1).aestronglyMeasurable (Eventually.of_forall hB11)
    have i4 : IntegrableOn (fun x => u x * fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) x
        Complex.I) Ω :=
      hui.mul_bdd (hd2c _ _).aestronglyMeasurable (Eventually.of_forall hB22)
    simp only [inner_eq_re_mul_add, laplacian_eq_pd_fun hφ, mul_add]
    rw [integral_add i1 i2, integral_add i3 i4]
    simp only [hu] at h1 h2 ⊢
    linarith
  -- (b) splitting `w = w^♮ + ∑ f`
  have hwsplit : ∫ x in Ω, w x * Δ φ x =
      (∫ x in Ω, u x * Δ φ x) + ∑ p ∈ X, ∫ x in Ω, truncLog (1 / 4) (x - p) * Δ φ x := by
    have iu : IntegrableOn (fun x => u x * Δ φ x) Ω :=
      hui.mul_bdd hlapc.aestronglyMeasurable (Eventually.of_forall hBL)
    have ip : ∀ p ∈ X, IntegrableOn (fun x => truncLog (1 / 4) (x - p) * Δ φ x) Ω := fun p _ =>
      ((hfi p).mul_bdd hlapc.aestronglyMeasurable (Eventually.of_forall hBL)).integrableOn
    rw [← integral_finsetSum X ip, ← integral_add iu (integrable_finsetSum X ip)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hu, ← Finset.sum_mul]
    ring
  -- (c) restriction to `Ω`
  have hrestr : ∀ F : ℂ → ℝ, ∫ x in Ω, F x * Δ φ x = ∫ x, F x * Δ φ x := fun F =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [laplacian_eq_zero_of_notMem_tsupport hφ (hout x hx), mul_zero]
  have hgΩ : ∫ x in Ω, inner ℝ (g x) (gradient φ x) = ∫ x, inner ℝ (g x) (gradient φ x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (hout x hx), inner_zero_right]
  -- (d) assemble
  have hE : ∫ x, inner ℝ (input63Field X g x) (gradient φ x) =
      (∫ x, inner ℝ (g x) (gradient φ x)) +
        ∑ p ∈ X, ∫ x, inner ℝ (gradient (truncLog (1 / 4)) (x - p)) (gradient φ x) := by
    have ig : Integrable (fun x => inner ℝ (g x) (gradient φ x)) :=
      integrable_inner_of_integrableOn hΩm hgi (aestronglyMeasurable_gradient _) hBg
        fun x hx => gradient_eq_zero_of_notMem_tsupport (hout x hx)
    have ip : ∀ p ∈ X, Integrable (fun x => inner ℝ (gradient (truncLog (1 / 4 : ℝ)) (x - p))
        (gradient φ x)) := fun p _ => integrable_inner_gradient_truncLog (by norm_num) p hφ hc
    rw [← integral_finsetSum X ip, ← integral_add ig (integrable_finsetSum X ip)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [input63Field, inner_add_left, sum_inner]
  have hfilter : ∑ p ∈ X.filter (· ∈ sqShrink a₀ t (1 / 2)), φ p = ∑ p ∈ X, φ p := by
    exact Finset.sum_filter_of_ne fun p _ hp =>
      interior_subset (hφU (subset_tsupport φ (Function.mem_support.2 hp)))
  rw [hE, ← hgΩ, hwg, finsum_mem_coe_finset]
  have hw' := hΔ φ hφ hc hφU
  rw [hfilter, ← hrestr, hwsplit] at hw'
  simp only [hrestr, integral_truncLog_mul_laplacian hφ hc (by norm_num : (0 : ℝ) < 1 / 4),
    integral_inner_gradient_truncLog hφ1 (by norm_num : (0 : ℝ) < 1 / 4)] at hw' ⊢
  have hneg : ∑ p ∈ X, 2 * π * (Real.circleAverage φ p (1 / 4) - φ p) =
      -∑ p ∈ X, 2 * π * (φ p - Real.circleAverage φ p (1 / 4)) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
  linarith

end Bridge

end Sphere

end SandierSerfaty

end
