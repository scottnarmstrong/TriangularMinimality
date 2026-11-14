/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.TruncLogPairing
public import SandierSerfaty.Screening.TruncDiff
public import SandierSerfaty.Sphere.Lower.LipschitzWeak
public import SandierSerfaty.Analysis.GreenIdentity
public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Screening.TruncFieldWeak
public import SandierSerfaty.Analysis.PolarMean

/-!
# Green's identity for the truncated logarithm

`Bridge.integral_truncLog_mul_laplacian`: for smooth compactly supported `φ`, `η > 0` and `p ∈ ℂ`,
```
∫ f_η(x - p) Δφ(x) dx = 2π (⨍_{∂B(p, η)} φ - φ(p)) = -∫ ⟨∇f_η(· - p), ∇φ⟩,
```
i.e. `f_η(· - p)` has weak gradient `∇f_η(· - p)` against second derivatives of test functions.

**Proof.** For `0 < ε ≤ η`, `f_η = f_ε - f_{ε,η}` off `p`, with `f_{ε,η} = truncDiff ε η` Lipschitz, so
integration by parts (`Lower.integral_mul_fderiv_of_lipschitz`) and the pairing identity
`integral_inner_gradient_truncLog` give
`∫ f_η Δφ - 2π(⨍_η φ - φ(p)) = ∫ f_ε Δφ - 2π(⨍_ε φ - φ(p))`. The right side is `O(ε)`
(`∫ f_ε = πε²/2`, `φ` Lipschitz), so the left side vanishes.
-/

open MeasureTheory Set Filter Topology Metric InnerProductSpace
open scoped ENNReal NNReal Real ContDiff Laplacian

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open Screening

theorem inner_gradient_eq_fderiv (u φ : ℂ → ℝ) (x : ℂ) :
    inner ℝ (gradient u x) (gradient φ x) =
      fderiv ℝ u x 1 * fderiv ℝ φ x 1 + fderiv ℝ u x Complex.I * fderiv ℝ φ x Complex.I :=
  Torus.inner_gradient_gradient u φ x

/-- **Integration by parts against the Laplacian** for a Lipschitz function. -/
theorem integral_mul_laplacian_of_lipschitz {D : ℂ → ℝ} {K : ℝ≥0} (hD : LipschitzWith K D)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ x, D x * Δ φ x = -∫ x, inner ℝ (gradient D x) (gradient φ x) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hlap : ∀ x, Δ φ x = fderiv ℝ (fun y => fderiv ℝ φ y 1) x 1 +
      fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) x Complex.I := fun x =>
    Analysis.laplacian_eq_pd hφ2.contDiffAt
  have hψ : ∀ v : ℂ, ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) := fun v =>
    (hφ.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const
  have hψc : ∀ v : ℂ, HasCompactSupport (fun y => fderiv ℝ φ y v) := fun v =>
    hc.fderiv_apply (𝕜 := ℝ) v
  have hint : ∀ v w : ℂ, Integrable (fun x => D x * fderiv ℝ (fun y => fderiv ℝ φ y v) x w) := by
    intro v w
    refine Continuous.integrable_of_hasCompactSupport (hD.continuous.mul ?_) ?_
    · exact ((hψ v).continuous_fderiv one_ne_zero).clm_apply continuous_const
    · exact ((hψc v).fderiv_apply (𝕜 := ℝ) w).mul_left
  have hint2 : ∀ v w : ℂ, Integrable (fun x => fderiv ℝ D x v * fderiv ℝ φ x w) := by
    intro v w
    obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖fderiv ℝ D x v‖ ≤ B :=
      ⟨K * ‖v‖, fun x => ((fderiv ℝ D x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hD) (norm_nonneg _))⟩
    have hc2 : Integrable (fun x => fderiv ℝ φ x w) :=
      (hψ w).continuous.integrable_of_hasCompactSupport (hψc w)
    refine (hc2.norm.const_mul B).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (measurable_fderiv_apply_const ℝ D v).aestronglyMeasurable.mul hc2.aestronglyMeasurable
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  simp only [hlap, mul_add, inner_gradient_eq_fderiv]
  rw [integral_add (hint 1 1) (hint _ _), integral_add (hint2 1 1) (hint2 _ _),
    Lower.integral_mul_fderiv_of_lipschitz hD (hψ 1) (hψc 1) 1,
    Lower.integral_mul_fderiv_of_lipschitz hD (hψ _) (hψc _) Complex.I]
  ring

theorem lipschitzWith_truncDiff_sub {ε η : ℝ} (hε : 0 < ε) (hεη : ε ≤ η) (p : ℂ) :
    LipschitzWith (Real.toNNReal ε⁻¹) (fun x => truncDiff ε η (x - p)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have := (lipschitzWith_truncDiff hε hεη).dist_le_mul (x - p) (y - p)
  rwa [dist_sub_right] at this

theorem gradient_truncDiff_sub {ε η : ℝ} (hε : 0 < ε) (hεη : ε ≤ η) (p x : ℂ) (hx0 : x - p ≠ 0)
    (hxε : ‖x - p‖ ≠ ε) (hxη : ‖x - p‖ ≠ η) :
    gradient (fun y => truncDiff ε η (y - p)) x =
      gradient (truncLog ε) (x - p) - gradient (truncLog η) (x - p) := by
  have e : (fun y => truncDiff ε η (y - p)) = fun y => truncDiff ε η (y + -p) := by
    ext y; rw [sub_eq_add_neg]
  rw [e, gradient_comp_add_right, ← sub_eq_add_neg, gradient_truncDiff hε hεη hx0 hxε hxη]

theorem integrable_inner_gradient_truncLog {η : ℝ} (hη : 0 < η) (p : ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => inner ℝ (gradient (truncLog η) (x - p)) (gradient φ x)) := by
  obtain ⟨B, hB⟩ := exists_norm_gradient_le (hφ.of_le (by norm_cast)) hc
  refine ((integrable_gradient_truncLog hη p).norm.mul_const B).mono'
    (((measurable_gradient _).comp (measurable_id.sub_const p)).aestronglyMeasurable.inner
      (measurable_gradient φ).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _))

/-- The Laplacian of a test function as the sum of second partial derivatives. -/
theorem laplacian_eq_pd_fun {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Δ φ = fun x => fderiv ℝ (fun y => fderiv ℝ φ y 1) x 1 +
      fderiv ℝ (fun y => fderiv ℝ φ y Complex.I) x Complex.I := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  funext x
  exact Analysis.laplacian_eq_pd hφ2.contDiffAt

theorem continuous_laplacian_of_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) : Continuous (Δ φ) := by
  rw [laplacian_eq_pd_fun hφ]
  have h : ∀ v w : ℂ, Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ φ y v) x w) := by
    intro v w
    have hψ : ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) :=
      (hφ.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const
    exact (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact (h 1 1).add (h _ _)

theorem hasCompactSupport_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    HasCompactSupport (Δ φ) := by
  rw [laplacian_eq_pd_fun hφ]
  exact ((hc.fderiv_apply (𝕜 := ℝ) 1).fderiv_apply (𝕜 := ℝ) 1).add
    ((hc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _)

theorem ae_ne_sub (p : ℂ) (η : ℝ) : ∀ᵐ x : ℂ, x - p ≠ 0 ∧ ‖x - p‖ ≠ η := by
  have h1 : ∀ᵐ x : ℂ, x ∉ ({p} : Set ℂ) := (countable_singleton p).ae_notMem volume
  have h2 : ∀ᵐ x : ℂ, x ∉ sphere p η :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume p η)
  filter_upwards [h1, h2] with x hx1 hx2
  refine ⟨sub_ne_zero.2 hx1, fun h => hx2 ?_⟩
  rw [mem_sphere, dist_eq_norm, h]

/-- The two-scale identity `∫ f_η Δφ = ∫ f_ε Δφ + 2π (⨍_η φ - ⨍_ε φ)`. -/
theorem integral_truncLog_mul_laplacian_eq {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {ε η : ℝ} (hε : 0 < ε) (hεη : ε ≤ η) (p : ℂ) :
    ∫ x, truncLog η (x - p) * Δ φ x =
      (∫ x, truncLog ε (x - p) * Δ φ x) +
        2 * π * (Real.circleAverage φ p η - Real.circleAverage φ p ε) := by
  have hη : 0 < η := hε.trans_le hεη
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
  have hlapc := continuous_laplacian_of_contDiff hφ
  have hlaps := hasCompactSupport_laplacian hφ hc
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Δ φ x‖ ≤ M := hlapc.bounded_above_of_compact_support hlaps
  have hintf : Integrable (fun x => truncLog ε (x - p) * Δ φ x) :=
    ((integrable_truncLog hε).comp_sub_right p).mul_bdd hlapc.aestronglyMeasurable
      (Eventually.of_forall hM)
  -- `f_η = f_ε - f_{ε,η}` off `p`
  have hsplit : (fun x => truncLog η (x - p) * Δ φ x) =ᵐ[volume]
      fun x => truncLog ε (x - p) * Δ φ x - truncDiff ε η (x - p) * Δ φ x := by
    filter_upwards [ae_ne_sub p η] with x hx
    rw [← sub_mul, ← truncLog_sub_truncLog hε hεη hx.1]
    ring
  have hD := lipschitzWith_truncDiff_sub hε hεη p
  have hintD : Integrable (fun x => truncDiff ε η (x - p) * Δ φ x) :=
    (hD.continuous.mul hlapc).integrable_of_hasCompactSupport hlaps.mul_left
  rw [integral_congr_ae hsplit, integral_sub hintf hintD,
    integral_mul_laplacian_of_lipschitz hD hφ hc]
  -- the gradient of `f_{ε,η}`
  have hgrad : (fun x => inner ℝ (gradient (fun y => truncDiff ε η (y - p)) x) (gradient φ x))
      =ᵐ[volume] fun x => inner ℝ (gradient (truncLog ε) (x - p)) (gradient φ x) -
        inner ℝ (gradient (truncLog η) (x - p)) (gradient φ x) := by
    filter_upwards [ae_ne_sub p ε, ae_ne_sub p η] with x h1 h2
    rw [gradient_truncDiff_sub hε hεη p x h1.1 h1.2 h2.2, inner_sub_left]
  rw [integral_congr_ae hgrad, integral_sub (integrable_inner_gradient_truncLog hε p hφ hc)
      (integrable_inner_gradient_truncLog hη p hφ hc),
    integral_inner_gradient_truncLog hφ1 hε p, integral_inner_gradient_truncLog hφ1 hη p]
  ring

theorem abs_integral_truncLog_mul_le {φ : ℂ → ℝ} {M : ℝ} (hM : ∀ x, ‖Δ φ x‖ ≤ M)
    (_hlapc : Continuous (Δ φ)) {ε : ℝ} (hε : 0 < ε) (p : ℂ) :
    |∫ x, truncLog ε (x - p) * Δ φ x| ≤ M * (π * ε ^ 2 / 2) := by
  have hint : Integrable (fun x => M * truncLog ε (x - p)) :=
    ((integrable_truncLog hε).comp_sub_right p).const_mul M
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)).trans_eq ?_
  · rw [norm_mul, Real.norm_of_nonneg (truncLog_nonneg _ _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM x) (truncLog_nonneg _ _)
  · rw [integral_const_mul, integral_sub_right_eq_self (fun x => truncLog ε x) p,
      Torus.integral_truncLog hε]

theorem abs_circleAverage_sub_le {φ : ℂ → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (p : ℂ) {ε : ℝ}
    (hε : 0 < ε) : |Real.circleAverage φ p ε - φ p| ≤ L * ε := by
  have hci : CircleIntegrable φ p ε := hφ.continuous.continuousOn.circleIntegrable'
  have hbd : ∀ x ∈ sphere p |ε|, |φ x - φ p| ≤ L * ε := by
    intro x hx
    rw [mem_sphere, abs_of_pos hε] at hx
    have := hφ.dist_le_mul x p
    rwa [Real.dist_eq, hx] at this
  rw [abs_le]
  constructor
  · have h := Real.circleAverage_mono (c := p) (R := ε) (f₁ := fun _ => φ p - L * ε)
      (continuous_const.continuousOn.circleIntegrable') hci
      (fun x hx => by have := (abs_le.1 (hbd x hx)).1; linarith)
    rw [Real.circleAverage_const] at h
    linarith
  · have h := Real.circleAverage_mono_on_of_le_circle hci
      (fun x hx => by have := (abs_le.1 (hbd x hx)).2; linarith : ∀ x ∈ sphere p |ε|,
        φ x ≤ φ p + L * ε)
    linarith

theorem eq_zero_of_abs_le_mul {K C δ : ℝ} (hδ : 0 < δ) (h : ∀ ε, 0 < ε → ε ≤ δ → |K| ≤ C * ε) :
    K = 0 := by
  by_contra hK
  have hK0 : 0 < |K| := abs_pos.2 hK
  set ε := min δ (|K| / (2 * (|C| + 1))) with hεdef
  have hε : 0 < ε := lt_min hδ (by positivity)
  have h1 := h ε hε (min_le_left _ _)
  have h2 : ε ≤ |K| / (2 * (|C| + 1)) := min_le_right _ _
  have h3 : C * ε ≤ |C| * ε := mul_le_mul_of_nonneg_right (le_abs_self C) hε.le
  have h4 : |C| * ε ≤ |C| * (|K| / (2 * (|C| + 1))) :=
    mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
  have h5 : |C| * (|K| / (2 * (|C| + 1))) < |K| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

theorem abs_integral_truncLog_mul_laplacian_sub_le {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) {η : ℝ} (p : ℂ) {M : ℝ} (hM : ∀ x, ‖Δ φ x‖ ≤ M) {L : ℝ≥0}
    (hL : LipschitzWith L φ) {ε : ℝ} (hε : 0 < ε) (hεη : ε ≤ η) (hε1 : ε ≤ 1) :
    |(∫ x, truncLog η (x - p) * Δ φ x) - 2 * π * (Real.circleAverage φ p η - φ p)| ≤
      (M * π / 2 + 2 * π * L) * ε := by
  have hlapc := continuous_laplacian_of_contDiff hφ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have e : (∫ x, truncLog η (x - p) * Δ φ x) - 2 * π * (Real.circleAverage φ p η - φ p) =
      (∫ x, truncLog ε (x - p) * Δ φ x) - 2 * π * (Real.circleAverage φ p ε - φ p) := by
    rw [integral_truncLog_mul_laplacian_eq hφ hc hε hεη p]; ring
  rw [e]
  have h1 := abs_integral_truncLog_mul_le hM hlapc hε p
  have h2 := abs_circleAverage_sub_le hL p hε
  have h3 : M * (π * ε ^ 2 / 2) ≤ M * π / 2 * ε := by
    have : ε ^ 2 ≤ ε := by nlinarith
    have hπ := Real.pi_pos
    calc M * (π * ε ^ 2 / 2) = M * π / 2 * ε ^ 2 := by ring
      _ ≤ M * π / 2 * ε := mul_le_mul_of_nonneg_left this (by positivity)
  have h4 : |2 * π * (Real.circleAverage φ p ε - φ p)| ≤ 2 * π * (L * ε) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc |(∫ x, truncLog ε (x - p) * Δ φ x) - 2 * π * (Real.circleAverage φ p ε - φ p)|
      ≤ |∫ x, truncLog ε (x - p) * Δ φ x| + |2 * π * (Real.circleAverage φ p ε - φ p)| :=
        abs_sub _ _
    _ ≤ M * π / 2 * ε + 2 * π * (L * ε) := by linarith
    _ = (M * π / 2 + 2 * π * L) * ε := by ring

/-- **Green's identity for the truncated logarithm**:
`∫ f_η(x - p) Δφ(x) dx = 2π (⨍_{∂B(p, η)} φ - φ(p))`. -/
theorem integral_truncLog_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {η : ℝ} (hη : 0 < η) (p : ℂ) :
    ∫ x, truncLog η (x - p) * Δ φ x = 2 * π * (Real.circleAverage φ p η - φ p) := by
  have hlapc := continuous_laplacian_of_contDiff hφ
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖Δ φ x‖ ≤ M :=
    hlapc.bounded_above_of_compact_support (hasCompactSupport_laplacian hφ hc)
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)
  have key := eq_zero_of_abs_le_mul (lt_min hη one_pos) fun ε hε hεδ =>
    abs_integral_truncLog_mul_laplacian_sub_le hφ hc p hM hL hε (hεδ.trans (min_le_left _ _))
      (hεδ.trans (min_le_right _ _))
  exact sub_eq_zero.1 key

end Bridge

end Sphere

end SandierSerfaty

end
