/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Statements
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Integration by parts for locally Lipschitz functions against a `C¹` test function

For a locally Lipschitz `u : ℂ → ℝ`, `C¹` compactly supported `φ` and a direction `e`,
`∫ u ∂ₑφ = -∫ (∂ₑu) φ`, with `∂ₑu` the a.e. derivative (Rademacher). This is what is needed to show that a
locally Lipschitz function has weak gradient equal to its classical (a.e.) gradient
(`Lower.hasWeakGradientOn_of_locallyLipschitz`), the form in which `Input63Statement` consumes `H¹` data.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- Integration by parts for a globally Lipschitz function. -/
theorem integral_mul_fderiv_of_lipschitz {u : ℂ → ℝ} {K : NNReal} (hu : LipschitzWith K u)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (e : ℂ) :
    ∫ x, u x * fderiv ℝ φ x e = -∫ x, fderiv ℝ u x e * φ x := by
  obtain ⟨Lφ, hLφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by norm_num)
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let ρ : ℝ := r + ‖e‖ + 1
  let B : Set ℂ := closedBall 0 ρ
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hint : ∀ f : ℂ → ℝ, Continuous f → Integrable (fun x => f x * φ x) := fun f hf =>
    (hf.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  -- the difference quotient
  let q : ℝ → ℂ → ℝ := fun t x => t⁻¹ * (u (x + t • e) - u x)
  have hφint : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have hq0 : ∀ t : ℝ, t ≠ 0 →
      ∫ x, q t x * φ x = ∫ x, u x * (t⁻¹ * (φ (x - t • e) - φ x)) := by
    intro t ht
    have h1 : ∫ x, u (x + t • e) * φ x = ∫ x, u x * φ (x - t • e) := by
      have := integral_add_right_eq_self (μ := (volume : Measure ℂ))
        (fun x => u x * φ (x - t • e)) (t • e)
      simpa using this
    have hu1 : Integrable (fun x => u (x + t • e) * φ x) := by
      have hcu : Continuous fun x => u (x + t • e) := hu.continuous.comp (by fun_prop)
      have := hcu.mul hφ.continuous
      exact this.integrable_of_hasCompactSupport hc.mul_left
    have hu0 := hint u hu.continuous
    have hu2 : Integrable (fun x => u x * φ (x - t • e)) := by
      have hcφ : Continuous fun x => φ (x - t • e) := hφ.continuous.comp (by fun_prop)
      have := hu.continuous.mul hcφ
      refine this.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.mul_left ?_
      exact hc.comp_homeomorph (Homeomorph.subRight (t • e))
    calc ∫ x, q t x * φ x = t⁻¹ * ((∫ x, u (x + t • e) * φ x) - ∫ x, u x * φ x) := by
          simp only [q]
          rw [← integral_sub hu1 hu0, ← integral_const_mul]
          congr 1; funext x; ring
      _ = ∫ x, u x * (t⁻¹ * (φ (x - t • e) - φ x)) := by
          rw [h1, ← integral_sub hu2 hu0, ← integral_const_mul]
          congr 1; funext x; ring
  -- limit of the left side
  have hlimL : Tendsto (fun t : ℝ => ∫ x, q t x * φ x) (𝓝[≠] 0) (𝓝 (∫ x, fderiv ℝ u x e * φ x)) := by
    have hlim : ∀ᵐ x ∂(volume : Measure ℂ),
        Tendsto (fun t => q t x * φ x) (𝓝[≠] 0) (𝓝 (fderiv ℝ u x e * φ x)) := by
      filter_upwards [hu.ae_differentiableAt] with x hx
      have h1 : HasDerivAt (fun t : ℝ => u (x + t • e)) (fderiv ℝ u x e) 0 := by
        have : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
        have h2 : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • e) := by
          simpa using hx.hasFDerivAt
        exact h2.comp_hasDerivAt 0 this
      exact (h1.tendsto_slope_zero.congr fun t => by simp [q]).mul_const _
    have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂(volume : Measure ℂ),
        ‖q t x * φ x‖ ≤ (K : ℝ) * ‖e‖ * |φ x| := by
      refine Eventually.of_forall fun t => Eventually.of_forall fun x => ?_
      by_cases ht : t = 0
      · simp only [q, ht, inv_zero, zero_mul, norm_zero]; positivity
      · have := hu.dist_le_mul (x + t • e) x
        rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
        rw [norm_mul, Real.norm_eq_abs (φ x)]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        simp only [q, Real.norm_eq_abs, abs_mul, abs_inv]
        rw [inv_mul_le_iff₀ (abs_pos.2 ht)]
        calc |u (x + t • e) - u x| ≤ K * (|t| * ‖e‖) := this
          _ = |t| * (K * ‖e‖) := by ring
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (K : ℝ) * ‖e‖ * |φ x|)
      (Eventually.of_forall fun t => ?_) hbound ?_ hlim
    · simp only [q]
      have hcu : Continuous fun x => u (x + t • e) := hu.continuous.comp (by fun_prop)
      exact (((hcu.sub hu.continuous).const_mul _).mul hφ.continuous).aestronglyMeasurable
    · exact (hφint.abs.const_mul _)
  -- limit of the right side
  have hlimR : Tendsto (fun t : ℝ => ∫ x, u x * (t⁻¹ * (φ (x - t • e) - φ x))) (𝓝[≠] 0)
      (𝓝 (-∫ x, u x * fderiv ℝ φ x e)) := by
    have hlim : ∀ x : ℂ, Tendsto (fun t : ℝ => u x * (t⁻¹ * (φ (x - t • e) - φ x))) (𝓝[≠] 0)
        (𝓝 (-(u x * fderiv ℝ φ x e))) := by
      intro x
      have h1 : HasDerivAt (fun t : ℝ => φ (x - t • e)) (-fderiv ℝ φ x e) 0 := by
        have : HasDerivAt (fun t : ℝ => x - t • e) (-e) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_sub x
        have h2 : HasFDerivAt φ (fderiv ℝ φ x) (x - (0 : ℝ) • e) := by
          simpa using (hφ.differentiable (by norm_num) x).hasFDerivAt
        have h3 := h2.comp_hasDerivAt (0 : ℝ) this
        rw [map_neg] at h3
        exact h3
      have hs : Tendsto (fun t : ℝ => t⁻¹ * (φ (x - t • e) - φ x)) (𝓝[≠] 0)
          (𝓝 (-fderiv ℝ φ x e)) :=
        h1.tendsto_slope_zero.congr fun t => by simp [smul_eq_mul]
      have := hs.const_mul (u x)
      simpa using this
    -- support of the difference quotient lies in `B`
    have hsupp : ∀ t : ℝ, |t| ≤ 1 → ∀ x, x ∉ B → φ (x - t • e) - φ x = 0 := by
      intro t ht x hx
      have h1 : x ∉ tsupport φ := fun h => hx (by
        have := hr h
        simp only [B, mem_closedBall, dist_zero_right] at this ⊢
        linarith [norm_nonneg e])
      have h2 : x - t • e ∉ tsupport φ := fun h => hx (by
        have h' := hr h
        simp only [B, mem_closedBall, dist_zero_right] at h' ⊢
        have : ‖x‖ ≤ ‖x - t • e‖ + ‖t • e‖ := by
          have := norm_add_le (x - t • e) (t • e)
          simpa using this
        rw [norm_smul, Real.norm_eq_abs] at this
        have : |t| * ‖e‖ ≤ ‖e‖ := by
          calc |t| * ‖e‖ ≤ 1 * ‖e‖ := by gcongr
            _ = ‖e‖ := one_mul _
        linarith)
      rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, sub_zero]
    obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hu.continuous.continuousOn
    have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂(volume : Measure ℂ),
        ‖u x * (t⁻¹ * (φ (x - t • e) - φ x))‖ ≤ B.indicator (fun _ => M * (Lφ * ‖e‖)) x := by
      have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| ≤ 1 := by
        have : ∀ᶠ t in 𝓝 (0 : ℝ), |t| ≤ 1 := by
          have := (continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))
          exact this.mono fun t ht => le_of_lt ht
        exact eventually_nhdsWithin_of_eventually_nhds this
      filter_upwards [hnear, self_mem_nhdsWithin] with t ht1 ht0
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, norm_mul]
        have hq : ‖t⁻¹ * (φ (x - t • e) - φ x)‖ ≤ Lφ * ‖e‖ := by
          have := hLφ.dist_le_mul (x - t • e) x
          rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
            Real.norm_eq_abs] at this
          rw [norm_mul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ (abs_pos.2 ht0)]
          calc ‖φ (x - t • e) - φ x‖ ≤ Lφ * (|t| * ‖e‖) := by simpa [Real.norm_eq_abs] using this
            _ = |t| * (Lφ * ‖e‖) := by ring
        calc ‖u x‖ * ‖t⁻¹ * (φ (x - t • e) - φ x)‖ ≤ M * (Lφ * ‖e‖) :=
              mul_le_mul (hM x hx) hq (norm_nonneg _) ((norm_nonneg _).trans (hM x hx))
          _ = _ := rfl
      · rw [Set.indicator_of_notMem hx, hsupp t ht1 x hx]; simp
    have hdct := tendsto_integral_filter_of_dominated_convergence
      (f := fun x => -(u x * fderiv ℝ φ x e))
      (fun x => B.indicator (fun _ => M * (Lφ * ‖e‖)) x)
      (Eventually.of_forall fun t => ?_) hbound ?_ (Eventually.of_forall fun x => ?_)
    · rwa [integral_neg] at hdct
    · have hcφ : Continuous fun x => φ (x - t • e) := hφ.continuous.comp (by fun_prop)
      exact (hu.continuous.mul (continuous_const.mul (hcφ.sub hφ.continuous))).aestronglyMeasurable
    · exact (integrable_indicator_iff hBc.measurableSet).2
        (integrableOn_const hBc.measure_lt_top.ne)
    · exact hlim x
  have := tendsto_nhds_unique (hlimL.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hq0 t ht)) hlimR
  linarith

/-- Integration by parts for a locally Lipschitz function. -/
theorem integral_mul_fderiv_of_locallyLipschitz {u : ℂ → ℝ} (hu : LocallyLipschitz u)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (e : ℂ) :
    ∫ x, u x * fderiv ℝ φ x e = -∫ x, fderiv ℝ u x e * φ x := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨K, hK⟩ := (hu.locallyLipschitzOn (s := closedBall (0 : ℂ) (r + 1))).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall _ _)
  obtain ⟨ũ, hũ, hEq⟩ := hK.extend_real
  have h1 := integral_mul_fderiv_of_lipschitz hũ hφ hc e
  have hsupp : ∀ x, x ∉ tsupport φ → φ x = 0 ∧ fderiv ℝ φ x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport hx, by
      have := (hc.fderiv (𝕜 := ℝ)).isCompact
      exact fderiv_of_notMem_tsupport ℝ hx⟩
  have hL : ∫ x, u x * fderiv ℝ φ x e = ∫ x, ũ x * fderiv ℝ φ x e := by
    congr 1; funext x
    by_cases hx : x ∈ tsupport φ
    · have : x ∈ closedBall (0 : ℂ) (r + 1) := by
        have := hr hx
        exact closedBall_subset_closedBall (by linarith) this
      rw [hEq this]
    · rw [(hsupp x hx).2]; simp
  have hR : ∫ x, fderiv ℝ u x e * φ x = ∫ x, fderiv ℝ ũ x e * φ x := by
    congr 1; funext x
    by_cases hx : x ∈ tsupport φ
    · have hxb : x ∈ ball (0 : ℂ) (r + 1) := by
        have := hr hx
        simp only [mem_closedBall, dist_zero_right, mem_ball] at this ⊢
        linarith
      have hev : u =ᶠ[𝓝 x] ũ :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxb) (fun y hy =>
          hEq (ball_subset_closedBall hy))
      rw [hev.fderiv_eq]
    · rw [(hsupp x hx).1]; simp
  rw [hL, hR]; exact h1

/-- The complex-valued gradient field `∂ₓ u + i ∂ᵧ u` of a function. -/
@[expose] noncomputable def gradC (u : ℂ → ℝ) (x : ℂ) : ℂ :=
  (fderiv ℝ u x 1 : ℝ) + (fderiv ℝ u x Complex.I : ℝ) * Complex.I

@[simp] theorem gradC_re (u : ℂ → ℝ) (x : ℂ) : (gradC u x).re = fderiv ℝ u x 1 := by
  simp [gradC]

@[simp] theorem gradC_im (u : ℂ → ℝ) (x : ℂ) : (gradC u x).im = fderiv ℝ u x Complex.I := by
  simp [gradC]

theorem measurable_gradC (u : ℂ → ℝ) : Measurable (gradC u) := by
  unfold gradC
  exact (Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ u 1)).add
    ((Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ u Complex.I)).mul_const _)

/-- A locally Lipschitz function has weak gradient equal to its a.e. gradient on a compact set. -/
theorem hasWeakGradientOn_of_locallyLipschitz {u : ℂ → ℝ} (hu : LocallyLipschitz u) {Ω : Set ℂ}
    (hΩ : IsCompact Ω) : HasWeakGradientOn Ω u (gradC u) := by
  obtain ⟨R, hR⟩ := hΩ.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨K, hK⟩ := (hu.locallyLipschitzOn (s := closedBall (0 : ℂ) (R + 1))).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall _ _)
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hΩ.measure_lt_top⟩
  have hgb : ∀ x ∈ Ω, ‖gradC u x‖ ≤ 2 * K := by
    intro x hx
    have hxb : x ∈ ball (0 : ℂ) (R + 1) := by
      have := hR hx
      simp only [mem_closedBall, dist_zero_right, mem_ball] at this ⊢
      linarith
    have hf : ‖fderiv ℝ u x‖ ≤ K :=
      norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hxb)
        (hK.mono ball_subset_closedBall)
    have h1 : ‖fderiv ℝ u x 1‖ ≤ K := by
      calc ‖fderiv ℝ u x 1‖ ≤ ‖fderiv ℝ u x‖ * ‖(1 : ℂ)‖ := (fderiv ℝ u x).le_opNorm _
        _ ≤ K := by simpa using hf
    have h2 : ‖fderiv ℝ u x Complex.I‖ ≤ K := by
      calc ‖fderiv ℝ u x Complex.I‖ ≤ ‖fderiv ℝ u x‖ * ‖Complex.I‖ := (fderiv ℝ u x).le_opNorm _
        _ ≤ K := by simpa using hf
    have := Complex.norm_le_abs_re_add_abs_im (gradC u x)
    rw [gradC_re, gradC_im, ← Real.norm_eq_abs, ← Real.norm_eq_abs] at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hΩ.exists_bound_of_continuousOn hu.continuous.continuousOn
    exact MemLp.of_bound hu.continuous.aestronglyMeasurable M
      ((ae_restrict_iff' hΩ.measurableSet).2 (Eventually.of_forall hM))
  · exact MemLp.of_bound (measurable_gradC u).aestronglyMeasurable (2 * K)
      ((ae_restrict_iff' hΩ.measurableSet).2 (Eventually.of_forall hgb))
  · intro φ hφ hc hsub
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_cast)
    have hnot : ∀ x, x ∉ Ω → φ x = 0 ∧ fderiv ℝ φ x = 0 := by
      intro x hx
      have hx' : x ∉ tsupport φ := fun h => hx (interior_subset (hsub h))
      exact ⟨image_eq_zero_of_notMem_tsupport hx', fderiv_of_notMem_tsupport ℝ hx'⟩
    constructor
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hnot x hx).2]; simp),
        integral_mul_fderiv_of_locallyLipschitz hu hφ1 hc 1,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hnot x hx).1]; simp)]
      simp
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hnot x hx).2]; simp),
        integral_mul_fderiv_of_locallyLipschitz hu hφ1 hc Complex.I,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [(hnot x hx).1]; simp)]
      simp

end Lower

end Sphere

end SandierSerfaty

end
