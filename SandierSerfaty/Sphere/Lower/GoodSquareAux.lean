/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GoodSquareWeak

/-!
# Elementary estimates for the good-square proposition (sphere note, Proposition 6.13)

* `Lower.integral_truncLog_density_sub_le`: `∫ f_{1/4}(x-z) m(x) dx - m̄ ∫_Q f_{1/4}(x-z) dx ≤ (π/32)(δ + m₊ 1_{z ∉ Q^{1/4}})`.
* `Lower.card_filter_not_shrink_le`: at most `7 t` of the separated points of `Q` lie within `1/4` of `∂Q`.
* `Lower.integral_norm_gradC_sub_le`: `∫_Q |∇(u - v)|² ≤ (1+ε) ∫_Q |∇u|² + (1+1/ε) ∫_Q |∇v|²`.
* `Lower.log_lam_ge`: the chart factor `π log λ(x_i) ≥ (π/2)(log m̄ + log(4π κ²)) - (π/2) δ/m₋`.
-/

open MeasureTheory Set Filter Topology Laplacian
open scoped ContDiff Classical ENNReal Pointwise

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem ball_subset_sqAt_of_mem_shrink {a z : ℂ} {t : ℝ} (hz : z ∈ sqShrink a t (1 / 4)) {x : ℂ}
    (hx : ‖x - z‖ < 1 / 4) : x ∈ sqAt a t := by
  have e1 : |(x - z).re| ≤ 1 / 4 := (Complex.abs_re_le_norm _).trans hx.le
  have e2 : |(x - z).im| ≤ 1 / 4 := (Complex.abs_im_le_norm _).trans hx.le
  rw [abs_le, Complex.sub_re] at e1
  rw [abs_le, Complex.sub_im] at e2
  rw [mem_sqShrink] at hz
  rw [mem_sqAt]
  obtain ⟨c1, c2, c3, c4⟩ := hz
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem integral_truncLog_density_sub_le {n : ℕ} {a z : ℂ} {t : ℝ} {mb δ : ℝ} (hmb : 0 ≤ mb) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ∈ sqAt a t, |blowupDens n x - mb| ≤ δ) :
    (∫ x, truncLog (1 / 4) (x - z) * blowupDens n x) - mb * ∫ x in sqAt a t, truncLog (1 / 4) (x - z) ≤
      Real.pi / 32 * δ + (if z ∈ sqShrink a t (1 / 4) then 0 else Real.pi / 32 * mPlus) := by
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  set f : ℂ → ℝ := fun x => truncLog (1 / 4) (x - z) with hf
  have hfint : Integrable f := (Screening.integrable_truncLog hη).comp_sub_right z
  have hfm : ∫ x, f x = Real.pi / 32 := by
    rw [hf]; simp only; rw [Screening.integral_truncLog_sub hη z]; ring
  have hf0 : ∀ x, 0 ≤ f x := fun x => Screening.truncLog_nonneg _ _
  have hfz : ∀ x, 1 / 4 ≤ ‖x - z‖ → f x = 0 := fun x hx => Screening.truncLog_eq_zero hη hx
  have hm := measurable_blowupDens n
  have hmI : Integrable fun x => f x * blowupDens n x :=
    hfint.mul_bdd (c := mPlus) hm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (blowupDens_nonneg n x)]; exact blowupDens_le n x)
  have hfQ : IntegrableOn f (sqAt a t) := hfint.integrableOn
  have hmQ : IntegrableOn (fun x => f x * blowupDens n x) (sqAt a t) := hmI.integrableOn
  have hQm := measurableSet_sqAt a t
  have hnn : 0 ≤ mb * ∫ x in sqAt a t, f x := mul_nonneg hmb (setIntegral_nonneg hQm fun x _ => hf0 x)
  by_cases hz : z ∈ sqShrink a t (1 / 4)
  · rw [ite_eq_left hz, add_zero]
    have hout : ∀ x, x ∉ sqAt a t → f x = 0 := fun x hx =>
      hfz x (not_lt.1 fun h => hx (ball_subset_sqAt_of_mem_shrink hz h))
    have e1 : ∫ x, f x * blowupDens n x = ∫ x in sqAt a t, f x * blowupDens n x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hout x hx, zero_mul]).symm
    have e2 : ∫ x in sqAt a t, f x = Real.pi / 32 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout, hfm]
    show (∫ x, f x * blowupDens n x) - mb * ∫ x in sqAt a t, f x ≤ _
    rw [e1, ← integral_const_mul, ← integral_sub hmQ (hfQ.const_mul mb)]
    have hle : ∫ x in sqAt a t, (f x * blowupDens n x - mb * f x) ≤ ∫ x in sqAt a t, δ * f x := by
      refine setIntegral_mono_on (hmQ.sub (hfQ.const_mul mb)) (hfQ.const_mul δ) hQm fun x hx => ?_
      have := hδ x hx
      rw [abs_le] at this
      nlinarith [hf0 x]
    rw [integral_const_mul, e2] at hle
    linarith
  · rw [ite_eq_right hz]
    have h1 : ∫ x, f x * blowupDens n x ≤ ∫ x, f x * mPlus :=
      integral_mono hmI (hfint.mul_const _) fun x => mul_le_mul_of_nonneg_left (blowupDens_le n x) (hf0 x)
    rw [integral_mul_const, hfm] at h1
    show (∫ x, f x * blowupDens n x) - mb * ∫ x in sqAt a t, f x ≤ _
    nlinarith [mPlus_pos, Real.pi_pos, mul_nonneg Real.pi_pos.le hδ0]

/-- The `1/2`-neighborhood of the boundary layer `Q ∖ Q^{1/4}` has area at most `5 t`. -/
theorem volume_boundary_nbhd' (a : ℂ) {t : ℝ} (ht : 2 ≤ t) :
    volume (((sqAt a t \ sqShrink a t (1 / 4)) + Metric.ball (0 : ℂ) (1 / 2))) ≤ ENNReal.ofReal (5 * t) := by
  have hsub : ((sqAt a t \ sqShrink a t (1 / 4)) + Metric.ball (0 : ℂ) (1 / 2)) ⊆
      sqAt (a - ⟨1 / 2, 1 / 2⟩) (t + 1) \ sqShrink a t (3 / 4) := by
    intro w hw
    obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_add.1 hw
    have hb' : ‖b‖ < 1 / 2 := by simpa using hb
    have hbr : |b.re| ≤ 1 / 2 := (Complex.abs_re_le_norm b).trans hb'.le
    have hbi : |b.im| ≤ 1 / 2 := (Complex.abs_im_le_norm b).trans hb'.le
    rw [abs_le] at hbr hbi
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_sqAt] at hp1
    rw [mem_sqShrink] at hp2
    constructor
    · rw [mem_sqAt]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro hq
      rw [mem_sqShrink] at hq
      simp only [Complex.add_re, Complex.add_im] at hq
      apply hp2
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine (measure_mono hsub).trans ?_
  have hT : sqShrink a t (3 / 4) ⊆ sqAt (a - ⟨1 / 2, 1 / 2⟩) (t + 1) := by
    intro z hz
    rw [mem_sqShrink] at hz
    rw [mem_sqAt]
    simp only [Complex.sub_re, Complex.sub_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [← ofReal_measureReal (ne_top_of_le_ne_top (volume_sqAt_ne_top (a - ⟨1 / 2, 1 / 2⟩) (t + 1))
    (measure_mono Set.sdiff_subset))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [measureReal_sdiff hT (measurableSet_sqShrink _ _ _) (volume_sqAt_ne_top _ _),
    volume_real_sqAt _ (by linarith)]
  have h0 : 0 ≤ volume.real (sqShrink a t (3 / 4)) := measureReal_nonneg
  unfold sqShrink
  rw [volume_real_sqAt _ (by linarith)]
  nlinarith

/-- At most `7 t` points of a `1`-separated finite set `S ⊆ Q` lie in `Q ∖ Q^{1/4}`. -/
theorem card_filter_not_shrink_le {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) (a : ℂ)
    {t : ℝ} (ht : 2 ≤ t) :
    ((S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4))).card : ℝ) ≤ 7 * t := by
  have h2 := card_filter_mul_le_volume hS (sqAt a t \ sqShrink a t (1 / 4))
  have h3 := h2.trans (volume_boundary_nbhd' a ht)
  have h4 : (((S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4))).card : ℝ)) * (Real.pi / 4) ≤ 5 * t := by
    have h5 : ENNReal.ofReal (((S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4))).card : ℝ) * (Real.pi / 4)) ≤
        ENNReal.ofReal (5 * t) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      convert h3
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h5
  have hpi := Real.pi_gt_three
  have hc0 : (0 : ℝ) ≤ (S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4))).card := Nat.cast_nonneg _
  nlinarith

theorem sq_norm_sub_le (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖x - y‖ ^ 2 ≤ (1 + ε) * ‖x‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by
  have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have h2 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have h3 : 2 * ‖x‖ * ‖y‖ ≤ ε * ‖x‖ ^ 2 + 1 / ε * ‖y‖ ^ 2 := by
    rw [← sub_nonneg]
    have e : ε * ‖x‖ ^ 2 + 1 / ε * ‖y‖ ^ 2 - 2 * ‖x‖ * ‖y‖ = (ε * ‖x‖ - ‖y‖) ^ 2 / ε := by
      field_simp; ring
    rw [e]; positivity
  have h4 := pow_le_pow_left₀ h2 h1 2
  nlinarith [h4]

theorem gradC_sub_of_differentiableAt {u v : ℂ → ℝ} {x : ℂ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) : gradC (fun y => u y - v y) x = gradC u x - gradC v x := by
  unfold gradC
  rw [fderiv_fun_sub hu hv]
  simp only [sub_apply]
  push_cast
  ring

theorem ae_differentiableAt_of_locallyLipschitz {u : ℂ → ℝ} (hu : LocallyLipschitz u) :
    ∀ᵐ x ∂(volume : Measure ℂ), DifferentiableAt ℝ u x := by
  have h1 : ∀ k : ℕ, ∀ᵐ x ∂(volume : Measure ℂ), x ∈ Metric.ball (0 : ℂ) k → DifferentiableAt ℝ u x := by
    intro k
    obtain ⟨K, hK⟩ := (hu.locallyLipschitzOn (s := Metric.closedBall (0 : ℂ) k)).exists_lipschitzOnWith_of_compact
      (isCompact_closedBall _ _)
    filter_upwards [hK.ae_differentiableWithinAt_of_mem] with x hx hxb
    exact (hx (Metric.ball_subset_closedBall hxb)).differentiableAt
      (Metric.closedBall_mem_nhds_of_mem hxb)
  rw [← ae_all_iff] at h1
  filter_upwards [h1] with x hx
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  exact hx k (by simpa using hk)

theorem integral_norm_gradC_sub_le {u v : ℂ → ℝ} (hu : LocallyLipschitz u) (hv : ContDiff ℝ ∞ v) {a : ℂ}
    {t : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∫ x in sqAt a t, ‖gradC (fun y => u y - v y) x‖ ^ 2 ≤
      (1 + ε) * (∫ x in sqAt a t, ‖gradC u x‖ ^ 2) + (1 + 1 / ε) * ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 := by
  have hQc := isCompact_sqAt a t
  have hQm := measurableSet_sqAt a t
  have hv1 : LocallyLipschitz v := ((hv.of_le (by norm_cast)).locallyLipschitz)
  have hw := hasWeakGradientOn_of_locallyLipschitz hu hQc
  have hwv := hasWeakGradientOn_of_locallyLipschitz hv1 hQc
  have hwd := hasWeakGradientOn_of_locallyLipschitz (hu.sub hv1) hQc
  have i1 : Integrable (fun x => ‖gradC u x‖ ^ 2) (volume.restrict (sqAt a t)) := hw.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have i2 : Integrable (fun x => ‖gradC v x‖ ^ 2) (volume.restrict (sqAt a t)) := hwv.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have i3 : Integrable (fun x => ‖gradC (fun y => u y - v y) x‖ ^ 2) (volume.restrict (sqAt a t)) :=
    hwd.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have e : (1 + ε) * (∫ x in sqAt a t, ‖gradC u x‖ ^ 2) + (1 + 1 / ε) * ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 =
      ∫ x in sqAt a t, ((1 + ε) * ‖gradC u x‖ ^ 2 + (1 + 1 / ε) * ‖gradC v x‖ ^ 2) := by
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  rw [e]
  refine integral_mono_ae i3 ((i1.const_mul _).add (i2.const_mul _)) ?_
  have hae : ∀ᵐ x ∂(volume : Measure ℂ), DifferentiableAt ℝ u x := ae_differentiableAt_of_locallyLipschitz hu
  filter_upwards [(ae_restrict_iff' hQm).2 (hae.mono fun x hx _ => hx)] with x hx
  rw [gradC_sub_of_differentiableAt hx (hv.differentiable (by simp) x)]
  exact sq_norm_sub_le _ _ hε

/-- The chart factor: `π log λ(x_i) ≥ (π/2)(log m̄ + log (4 π κ²)) - (π/2) δ / m₋` for `s x_i ∈ Q`. -/
theorem pi_log_lam_ge {n : ℕ} (hn : 0 < n) (x : ℂ) {mb δ : ℝ} (hmb : mMinus ≤ mb)
    (hx : ‖blowupScale n • x‖ ≤ 2 * blowupScale n)
    (hδ : |blowupDens n (blowupScale n • x) - mb| ≤ δ) :
    Real.pi / 2 * (Real.log mb + Real.log (4 * Real.pi * blowupKappa ^ 2)) - Real.pi / 2 * (δ / mMinus) ≤
      Real.pi * Real.log (lam x) := by
  have hs := blowupScale_pos hn
  have hk := blowupKappa_pos
  have hp := Real.pi_pos
  have hdens : blowupDens n (blowupScale n • x) = lam x ^ 2 / (4 * Real.pi * blowupKappa ^ 2) := by
    unfold blowupDens
    rw [inv_smul_smul₀ hs.ne']
  have hlam := lam_pos x
  have hmx := (blowupDens_mem_Icc hn hx).1
  have hlog : Real.log (blowupDens n (blowupScale n • x)) =
      2 * Real.log (lam x) - Real.log (4 * Real.pi * blowupKappa ^ 2) := by
    rw [hdens, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hd := abs_log_sub_log_le mMinus_pos hmx hmb
  have hd2 := (abs_le.1 hd).1
  have hd3 : |blowupDens n (blowupScale n • x) - mb| / mMinus ≤ δ / mMinus :=
    div_le_div_of_nonneg_right hδ mMinus_pos.le
  have hd4 : Real.log mb - Real.log (blowupDens n (blowupScale n • x)) ≤ δ / mMinus := by
    have := (abs_le.1 hd).2
    have h5 : |blowupDens n (blowupScale n • x) - mb| = |mb - blowupDens n (blowupScale n • x)| := abs_sub_comm _ _
    have := abs_log_sub_log_le mMinus_pos hmb hmx
    have h6 := (abs_le.1 this).2
    rw [abs_sub_comm] at hd3
    linarith [div_le_div_of_nonneg_right (le_of_eq h5.symm) mMinus_pos.le]
  nlinarith

end Lower

end Sphere

end SandierSerfaty

end
