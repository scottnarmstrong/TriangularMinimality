/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PeriodicGreen
public import SandierSerfaty.Analysis.PolarDivergence
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The circle term at a logarithmic puncture

If `u = s - log ‖· - p‖` near `p` with `s` of class `C¹` at `p`, then the circle term
`circleTerm u p η = ∫_{-π}^{π} η · u · ∂_r u (p + η e^{iθ}) dθ` satisfies
`circleTerm u p η - 2π log η → -2π s(p)` as `η → 0+`
(`SandierSerfaty.Analysis.tendsto_circleTerm_sub_log`).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Analysis

/-- `∫_{-π}^{π} η · u · ∂_r u` on the circle of radius `η` about `p`. -/
@[expose] noncomputable def circleTerm (u : ℂ → ℝ) (p : ℂ) (η : ℝ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi,
    η * (u (p + polarPt η θ) *
      (Real.cos θ * pd₁ u (p + polarPt η θ) + Real.sin θ * pd₂ u (p + polarPt η θ)))

/-- The radial combination `cos θ ∂₁ + sin θ ∂₂`. -/
@[expose] noncomputable def radialPd (f : ℂ → ℝ) (x : ℂ) (θ : ℝ) : ℝ :=
  Real.cos θ * pd₁ f x + Real.sin θ * pd₂ f x

theorem radialPd_eq (f : ℂ → ℝ) (x : ℂ) (θ : ℝ) :
    radialPd f x θ = fderiv ℝ f x ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
  rw [fderiv_polar_dir]; rfl

/-- The radial derivative of `u` on a small circle, from the local form `u = s - log`. -/
theorem radialPd_eq_of_localForm {u s : ℂ → ℝ} {p : ℂ} {r θ : ℝ} (hr : 0 < r)
    (hu : DifferentiableAt ℝ u (p + polarPt r θ)) (hs : DifferentiableAt ℝ s (p + polarPt r θ))
    (hloc : ∀ᶠ x in 𝓝 (p + polarPt r θ), u x = s x - Real.log ‖x - p‖) :
    radialPd u (p + polarPt r θ) θ = radialPd s (p + polarPt r θ) θ - r⁻¹ := by
  -- shift the centre to `0`
  set ut : ℂ → ℝ := fun y => u (p + y) with hut
  set st : ℂ → ℝ := fun y => s (p + y) with hst
  have hdu : DifferentiableAt ℝ ut (polarPt r θ) :=
    hu.comp (polarPt r θ) (differentiableAt_const p |>.add differentiableAt_id)
  have hds : DifferentiableAt ℝ st (polarPt r θ) :=
    hs.comp (polarPt r θ) (differentiableAt_const p |>.add differentiableAt_id)
  have h1 := hasDerivAt_comp_polarPt_r (θ := θ) hdu
  have h2 := hasDerivAt_comp_polarPt_r (θ := θ) hds
  have h3 : HasDerivAt (fun r' : ℝ => Real.log r') r⁻¹ r := Real.hasDerivAt_log hr.ne'
  have h4 := h2.sub h3
  -- `ut (polarPt r' θ) = st (polarPt r' θ) - log r'` for `r'` near `r`
  have hcont : ContinuousAt (fun r' : ℝ => p + polarPt r' θ) r :=
    (continuous_const.add (continuous_polarPt.comp (continuous_id.prodMk continuous_const))).continuousAt
  have hev : ∀ᶠ r' in 𝓝 r, ut (polarPt r' θ) = st (polarPt r' θ) - Real.log r' := by
    filter_upwards [hcont.eventually hloc, eventually_gt_nhds hr] with r' h' hr'
    simp only [hut, hst]
    rw [h', add_sub_cancel_left, norm_polarPt hr'.le]
  have h5 : HasDerivAt (fun r' : ℝ => ut (polarPt r' θ)) _ r := h4.congr_of_eventuallyEq
    (hev.mono fun r' h => h)
  have h6 := h1.unique h5
  simp only [radialPd, hut, hst] at h6 ⊢
  simp only [pd₁, pd₂] at h6 ⊢
  rw [fderiv_comp_add_left, fderiv_comp_add_left] at h6
  linarith


theorem abs_radialPd_le (f : ℂ → ℝ) (x : ℂ) (θ : ℝ) : |radialPd f x θ| ≤ ‖fderiv ℝ f x‖ := by
  rw [radialPd_eq]
  have hn : ‖(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I‖ = 1 := by
    simp
  calc |fderiv ℝ f x ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)|
      = ‖fderiv ℝ f x ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ f x‖ * ‖(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I‖ :=
        (fderiv ℝ f x).le_opNorm _
    _ = ‖fderiv ℝ f x‖ := by rw [hn, mul_one]

/-- A good ball around `p`: `s` is `C¹` with bounded data, and `u = s - log` off `p`. -/
theorem exists_good_ball {u s : ℂ → ℝ} {p : ℂ} (hs : ContDiffAt ℝ 1 s p)
    (hloc : ∀ᶠ x in 𝓝[≠] p, u x = s x - Real.log ‖x - p‖)
    (hdu : ∀ᶠ x in 𝓝[≠] p, DifferentiableAt ℝ u x) :
    ∃ r > 0, ∃ M M' : ℝ, 0 ≤ M ∧ 0 ≤ M' ∧ ∀ x ∈ ball p r, ContDiffAt ℝ 1 s x ∧ |s x| ≤ M ∧ ‖fderiv ℝ s x‖ ≤ M' ∧
      (x ≠ p → u x = s x - Real.log ‖x - p‖ ∧ DifferentiableAt ℝ u x) := by
  have h1 : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 1 s x := hs.eventually (by simp)
  have hc : ContinuousAt s p := hs.continuousAt
  have h2 : ∀ᶠ x in 𝓝 p, |s x| < |s p| + 1 :=
    hc.abs.eventually (eventually_lt_nhds (by linarith : |s p| < |s p| + 1))
  have hd : ContinuousAt (fderiv ℝ s) p := (hs.fderiv_right (m := 0) (by norm_num)).continuousAt
  have h3 : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ s x‖ < ‖fderiv ℝ s p‖ + 1 :=
    hd.norm.eventually (eventually_lt_nhds (by linarith : ‖fderiv ℝ s p‖ < ‖fderiv ℝ s p‖ + 1))
  have h4 : ∀ᶠ x in 𝓝 p, x ≠ p → u x = s x - Real.log ‖x - p‖ ∧ DifferentiableAt ℝ u x := by
    have := hloc.and hdu
    rw [eventually_nhdsWithin_iff] at this
    exact this
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 ((h1.and (h2.and h3)).and h4)
  exact ⟨r, hr, |s p| + 1, ‖fderiv ℝ s p‖ + 1, by positivity, by positivity, fun x hx =>
    ⟨(hball x hx).1.1, (hball x hx).1.2.1.le, (hball x hx).1.2.2.le, (hball x hx).2⟩⟩


theorem tendsto_circleTerm_sub_log {u s : ℂ → ℝ} {p : ℂ} (hs : ContDiffAt ℝ 1 s p)
    (hloc : ∀ᶠ x in 𝓝[≠] p, u x = s x - Real.log ‖x - p‖)
    (hdu : ∀ᶠ x in 𝓝[≠] p, DifferentiableAt ℝ u x) :
    Tendsto (fun η => circleTerm u p η - 2 * Real.pi * Real.log η) (𝓝[>] 0)
      (𝓝 (-(2 * Real.pi) * s p)) := by
  obtain ⟨r, hr, M, M', hM, hM', hgood⟩ := exists_good_ball hs hloc hdu
  -- the circle points
  have hpt : ∀ η θ : ℝ, 0 < η → η < r → p + polarPt η θ ∈ ball p r ∧ p + polarPt η θ ≠ p := by
    intro η θ hη hηr
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_polarPt hη.le]; exact hηr
    · intro h
      have : polarPt η θ = 0 := by simpa using h
      exact polarPt_ne_zero hη θ this
  have hcircle : ∀ η θ : ℝ, 0 < η → η < r →
      u (p + polarPt η θ) = s (p + polarPt η θ) - Real.log η := by
    intro η θ hη hηr
    obtain ⟨hb, hne⟩ := hpt η θ hη hηr
    rw [((hgood _ hb).2.2.2 hne).1, add_sub_cancel_left, norm_polarPt hη.le]
  have hrad : ∀ η θ : ℝ, 0 < η → η < r →
      radialPd u (p + polarPt η θ) θ = radialPd s (p + polarPt η θ) θ - η⁻¹ := by
    intro η θ hη hηr
    obtain ⟨hb, hne⟩ := hpt η θ hη hηr
    refine radialPd_eq_of_localForm hη ((hgood _ hb).2.2.2 hne).2
      ((hgood _ hb).1.differentiableAt one_ne_zero) ?_
    have hopen : IsOpen (ball p r ∩ {p}ᶜ) := isOpen_ball.inter isClosed_singleton.isOpen_compl
    filter_upwards [hopen.mem_nhds ⟨hb, hne⟩] with x hx
    exact ((hgood x hx.1).2.2.2 hx.2).1
  -- continuity in `θ` of the pieces
  have hpc : ∀ η : ℝ, Continuous fun θ : ℝ => p + polarPt η θ := fun η =>
    continuous_const.add (continuous_polarPt.comp (continuous_const.prodMk continuous_id))
  have hcont_s : ∀ η : ℝ, 0 < η → η < r → Continuous fun θ => s (p + polarPt η θ) := by
    intro η hη hηr
    refine continuous_iff_continuousAt.2 fun θ => ?_
    exact ContinuousAt.comp (g := s) (f := fun θ : ℝ => p + polarPt η θ)
      ((hgood _ (hpt η θ hη hηr).1).1.continuousAt) (hpc η).continuousAt
  have hcont_σ : ∀ η : ℝ, 0 < η → η < r →
      Continuous fun θ => radialPd s (p + polarPt η θ) θ := by
    intro η hη hηr
    refine continuous_iff_continuousAt.2 fun θ => ?_
    have hd1 : ContinuousAt (fun x => fderiv ℝ s x 1) (p + polarPt η θ) :=
      continuousAt_fderiv_apply (hgood _ (hpt η θ hη hηr).1).1 1
    have hd2 : ContinuousAt (fun x => fderiv ℝ s x Complex.I) (p + polarPt η θ) :=
      continuousAt_fderiv_apply (hgood _ (hpt η θ hη hηr).1).1 Complex.I
    have e1 := ContinuousAt.comp (g := fun x => fderiv ℝ s x 1) (f := fun θ : ℝ => p + polarPt η θ) hd1 (hpc η).continuousAt
    have e2 := ContinuousAt.comp (g := fun x => fderiv ℝ s x Complex.I) (f := fun θ : ℝ => p + polarPt η θ) hd2 (hpc η).continuousAt
    unfold radialPd pd₁ pd₂
    exact (Real.continuous_cos.continuousAt.mul e1).add (Real.continuous_sin.continuousAt.mul e2)
  -- the exact formula for the circle term on small circles
  set F : ℝ → ℝ → ℝ := fun η θ =>
    -(s (p + polarPt η θ)) + η * radialPd s (p + polarPt η θ) θ *
      (s (p + polarPt η θ) - Real.log η) with hF
  have hexp : ∀ η : ℝ, 0 < η → η < r →
      circleTerm u p η - 2 * Real.pi * Real.log η = ∫ θ in (-Real.pi)..Real.pi, F η θ := by
    intro η hη hηr
    have hG : ∀ θ ∈ Set.uIcc (-Real.pi) Real.pi,
        η * (u (p + polarPt η θ) * (Real.cos θ * pd₁ u (p + polarPt η θ) +
          Real.sin θ * pd₂ u (p + polarPt η θ))) =
        (s (p + polarPt η θ) - Real.log η) * (η * radialPd s (p + polarPt η θ) θ - 1) := by
      intro θ _
      have h1 := hrad η θ hη hηr
      have h2 := hcircle η θ hη hηr
      have h3 : Real.cos θ * pd₁ u (p + polarPt η θ) + Real.sin θ * pd₂ u (p + polarPt η θ) =
          radialPd u (p + polarPt η θ) θ := rfl
      rw [h3, h1, h2]
      field_simp
    have hcts : Continuous fun θ => (s (p + polarPt η θ) - Real.log η) *
        (η * radialPd s (p + polarPt η θ) θ - 1) :=
      ((hcont_s η hη hηr).sub continuous_const).mul
        ((continuous_const.mul (hcont_σ η hη hηr)).sub continuous_const)
    unfold circleTerm
    rw [intervalIntegral.integral_congr hG]
    have hL : (2 * Real.pi * Real.log η) = ∫ _θ in (-Real.pi)..Real.pi, Real.log η := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hL, ← intervalIntegral.integral_sub (hcts.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [hF]
    ring
  -- dominated convergence
  have hlog : Tendsto (fun η : ℝ => η * Real.log η) (𝓝[>] 0) (𝓝 0) := by
    have := Real.continuous_mul_log.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), |η * Real.log η| < 1 / (M' + 1) := by
    have h0 : Tendsto (fun η : ℝ => |η * Real.log η|) (𝓝[>] 0) (𝓝 0) := by simpa using hlog.abs
    exact h0.eventually_lt_const (by positivity)
  have hFcont : ∀ η : ℝ, 0 < η → η < r → Continuous (F η) := by
    intro η hη hηr
    have := ((hcont_s η hη hηr).neg).add
      ((((continuous_const (y := η)).mul (hcont_σ η hη hηr))).mul
        ((hcont_s η hη hηr).sub (continuous_const (y := Real.log η))))
    exact this
  have hsmall2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < 1 / (M * M' + 1) :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (M * M' + 1))).filter_mono nhdsWithin_le_nhds
  have hFbound : ∀ η : ℝ, 0 < η → η < r → η < 1 / (M * M' + 1) → |η * Real.log η| < 1 / (M' + 1) →
      ∀ θ, ‖F η θ‖ ≤ M + 2 := by
    intro η hη hηr hη2 hη3 θ
    obtain ⟨hb, hne⟩ := hpt η θ hη hηr
    have hg := hgood _ hb
    have h1 : |s (p + polarPt η θ)| ≤ M := hg.2.1
    have h2 : |radialPd s (p + polarPt η θ) θ| ≤ M' := (abs_radialPd_le _ _ _).trans hg.2.2.1
    have hη' : η * (M * M') ≤ 1 := by
      have : η * (M * M' + 1) < 1 := by
        have := mul_lt_mul_of_pos_right hη2 (by positivity : (0 : ℝ) < M * M' + 1)
        rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
      nlinarith [mul_nonneg hM hM', hη]
    have h3 : M' * |η * Real.log η| ≤ 1 := by
      have : |η * Real.log η| * (M' + 1) < 1 := by
        have := mul_lt_mul_of_pos_right hη3 (by positivity : (0 : ℝ) < M' + 1)
        rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
      nlinarith [abs_nonneg (η * Real.log η)]
    simp only [hF, Real.norm_eq_abs]
    calc |-(s (p + polarPt η θ)) + η * radialPd s (p + polarPt η θ) θ *
          (s (p + polarPt η θ) - Real.log η)|
        ≤ |s (p + polarPt η θ)| + |η * radialPd s (p + polarPt η θ) θ *
          (s (p + polarPt η θ) - Real.log η)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg]
      _ ≤ M + (|η| * |radialPd s (p + polarPt η θ) θ| * (|s (p + polarPt η θ)| + |Real.log η|)) := by
          refine add_le_add h1 ?_
          rw [abs_mul, abs_mul]
          gcongr
          exact abs_sub _ _
      _ ≤ M + (η * M' * (M + |Real.log η|)) := by
          rw [abs_of_pos hη]
          gcongr
      _ = M + (η * (M * M') + M' * |η * Real.log η|) := by
          rw [abs_mul, abs_of_pos hη]; ring
      _ ≤ M + 2 := by linarith
  have hlimF : Tendsto (fun η => ∫ θ in (-Real.pi)..Real.pi, F η θ) (𝓝[>] 0)
      (𝓝 (∫ _θ in (-Real.pi)..Real.pi, -(s p))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M + 2) ?_ ?_
      (continuous_const.intervalIntegrable _ _) ?_
    · filter_upwards [Ioo_mem_nhdsGT hr] with η hη
      exact (hFcont η hη.1 hη.2).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hr, hsmall2, hsmall] with η hη h2 h3
      exact Filter.Eventually.of_forall fun θ _ => hFbound η hη.1 hη.2 h2 h3 θ
    · refine Filter.Eventually.of_forall fun θ _ => ?_
      -- pointwise limit
      have hpc0 : Tendsto (fun η : ℝ => p + polarPt η θ) (𝓝[>] 0) (𝓝 p) := by
        have : Continuous fun η : ℝ => p + polarPt η θ :=
          continuous_const.add (continuous_polarPt.comp (continuous_id.prodMk continuous_const))
        have h := this.tendsto 0
        simp only [polarPt, Complex.ofReal_zero, zero_mul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hs_lim : Tendsto (fun η : ℝ => s (p + polarPt η θ)) (𝓝[>] 0) (𝓝 (s p)) :=
        hs.continuousAt.tendsto.comp hpc0
      have h2 : Tendsto (fun η : ℝ => η * radialPd s (p + polarPt η θ) θ *
          (s (p + polarPt η θ) - Real.log η)) (𝓝[>] 0) (𝓝 0) := by
        refine squeeze_zero_norm' (a := fun η : ℝ => M' * (η * M + |η * Real.log η|)) ?_ ?_
        · filter_upwards [Ioo_mem_nhdsGT hr] with η hη
          obtain ⟨hb, hne⟩ := hpt η θ hη.1 hη.2
          have hg := hgood _ hb
          have h1 : |s (p + polarPt η θ)| ≤ M := hg.2.1
          have h2 : |radialPd s (p + polarPt η θ) θ| ≤ M' := (abs_radialPd_le _ _ _).trans hg.2.2.1
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hη.1]
          calc η * |radialPd s (p + polarPt η θ) θ| * |s (p + polarPt η θ) - Real.log η|
              ≤ η * M' * (M + |Real.log η|) := by
                have hh : |s (p + polarPt η θ) - Real.log η| ≤ M + |Real.log η| :=
                  (abs_sub _ _).trans (add_le_add h1 le_rfl)
                have h2' : η * |radialPd s (p + polarPt η θ) θ| ≤ η * M' :=
                  mul_le_mul_of_nonneg_left h2 hη.1.le
                exact mul_le_mul h2' hh (abs_nonneg _) (by have := hη.1; positivity)
            _ = M' * (η * M + |η * Real.log η|) := by
                rw [abs_mul, abs_of_pos hη.1]; ring
        · have h0 : Tendsto (fun η : ℝ => |η * Real.log η|) (𝓝[>] 0) (𝓝 0) := by
            simpa using hlog.abs
          have h1 : Tendsto (fun η : ℝ => η * M) (𝓝[>] 0) (𝓝 0) := by
            have hc : Continuous fun η : ℝ => η * M := continuous_id.mul continuous_const
            have := hc.tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          simpa using (h1.add h0).const_mul M'
      have := (hs_lim.neg).add h2
      simpa [hF] using this
  have hval : ∫ _θ in (-Real.pi)..Real.pi, -(s p) = -(2 * Real.pi) * s p := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hval] at hlimF
  refine hlimF.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with η hη
  exact (hexp η hη.1 hη.2).symm

end Analysis

end SandierSerfaty

end
