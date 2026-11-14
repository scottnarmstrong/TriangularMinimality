/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.RadialGreen

/-!
# Truncation identity near one puncture, centre `0` (sphere note, Lemma 3.10, local step)

Let `u` be `C¹` at `0` and `C²` on `0 < ‖x‖ ≤ α` with `Δ u = 2π ϱ` there, and let `H₁ = u + f_α` on
`0 < ‖x‖ < α`, `f_α = truncLog α`.  Then, as `η ↓ 0`,
`½ ∫_{η ≤ ‖x‖ < α} |∇H₁|² + π log η → ½ ∫_{B(0,α)} |∇u|² + π log α - 2π ∫_{B(0,α)} f_α ϱ`
(`Sphere.tendsto_annulus_energy`).  The cross term `∫_{η ≤ ‖x‖ < α} ⟨∇u, ∇f_α⟩ = 2π (⨍_η u - ⨍_α u)` is
computed in polar coordinates (`Sphere.integral_cross_annulus`).
-/

open MeasureTheory Filter Topology Set SandierSerfaty.Analysis Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

variable {u : ℂ → ℝ} {α : ℝ}

theorem continuousAt_pd₁ (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {x : ℂ} (hx : ‖x‖ ≤ α) :
    ContinuousAt (pd₁ u) x ∧ ContinuousAt (pd₂ u) x := by
  by_cases h0 : x = 0
  · subst h0
    have h1 := contDiffAt_pd (n := 0) (by simpa using hu1) 1
    have h2 := contDiffAt_pd (n := 0) (by simpa using hu1) Complex.I
    exact ⟨h1.continuousAt, h2.continuousAt⟩
  · exact ⟨(contDiffAt_pd₁_le hu2 x h0 hx).continuousAt, (contDiffAt_pd₂_le hu2 x h0 hx).continuousAt⟩

theorem integrableOn_norm_gradient_sq (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) :
    IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (Metric.ball 0 α) := by
  have hc : ContinuousOn (fun x => ‖gradient u x‖ ^ 2) (Metric.closedBall 0 α) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx
    obtain ⟨c1, c2⟩ := continuousAt_pd₁ hu1 hu2 hx
    refine ContinuousAt.continuousWithinAt ?_
    simp only [norm_gradient_sq]
    exact (c1.pow 2).add (c2.pow 2)
  exact (hc.integrableOn_compact (isCompact_closedBall 0 α)).mono_set Metric.ball_subset_closedBall

theorem cross_integrand_polar {r : ℝ} {θ : ℝ}
    (hr : 0 < r) (hrα : r < α) :
    r * inner ℝ (gradient u ((r : ℂ) * Torus.dir θ)) (gradient (truncLog α) ((r : ℂ) * Torus.dir θ)) =
      -radialComp (pd₁ u) (pd₂ u) r θ := by
  have hx : (r : ℂ) * Torus.dir θ = polarPt r θ := rfl
  have hn : ‖polarPt r θ‖ = r := norm_polarPt hr.le θ
  rw [hx, Screening.gradient_truncLog_of_lt (by rw [hn]; exact hr) (by rw [hn]; exact hrα),
    real_inner_smul_right, Screening.inner_gradient_left, hn]
  have h1 : polarPt r θ = r • ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    simp only [polarPt, Complex.real_smul]
  have h2 : fderiv ℝ u (polarPt r θ) (polarPt r θ) =
      r * (Real.cos θ * pd₁ u (polarPt r θ) + Real.sin θ * pd₂ u (polarPt r θ)) := by
    conv_lhs => rw [h1]
    rw [map_smul, fderiv_polar_dir, smul_eq_mul]
    rfl
  rw [h2]
  simp only [radialComp]
  field_simp

/-- The cross term, in polar coordinates: `∫_{η ≤ ‖x‖ < α} ⟨∇u, ∇f_α⟩ = 2π (⨍_η u - ⨍_α u)`. -/
theorem integral_cross_annulus (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {η : ℝ}
    (hη : 0 < η) (hηα : η ≤ α) :
    ∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, inner ℝ (gradient u x) (gradient (truncLog α) x) =
      2 * Real.pi * (Real.circleAverage u 0 η - Real.circleAverage u 0 α) := by
  have hrc : ContinuousOn (fun p : ℝ × ℝ => radialComp (pd₁ u) (pd₂ u) p.1 p.2)
      (Icc η α ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_radialComp_le (contDiffAt_pd₁_le hu2) (contDiffAt_pd₂_le hu2)).mono
      (box_subset hη)
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * inner ℝ (gradient u ((p.1 : ℂ) * Torus.dir p.2))
      (gradient (truncLog α) ((p.1 : ℂ) * Torus.dir p.2))) (Ico η α ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have h1 : IntegrableOn (fun p : ℝ × ℝ => -radialComp (pd₁ u) (pd₂ u) p.1 p.2)
        (Ico η α ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      (hrc.neg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
    refine h1.congr_fun (fun p hp => ?_) (measurableSet_Ico.prod measurableSet_Ioo)
    exact (cross_integrand_polar (lt_of_lt_of_le hη hp.1.1) hp.1.2).symm
  have := Torus.integral_polar_radial (f := fun x : ℂ =>
      inner ℝ (gradient u x) (gradient (truncLog α) x)) measurableSet_Ico
    (fun r hr => lt_of_lt_of_le hη hr.1) hint
  rw [this]
  have hin : ∀ θ : ℝ, θ ∈ Icc (-Real.pi) Real.pi → ∫ r in Ico η α, r * inner ℝ (gradient u ((r : ℂ) * Torus.dir θ))
      (gradient (truncLog α) ((r : ℂ) * Torus.dir θ)) = u (polarPt η θ) - u (polarPt α θ) := by
    intro θ hθ
    rw [setIntegral_congr_fun measurableSet_Ico
      (fun r hr => cross_integrand_polar (lt_of_lt_of_le hη hr.1) hr.2),
      Torus.setIntegral_Ico_eq_intervalIntegral hηα, intervalIntegral.integral_neg]
    have hder : ∀ r ∈ uIcc η α, HasDerivAt (fun s : ℝ => u (polarPt s θ))
        (radialComp (pd₁ u) (pd₂ u) r θ) r := by
      intro r hr
      rw [uIcc_of_le hηα] at hr
      have hr0 : 0 < r := lt_of_lt_of_le hη hr.1
      have hd : DifferentiableAt ℝ u (polarPt r θ) :=
        (hu2 _ (polarPt_ne_zero hr0 θ) (by rw [norm_polarPt hr0.le]; exact hr.2)).differentiableAt
          (by norm_num)
      have := hasDerivAt_comp_polarPt_r hd
      refine this.congr_deriv ?_
      simp only [radialComp, pd₁, pd₂]; ring
    have hcont : ContinuousOn (fun r : ℝ => radialComp (pd₁ u) (pd₂ u) r θ) (uIcc η α) := by
      rw [uIcc_of_le hηα]
      have := hrc.comp (continuous_id.prodMk (continuous_const (y := θ))).continuousOn
        (s := Icc η α) (t := Icc η α ×ˢ Icc (-Real.pi) Real.pi) (fun r hr => ⟨hr, hθ⟩)
      exact this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hin θ (Ioo_subset_Icc_self hθ)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hcirc : ∀ r : ℝ, 0 < r → r ≤ α → Continuous fun θ => u (polarPt r θ) := by
    intro r hr0 hrα
    refine continuous_iff_continuousAt.2 fun θ => ?_
    exact ContinuousAt.comp (f := polarPt r) (g := u)
      (hu2 _ (polarPt_ne_zero hr0 θ) (by rw [norm_polarPt hr0.le]; exact hrα)).continuousAt
      (continuous_polarPt_theta r).continuousAt
  rw [intervalIntegral.integral_sub ((hcirc η hη hηα).intervalIntegrable _ _)
    ((hcirc α (hη.trans_le hηα) le_rfl).intervalIntegrable _ _),
    integral_polarPt_eq_circleAverage, integral_polarPt_eq_circleAverage]
  ring

theorem gradient_eq_complex (u : ℂ → ℝ) :
    gradient u = fun x => (pd₁ u x : ℂ) + (pd₂ u x : ℂ) * Complex.I := by
  funext x
  apply Complex.ext <;> simp [gradient_re, gradient_im]

theorem continuousOn_gradient (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) :
    ContinuousOn (gradient u) (Metric.closedBall 0 α) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  obtain ⟨c1, c2⟩ := continuousAt_pd₁ hu1 hu2 hx
  refine ContinuousAt.continuousWithinAt ?_
  rw [gradient_eq_complex]
  exact (Complex.continuous_ofReal.continuousAt.comp c1).add
    ((Complex.continuous_ofReal.continuousAt.comp c2).mul continuousAt_const)

/-- The three terms of `|∇u + ∇f_α|²` and their integrals on the annulus. -/
theorem integral_annulus_expand (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {H₁ : ℂ → ℝ} {η : ℝ} (hη : 0 < η) (hηα : η < α)
    (hH₁ : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < α → H₁ x = u x + truncLog α x) :
    ∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, ‖gradient H₁ x‖ ^ 2 =
      (∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, ‖gradient u x‖ ^ 2) +
      2 * (∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, inner ℝ (gradient u x) (gradient (truncLog α) x)) +
      ∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, (‖x‖ ^ 2)⁻¹ := by
  set S : Set ℂ := {x : ℂ | ‖x‖ ∈ Ico η α} with hS
  have hSm : MeasurableSet S := measurable_norm measurableSet_Ico
  have hα : 0 < α := hη.trans hηα
  have hSx : ∀ x ∈ S, 0 < ‖x‖ ∧ ‖x‖ < α := fun x hx => ⟨lt_of_lt_of_le hη hx.1, hx.2⟩
  -- the compact closed annulus
  set K : Set ℂ := {x : ℂ | η ≤ ‖x‖ ∧ ‖x‖ ≤ α} with hK
  have hKc : IsCompact K := by
    have : K = Metric.closedBall 0 α ∩ {x : ℂ | η ≤ ‖x‖} := by
      ext x; simp [hK, and_comm]
    rw [this]
    exact (isCompact_closedBall 0 α).inter_right (isClosed_le continuous_const continuous_norm)
  have hSK : S ⊆ K := fun x hx => ⟨hx.1, hx.2.le⟩
  have hKball : K ⊆ Metric.closedBall 0 α := fun x hx => by
    rw [mem_closedBall_zero_iff]; exact hx.2
  have hKne : ∀ x ∈ K, x ≠ 0 := fun x hx h => by
    have := hx.1; rw [h, norm_zero] at this; linarith
  have hgrad := continuousOn_gradient hu1 hu2
  -- model functions
  have hinv : ContinuousOn (fun x : ℂ => (‖x‖ ^ 2)⁻¹) K :=
    ((continuous_norm.pow 2).continuousOn).inv₀
      (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.2 (hKne x hx)))
  have hA2 : ContinuousOn (fun x : ℂ => inner ℝ (gradient u x) (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)) K :=
    (hgrad.mono hKball).inner (hinv.neg.smul continuous_id.continuousOn)
  have hA3 : ContinuousOn (fun x : ℂ => (‖x‖ ^ 2)⁻¹) K := hinv
  have hA1 : ContinuousOn (fun x : ℂ => ‖gradient u x‖ ^ 2) K :=
    ((hgrad.mono hKball).norm).pow 2
  have iA1 : IntegrableOn (fun x : ℂ => ‖gradient u x‖ ^ 2) S :=
    (hA1.integrableOn_compact hKc).mono_set hSK
  have iA2 : IntegrableOn (fun x : ℂ => inner ℝ (gradient u x) (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)) S :=
    (hA2.integrableOn_compact hKc).mono_set hSK
  have iA3 : IntegrableOn (fun x : ℂ => (‖x‖ ^ 2)⁻¹) S :=
    (hA3.integrableOn_compact hKc).mono_set hSK
  -- gradient of `truncLog` on `S`
  have hgf : ∀ x ∈ S, gradient (truncLog α) x = -((‖x‖ ^ 2)⁻¹ : ℝ) • x := fun x hx =>
    Screening.gradient_truncLog_of_lt (hSx x hx).1 (hSx x hx).2
  have hpt : ∀ x ∈ S, ‖gradient H₁ x‖ ^ 2 = ‖gradient u x‖ ^ 2 +
      2 * inner ℝ (gradient u x) (-((‖x‖ ^ 2)⁻¹ : ℝ) • x) + (‖x‖ ^ 2)⁻¹ := by
    intro x hx
    obtain ⟨h0, hα'⟩ := hSx x hx
    have hev : H₁ =ᶠ[𝓝 x] fun z => u z + truncLog α z := by
      have hopen : IsOpen {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < α} :=
        (isOpen_lt (continuous_const : Continuous fun _ : ℂ => (0 : ℝ)) continuous_norm).inter
          (isOpen_lt continuous_norm (continuous_const : Continuous fun _ : ℂ => α))
      filter_upwards [hopen.mem_nhds (show x ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < α} from ⟨h0, hα'⟩)] with z hz
      exact hH₁ z hz.1 hz.2
    have hdu : DifferentiableAt ℝ u x :=
      (hu2 x (norm_pos_iff.1 h0) hα'.le).differentiableAt (by norm_num)
    have hdf : DifferentiableAt ℝ (truncLog α) x :=
      (Screening.hasFDerivAt_truncLog_of_lt h0 hα').differentiableAt
    have hg : gradient H₁ x = gradient u x + gradient (truncLog α) x := by
      simp only [gradient, hev.fderiv_eq, fderiv_fun_add hdu hdf, map_add]
    rw [hg, hgf x hx, norm_add_sq_real, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
    have hn : (0 : ℝ) < ‖x‖ := h0
    field_simp
  have iA12 : IntegrableOn (fun x : ℂ => ‖gradient u x‖ ^ 2 +
      2 * inner ℝ (gradient u x) (-((‖x‖ ^ 2)⁻¹ : ℝ) • x)) S := iA1.add (iA2.const_mul 2)
  rw [setIntegral_congr_fun hSm hpt, integral_add iA12 iA3, integral_add iA1 (iA2.const_mul 2),
    integral_const_mul]
  congr 3
  exact setIntegral_congr_fun hSm fun x hx => by rw [hgf x hx]

theorem integral_inv_sq_Ico {η : ℝ} (hη : 0 < η) (hηα : η < α) :
    ∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, (‖x‖ ^ 2)⁻¹ = 2 * Real.pi * Real.log (α / η) :=
  Torus.integral_inv_sq_annulus hη hηα

/-- **Truncation identity near one puncture** (centre `0`). -/
theorem tendsto_annulus_energy {ϱ H₁ : ℂ → ℝ} (hα : 0 < α) (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x)
    (hϱ : ContinuousOn ϱ (Metric.closedBall 0 α))
    (hΔ : ∀ x, x ≠ 0 → ‖x‖ ≤ α → Laplacian.laplacian u x = 2 * Real.pi * ϱ x)
    (hH₁ : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < α → H₁ x = u x + truncLog α x) :
    Tendsto (fun η : ℝ => (1 / 2 : ℝ) * (∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, ‖gradient H₁ x‖ ^ 2) +
        Real.pi * Real.log η) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * (∫ x in Metric.ball (0 : ℂ) α, ‖gradient u x‖ ^ 2) +
        Real.pi * Real.log α -
        2 * Real.pi * ∫ x in Metric.ball (0 : ℂ) α, truncLog α x * ϱ x)) := by
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η < α := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hα] with η h1 h2 using ⟨h1, h2.2⟩
  have hgreen := circleAverage_sub_eq_integral_zero hα hu1 hu2 hϱ hΔ
  have hA := tendsto_integral_annulus (integrableOn_norm_gradient_sq hu1 hu2)
  have havg : Tendsto (fun η : ℝ => Real.circleAverage u 0 η) (𝓝[>] 0) (𝓝 (u 0)) := by
    have h := (tendsto_integral_circle hα hu1 hu2).const_mul (2 * Real.pi)⁻¹
    have e : ∀ η : ℝ, (2 * Real.pi)⁻¹ * ∫ θ in (-Real.pi)..Real.pi, u (polarPt η θ) =
        Real.circleAverage u 0 η := fun η => by
      rw [integral_polarPt_eq_circleAverage, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    simp only [e] at h
    have e2 : (2 * Real.pi)⁻¹ * (2 * Real.pi * u 0) = u 0 := by
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rwa [e2] at h
  have hlim := (((hA.const_mul (1 / 2 : ℝ)).add
    ((havg.sub_const (Real.circleAverage u 0 α)).const_mul (2 * Real.pi))).add_const
    (Real.pi * Real.log α))
  have hval : (1 / 2 : ℝ) * (∫ x in Metric.ball (0 : ℂ) α, ‖gradient u x‖ ^ 2) +
      2 * Real.pi * (u 0 - Real.circleAverage u 0 α) + Real.pi * Real.log α =
      (1 / 2 : ℝ) * (∫ x in Metric.ball (0 : ℂ) α, ‖gradient u x‖ ^ 2) +
        Real.pi * Real.log α - 2 * Real.pi * ∫ x in Metric.ball (0 : ℂ) α, truncLog α x * ϱ x := by
    rw [← hgreen]; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with η hη
  rw [integral_annulus_expand hu1 hu2 hη.1 hη.2 hH₁,
    integral_cross_annulus hu2 hη.1 hη.2.le, integral_inv_sq_Ico hη.1 hη.2,
    Real.log_div hα.ne' hη.1.ne']
  ring

end Sphere

end SandierSerfaty

end
