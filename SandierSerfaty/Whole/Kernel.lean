/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Analysis.GreenIdentity

/-!
# The planar kernel `κ(y) = y / ‖y‖²` and the linear field: weak divergence and curl

`κ = ∇ log ‖·‖` and `x ↦ x - c = ∇(‖x - c‖² / 2)`. In the weak sense, tested against `C¹` compactly
supported `φ` (convention `ℂ = ℝ²`, `∇φ = ∂₁φ + i ∂₂φ`, curl tested against `i ∇φ`):

* `integral_inner_kernel_gradient`: `∫ ⟪κ(x - p), ∇φ⟫ = -2π φ(p)` (`div κ = 2π δ₀`);
* `integral_inner_kernel_I_gradient`: `∫ ⟪κ(x - p), i ∇φ⟫ = 0` (`curl κ = 0`);
* `integral_inner_sub_gradient`: `∫ ⟪x - c, ∇φ⟫ = -2 ∫ φ`;
* `integral_inner_sub_I_gradient`: `∫ ⟪x - c, i ∇φ⟫ = 0`.

The curl identities follow from `integral_radial_mul_fderiv_I`: in polar coordinates around `p` the
integrand is an angular derivative, whose integral over a full circle vanishes. These are the
ingredients of the regularity lemma (comparison note, Lemma `lem:regularity`, paper Lemma `red:local`).
-/

open MeasureTheory Filter Topology Metric InnerProductSpace Set
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Whole

/-- `κ(y) = y / ‖y‖²`, the gradient of `log ‖y‖` (with `κ 0 = 0`). -/
@[expose] noncomputable def kernel (y : ℂ) : ℂ := (‖y‖ ^ 2)⁻¹ • y

theorem norm_kernel (y : ℂ) : ‖kernel y‖ = ‖y‖⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [kernel]
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp

theorem measurable_kernel : Measurable kernel :=
  ((measurable_norm.pow_const 2).inv).smul measurable_id

theorem continuousAt_kernel {y : ℂ} (hy : y ≠ 0) : ContinuousAt kernel y := by
  have hn : ‖y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  exact ((continuous_norm.pow 2).continuousAt.inv₀ hn).smul continuousAt_id

theorem continuousOn_kernel_sub (p : ℂ) : ContinuousOn (fun x => kernel (x - p)) {p}ᶜ := by
  intro x hx
  exact (ContinuousAt.comp (f := fun y : ℂ => y - p) (x := x) (continuousAt_kernel (sub_ne_zero.2 hx))
    (continuous_sub_right p).continuousAt).continuousWithinAt

/-- `κ(· - p)` is locally integrable (`‖κ(y)‖ = ‖y‖⁻¹` is integrable near `0` in the plane). -/
theorem locallyIntegrable_kernel_sub (p : ℂ) : LocallyIntegrable (fun x => kernel (x - p)) volume := by
  intro x
  by_cases hx : x = p
  · subst hx
    refine Torus.integrableAtFilter_of_norm_le_inv (C := 1) one_pos
      (measurable_kernel.comp (measurable_id.sub_const _)).aestronglyMeasurable fun y _ _ => ?_
    rw [norm_kernel, one_div]
  · have hopen : IsOpen ({p}ᶜ : Set ℂ) := isOpen_compl_singleton
    have := ((continuousOn_kernel_sub p).locallyIntegrableOn (μ := volume) hopen.measurableSet) x hx
    rwa [hopen.nhdsWithin_eq hx] at this

/-- A locally integrable field paired with a continuous compactly supported field is integrable. -/
theorem integrable_inner_of_locallyIntegrable {E G : ℂ → ℂ} (hE : LocallyIntegrable E volume)
    (hG : Continuous G) (hc : HasCompactSupport G) :
    Integrable (fun x => inner ℝ (E x) (G x)) := by
  have hK : IsCompact (tsupport G) := hc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hG
  have hEK : IntegrableOn (fun x => M * ‖E x‖) (tsupport G) :=
    ((hE.integrableOn_isCompact hK).norm).const_mul M
  have hmeas : AEStronglyMeasurable (fun x => inner ℝ (E x) (G x)) volume :=
    AEStronglyMeasurable.inner (hE.aestronglyMeasurable : AEStronglyMeasurable E volume)
      hG.aestronglyMeasurable
  refine Integrable.mono' (hEK.integrable_indicator hK.measurableSet) hmeas
    (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport G
  · rw [indicator_of_mem hx]
    calc ‖inner ℝ (E x) (G x)‖ ≤ ‖E x‖ * ‖G x‖ := norm_inner_le_norm _ _
      _ ≤ ‖E x‖ * M := by gcongr; exact hM x
      _ = M * ‖E x‖ := mul_comm _ _
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
    simp

theorem continuous_I_mul_gradient {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Continuous fun x => Complex.I * gradient φ x :=
  continuous_const.mul (Torus.continuous_gradient hφ)

theorem hasCompactSupport_I_mul_gradient {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport fun x => Complex.I * gradient φ x :=
  (Torus.hasCompactSupport_gradient hc).mul_left

/-- `⟪y, i w⟫ = -⟪i y, w⟫`. -/
theorem inner_I_mul_right (y w : ℂ) : inner ℝ y (Complex.I * w) = -inner ℝ (Complex.I * y) w := by
  simp only [Complex.inner, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ### Polar coordinates: angular derivatives integrate to zero -/

theorem hasDerivAt_dir (θ : ℝ) : HasDerivAt Torus.dir (Complex.I * Torus.dir θ) θ := by
  have h1 := (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I
  have h : HasDerivAt Torus.dir (((-Real.sin θ : ℝ) : ℂ) + ((Real.cos θ : ℝ) : ℂ) * Complex.I) θ :=
    h1.add h2
  convert h using 1
  simp only [Torus.dir, Complex.ofReal_neg]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The angular derivative of `φ` along the circle `s ↦ p + r e^{is}`. -/
theorem hasDerivAt_arc {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (p : ℂ) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => φ ((r : ℂ) * Torus.dir s + p))
      (r * fderiv ℝ φ ((r : ℂ) * Torus.dir θ + p) (Complex.I * Torus.dir θ)) θ := by
  have h1 : HasDerivAt (fun s : ℝ => (r : ℂ) * Torus.dir s + p)
      ((r : ℂ) * (Complex.I * Torus.dir θ)) θ :=
    ((hasDerivAt_dir θ).const_mul (r : ℂ)).add_const p
  have h2 : HasFDerivAt φ (fderiv ℝ φ ((r : ℂ) * Torus.dir θ + p)) ((r : ℂ) * Torus.dir θ + p) :=
    (hφ.differentiable (by norm_num) _).hasFDerivAt
  have h := h2.comp_hasDerivAt θ h1
  have e : (r : ℂ) * (Complex.I * Torus.dir θ) = r • (Complex.I * Torus.dir θ) :=
    (Complex.real_smul).symm
  rw [e, map_smul, smul_eq_mul] at h
  exact h

theorem dir_neg_pi : Torus.dir (-Real.pi) = Torus.dir Real.pi := by
  simp [Torus.dir]

/-- **Angular derivatives integrate to zero.** For a radial weight `a` with `r² a(r)` locally bounded on
`(0, ∞)`, `∫ a(‖x - p‖) ∂φ(x)[i (x - p)] dx = 0`. -/
theorem integral_radial_mul_fderiv_I {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (p : ℂ) {a : ℝ → ℝ} (ha : Measurable a)
    (hab : ∀ R : ℝ, ∃ M : ℝ, ∀ r ∈ Ioc (0 : ℝ) R, |r ^ 2 * a r| ≤ M) :
    ∫ x : ℂ, a ‖x - p‖ * fderiv ℝ φ x (Complex.I * (x - p)) = 0 := by
  obtain ⟨R, hR⟩ := Torus.exists_forall_norm_le_zero hc
  set R' : ℝ := R + ‖p‖ with hR'
  obtain ⟨M, hM⟩ := hab R'
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x : ℂ, ‖fderiv ℝ φ x‖ ≤ B := by
    have hfc : HasCompactSupport (fderiv ℝ φ) := hc.fderiv (𝕜 := ℝ)
    exact hfc.exists_bound_of_continuous (hφ.continuous_fderiv (by norm_num))
  set Φ : ℂ → ℝ := fun y => a ‖y‖ * fderiv ℝ φ (y + p) (Complex.I * y) with hΦ
  have h1 : ∫ x : ℂ, a ‖x - p‖ * fderiv ℝ φ x (Complex.I * (x - p)) = ∫ y : ℂ, Φ y := by
    rw [← integral_sub_right_eq_self Φ p]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [hΦ]
  rw [h1, ← Complex.integral_comp_polarCoord_symm]
  set D : ℝ × ℝ → ℝ := fun z =>
    fderiv ℝ φ ((z.1 : ℂ) * Torus.dir z.2 + p) (Complex.I * Torus.dir z.2) with hD
  set G : ℝ × ℝ → ℝ := fun z => (z.1 ^ 2 * a z.1) * D z with hG
  have h2 : ∫ z in polarCoord.target, z.1 • Φ (Complex.polarCoord.symm z) =
      ∫ z in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, G z := by
    rw [polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun z hz => ?_
    have hr : 0 < z.1 := hz.1
    have hsymm : Complex.polarCoord.symm z = (z.1 : ℂ) * Torus.dir z.2 := by
      rw [Complex.polarCoord_symm_apply]; rfl
    simp only [hΦ, hG, hD, hsymm, smul_eq_mul]
    have hn : ‖(z.1 : ℂ) * Torus.dir z.2‖ = z.1 := by
      rw [norm_mul, Torus.norm_dir, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hlin : fderiv ℝ φ ((z.1 : ℂ) * Torus.dir z.2 + p) (Complex.I * ((z.1 : ℂ) * Torus.dir z.2)) =
        z.1 * fderiv ℝ φ ((z.1 : ℂ) * Torus.dir z.2 + p) (Complex.I * Torus.dir z.2) := by
      have : Complex.I * ((z.1 : ℂ) * Torus.dir z.2) = z.1 • (Complex.I * Torus.dir z.2) := by
        rw [Complex.real_smul]; ring
      rw [this, map_smul, smul_eq_mul]
    rw [hn, hlin]
    ring
  rw [h2]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  have hdir : Continuous Torus.dir := by unfold Torus.dir; fun_prop
  have hDc : Continuous D := by
    have h1 : Continuous fun z : ℝ × ℝ => (z.1 : ℂ) * Torus.dir z.2 + p := by
      have hs2 : Continuous fun z : ℝ × ℝ => Torus.dir z.2 := hdir.comp continuous_snd
      exact ((Complex.continuous_ofReal.comp continuous_fst).mul hs2).add continuous_const
    exact ((hφ.continuous_fderiv (by norm_num)).comp h1).clm_apply
      (continuous_const.mul (hdir.comp continuous_snd))
  have hDB : ∀ z, |D z| ≤ B := by
    intro z
    have := (fderiv ℝ φ ((z.1 : ℂ) * Torus.dir z.2 + p)).le_opNorm (Complex.I * Torus.dir z.2)
    rw [norm_mul, Complex.norm_I, Torus.norm_dir, one_mul, mul_one, Real.norm_eq_abs] at this
    exact this.trans (hB _)
  have hfar : ∀ z : ℝ × ℝ, R' < z.1 → D z = 0 := by
    intro z hz
    have hz' : R < ‖(z.1 : ℂ) * Torus.dir z.2 + p‖ := by
      have h1 : ‖(z.1 : ℂ) * Torus.dir z.2‖ = |z.1| := by
        rw [norm_mul, Torus.norm_dir, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖(z.1 : ℂ) * Torus.dir z.2‖ ≤ ‖(z.1 : ℂ) * Torus.dir z.2 + p‖ + ‖p‖ := by
        have := norm_sub_le ((z.1 : ℂ) * Torus.dir z.2 + p) p
        simpa using this
      linarith [le_abs_self z.1]
    simp [hD, (hR _ hz').1]
  have hGm : AEStronglyMeasurable G ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have : Measurable G := by
      refine Measurable.mul ?_ hDc.measurable
      exact (measurable_fst.pow_const 2).mul (ha.comp measurable_fst)
    exact this.aestronglyMeasurable
  have hint : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have hs : IntegrableOn G (Ioc (0 : ℝ) R' ×ˢ Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      refine Measure.integrableOn_of_bounded (M := M * B) ?_ hGm ?_
      · rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top (by simp) (by simp)
      · rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioo)]
        refine Eventually.of_forall fun z hz => ?_
        rw [hG, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hM z.1 hz.1) (hDB z) (abs_nonneg _)
          ((abs_nonneg _).trans (hM z.1 hz.1))
    refine hs.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    intro z hz
    have hz2 : R' < z.1 := by
      by_contra hle
      exact hz.2 ⟨⟨hz.1.1, not_lt.1 hle⟩, hz.1.2⟩
    simp [hG, hfar z hz2]
  rw [hvol, setIntegral_prod _ hint]
  have hinner : ∀ r ∈ Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi, G (r, θ) = 0 := by
    intro r hr
    have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
    have hθc : Continuous fun θ : ℝ => D (r, θ) := hDc.comp (by fun_prop)
    have hftc : ∫ θ in (-Real.pi)..Real.pi, r * D (r, θ) = 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ =>
        φ ((r : ℂ) * Torus.dir s + p)) (fun θ _ => hasDerivAt_arc hφ p r θ)
        ((continuous_const.mul hθc).intervalIntegrable _ _)]
      simp [dir_neg_pi]
    have hD0 : ∫ θ in (-Real.pi)..Real.pi, D (r, θ) = 0 := by
      rw [intervalIntegral.integral_const_mul] at hftc
      exact (mul_eq_zero.1 hftc).resolve_left hr0
    have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    simp only [hG]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi, hD0,
      mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  simp

/-! ### The kernel -/

theorem inner_kernel_gradient (φ : ℂ → ℝ) (p x : ℂ) :
    inner ℝ (kernel (x - p)) (gradient φ x) = (‖x - p‖ ^ 2)⁻¹ * fderiv ℝ φ x (x - p) := by
  rw [kernel, real_inner_smul_left, real_inner_comm, Torus.inner_gradient_apply]

theorem inner_kernel_I_gradient (φ : ℂ → ℝ) (p x : ℂ) :
    inner ℝ (kernel (x - p)) (Complex.I * gradient φ x) =
      -((‖x - p‖ ^ 2)⁻¹ * fderiv ℝ φ x (Complex.I * (x - p))) := by
  rw [kernel, real_inner_smul_left, inner_I_mul_right, real_inner_comm, Torus.inner_gradient_apply]
  ring

/-- `div κ(· - p) = 2π δ_p` weakly. -/
theorem integral_inner_kernel_gradient {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (p : ℂ) : ∫ x, inner ℝ (kernel (x - p)) (gradient φ x) = -(2 * Real.pi * φ p) := by
  simp_rw [inner_kernel_gradient]
  exact Torus.integral_fderiv_div_sq hφ hc p

/-- `curl κ(· - p) = 0` weakly. -/
theorem integral_inner_kernel_I_gradient {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (p : ℂ) : ∫ x, inner ℝ (kernel (x - p)) (Complex.I * gradient φ x) = 0 := by
  simp_rw [inner_kernel_I_gradient]
  rw [integral_neg, integral_radial_mul_fderiv_I (a := fun r => (r ^ 2)⁻¹) hφ hc p
    (measurable_id.pow_const 2).inv, neg_zero]
  intro R
  refine ⟨1, fun r hr => ?_⟩
  have : r ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hr.1)
  rw [mul_inv_cancel₀ this, abs_one]

/-! ### The linear field -/

theorem clm_apply_eq_re_im (L : ℂ →L[ℝ] ℝ) (z : ℂ) : L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem pd_re_sub (c x : ℂ) : Weyl.pd 1 (fun y : ℂ => (y - c).re) x = 1 := by
  have e : (fun y : ℂ => (y - c).re) = fun y => Complex.reCLM y - c.re := by funext y; simp
  rw [Weyl.pd, e, fderiv_sub_const, Complex.reCLM.fderiv]
  simp

theorem pd_im_sub (c x : ℂ) : Weyl.pd Complex.I (fun y : ℂ => (y - c).im) x = 1 := by
  have e : (fun y : ℂ => (y - c).im) = fun y => Complex.imCLM y - c.im := by funext y; simp
  rw [Weyl.pd, e, fderiv_sub_const, Complex.imCLM.fderiv]
  simp

/-- `div (x - c) = 2` weakly. -/
theorem integral_inner_sub_gradient {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (c : ℂ) : ∫ x, inner ℝ (x - c) (gradient φ x) = -(2 * ∫ x, φ x) := by
  have hK : IsCompact (tsupport φ) := hc
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hre : ContDiffOn ℝ 1 (fun y : ℂ => (y - c).re) univ :=
    (Complex.reCLM.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
  have him : ContDiffOn ℝ 1 (fun y : ℂ => (y - c).im) univ :=
    (Complex.imCLM.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
  have hpt : ∀ x, inner ℝ (x - c) (gradient φ x) =
      (x - c).re * Weyl.pd 1 φ x + (x - c).im * Weyl.pd Complex.I φ x := by
    intro x
    rw [real_inner_comm, Torus.inner_gradient_apply, clm_apply_eq_re_im]
    rfl
  have i1 : Integrable fun x => (x - c).re * Weyl.pd 1 φ x :=
    Weyl.integrable_mul_of_supp hK (subset_univ _) hre.continuousOn
      (Weyl.contDiff_pd (m := 0) hφ (by norm_num) 1).continuous (Weyl.pd_eq_zero_of_notMem hK hφ0 1)
  have i2 : Integrable fun x => (x - c).im * Weyl.pd Complex.I φ x :=
    Weyl.integrable_mul_of_supp hK (subset_univ _) him.continuousOn
      (Weyl.contDiff_pd (m := 0) hφ (by norm_num) Complex.I).continuous
      (Weyl.pd_eq_zero_of_notMem hK hφ0 Complex.I)
  simp_rw [hpt]
  rw [integral_add i1 i2,
    Weyl.integral_mul_pd_eq_neg hK (subset_univ _) isOpen_univ hre hφ hφ0 1,
    Weyl.integral_mul_pd_eq_neg hK (subset_univ _) isOpen_univ him hφ hφ0 Complex.I]
  simp_rw [pd_re_sub, pd_im_sub, one_mul]
  ring

/-- `curl (x - c) = 0` weakly. -/
theorem integral_inner_sub_I_gradient {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (c : ℂ) : ∫ x, inner ℝ (x - c) (Complex.I * gradient φ x) = 0 := by
  have hpt : ∀ x, inner ℝ (x - c) (Complex.I * gradient φ x) =
      -((fun _ : ℝ => (1 : ℝ)) ‖x - c‖ * fderiv ℝ φ x (Complex.I * (x - c))) := by
    intro x
    rw [inner_I_mul_right, real_inner_comm, Torus.inner_gradient_apply, one_mul]
  simp_rw [hpt]
  rw [integral_neg, integral_radial_mul_fderiv_I hφ hc c measurable_const, neg_zero]
  intro R
  refine ⟨max (R ^ 2) 0, fun r hr => ?_⟩
  rw [mul_one, abs_of_nonneg (sq_nonneg r)]
  exact le_max_of_le_left (pow_le_pow_left₀ hr.1.le hr.2 2)

end Whole

end SandierSerfaty

end
