/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Torus.PotentialIntegrable
public import SandierSerfaty.Analysis.PolarDivergence
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The gradient of a torus potential is a distributional gradient (screening note, Lemma 6.4)

For a torus potential `h` (`IsTorusPotential Γ a h`) with locally finite charge set, `h ∈ L¹_loc` and
```
∫ h ∇φ = -∫ φ ∇h        (φ ∈ C_c^∞(ℂ)).
```
`gradient h` is Mathlib's gradient, which is `0` at points of non-differentiability (the charges, a
null set); so `∇h` is the weak gradient of `h`.

## Proof (screening note, Lemma `lem:Etrigrad`)

The identity `GradId h (∇h) φ` is additive in `φ`.

* Away from the charges (`tsupport φ` in the open set where `h` is smooth) it is the integration by
  parts of `Weyl.integral_mul_pd_eq_neg`, in each coordinate direction.
* Near a charge `p` (`tsupport φ ⊆ ball p r`, the ball of the local form `h = v - log ‖· - p‖`) we apply the
  divergence theorem on the exterior of `B(p, η)` (`Analysis.integral_exterior_div`) to the field
  `h φ e`; the boundary term is `O(η (1 + |log η|))`, and the exterior integral converges to the
  full integral by dominated convergence.
* A general test function is split by smooth bump functions, one charge at a time, exactly as in
  `IsTorusPotential.elecId_of_subset`.

**Corollary** `triangularField_isDistGradient`: `E_tri = ∇ h_tri` is the distributional gradient of
`h_tri = torusPotential Λ_tri 0 ∈ L¹_loc` (the clause of `configEnergy`).
-/

open MeasureTheory Filter Topology Metric Set Complex InnerProductSpace
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Assembly

open Torus

/-- The weak gradient identity `∫ H ∇φ = -∫ φ E` for the test function `φ` (the clause of
`configEnergy`; `H` real, `E` complex). -/
@[expose] def GradId (H : ℂ → ℝ) (E : ℂ → ℂ) (φ : ℂ → ℝ) : Prop :=
  (∫ x, H x • gradient φ x) = -(∫ x, φ x • E x)

theorem integrable_smul_gradient {H : ℂ → ℝ} (hH : LocallyIntegrable H volume) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => H x • gradient φ x) :=
  hH.integrable_smul_right_of_hasCompactSupport (continuous_gradient hφ)
    (hasCompactSupport_gradient hc)

theorem integrable_smul_field {E : ℂ → ℂ} (hE : LocallyIntegrable E volume) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) : Integrable (fun x => φ x • E x) :=
  hE.integrable_smul_left_of_hasCompactSupport hφ hc

/-- The weak gradient identity is additive in the test function. -/
theorem GradId.add {H : ℂ → ℝ} {E : ℂ → ℂ} (hH : LocallyIntegrable H volume)
    (hE : LocallyIntegrable E volume) {φ₁ φ₂ : ℂ → ℝ}
    (h₁ : ContDiff ℝ ∞ φ₁) (c₁ : HasCompactSupport φ₁)
    (h₂ : ContDiff ℝ ∞ φ₂) (c₂ : HasCompactSupport φ₂)
    (e₁ : GradId H E φ₁) (e₂ : GradId H E φ₂) : GradId H E (fun x => φ₁ x + φ₂ x) := by
  have d₁ : Differentiable ℝ φ₁ := h₁.differentiable (by simp)
  have d₂ : Differentiable ℝ φ₂ := h₂.differentiable (by simp)
  have hg : ∀ x, gradient (fun y => φ₁ y + φ₂ y) x = gradient φ₁ x + gradient φ₂ x := by
    intro x
    simp only [gradient]
    rw [fderiv_fun_add (d₁ x) (d₂ x), map_add]
  have i₁ := integrable_smul_gradient hH (h₁.of_le (by simp)) c₁
  have i₂ := integrable_smul_gradient hH (h₂.of_le (by simp)) c₂
  have j₁ := integrable_smul_field hE h₁.continuous c₁
  have j₂ := integrable_smul_field hE h₂.continuous c₂
  unfold GradId at *
  simp_rw [hg, smul_add, add_smul]
  rw [integral_add i₁ i₂, integral_add j₁ j₂, e₁, e₂]
  ring

theorem gradient_re (f : ℂ → ℝ) (x : ℂ) : (gradient f x).re = Weyl.pd 1 f x := by
  show (gradient f x).re = fderiv ℝ f x 1
  have e : ∀ w : ℂ, inner ℝ w 1 = w.re := fun w => by simp [Complex.inner]
  rw [← inner_gradient_apply f x 1, e]

theorem gradient_im (f : ℂ → ℝ) (x : ℂ) : (gradient f x).im = Weyl.pd Complex.I f x := by
  show (gradient f x).im = fderiv ℝ f x Complex.I
  have e : ∀ w : ℂ, inner ℝ w Complex.I = w.im := fun w => by simp [Complex.inner]
  rw [← inner_gradient_apply f x Complex.I, e]

/-- The weak gradient identity from its two real components. -/
theorem gradId_of_components {H : ℂ → ℝ} {φ : ℂ → ℝ} (hH : LocallyIntegrable H volume)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (h : ℂ → ℝ)
    (hh : LocallyIntegrable (gradient h) volume)
    (e1 : ∫ x, H x * Weyl.pd 1 φ x = -∫ x, φ x * Weyl.pd 1 h x)
    (e2 : ∫ x, H x * Weyl.pd Complex.I φ x = -∫ x, φ x * Weyl.pd Complex.I h x) :
    GradId H (gradient h) φ := by
  have i1 := integrable_smul_gradient hH hφ hc
  have i2 := integrable_smul_field hh hφ.continuous hc
  unfold GradId
  apply Complex.ext
  · have a1 := integral_re i1
    have a2 := integral_re i2
    simp only [RCLike.re_to_complex, Complex.smul_re, smul_eq_mul, gradient_re] at a1 a2
    rw [Complex.neg_re, ← a1, ← a2, e1]
  · have a1 := integral_im i1
    have a2 := integral_im i2
    simp only [RCLike.im_to_complex, Complex.smul_im, smul_eq_mul, gradient_im] at a1 a2
    rw [Complex.neg_im, ← a1, ← a2, e2]

/-! ### Away from the charges -/

theorem gradId_of_subset_compl {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}
    {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hK : tsupport φ ⊆ {x : ℂ | ∀ i, x - a i ∉ Γ}) : GradId h (gradient h) φ := by
  have hopen := isOpen_notMem_chargeSet Γ a
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have key : ∀ w : ℂ, ∫ x, h x * Weyl.pd w φ x = -∫ x, φ x * Weyl.pd w h x := fun w => by
    have := Weyl.integral_mul_pd_eq_neg hc hK hopen (hP.2.1.of_le (by norm_num)) hφ1 hφ0 w
    simpa [mul_comm] using this
  exact gradId_of_components hP.locallyIntegrable hφ1 hc h hP.locallyIntegrable_gradient
    (key 1) (key Complex.I)

/-! ### Near a charge -/

section Near

variable {h v φ : ℂ → ℝ} {p : ℂ} {r : ℝ}

theorem exists_abs_le_log (hr : 0 < r) (hv : ContDiffOn ℝ ∞ v (ball p r))
    (hloc : ∀ x ∈ ball p r, x ≠ p → h x = v x - Real.log ‖x - p‖) :
    ∃ A : ℝ, ∀ y, y ≠ p → ‖y - p‖ ≤ r / 2 → |h y| ≤ A + |Real.log ‖y - p‖| := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (hv.continuousOn.mono (closedBall_subset_ball (by linarith)))
  refine ⟨A, fun y hyp hy => ?_⟩
  have hyb : y ∈ closedBall p (r / 2) := by rwa [mem_closedBall, dist_eq_norm]
  have hyb' : y ∈ ball p r := closedBall_subset_ball (by linarith) hyb
  rw [hloc y hyb' hyp]
  have := hA y hyb
  rw [Real.norm_eq_abs] at this
  calc |v y - Real.log ‖y - p‖| ≤ |v y| + |Real.log ‖y - p‖| := abs_sub _ _
    _ ≤ A + |Real.log ‖y - p‖| := by linarith

theorem tendsto_mul_abs_log : Tendsto (fun η : ℝ => η * |Real.log η|) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun η : ℝ => |η * Real.log η|) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).abs
    simp only [zero_mul, abs_zero, Real.log_zero] at this
    simpa using tendsto_nhdsWithin_of_tendsto_nhds this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < η from hη)]

/-- The boundary term of the exterior divergence theorem tends to `0` with the radius. -/
theorem tendsto_boundary_term (hr : 0 < r) {A M : ℝ} (hA : ∀ y, y ≠ p → ‖y - p‖ ≤ r / 2 →
      |h y| ≤ A + |Real.log ‖y - p‖|) (hM : ∀ x, |φ x| ≤ M) (a b : ℝ) :
    Tendsto (fun η : ℝ => ∫ θ in (-Real.pi)..Real.pi,
      η * (a * (h (p + Analysis.polarPt η θ) * φ (p + Analysis.polarPt η θ)) * Real.cos θ +
        b * (h (p + Analysis.polarPt η θ) * φ (p + Analysis.polarPt η θ)) * Real.sin θ))
      (𝓝[>] 0) (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hlim : Tendsto (fun η : ℝ => (2 * Real.pi * (|a| + |b|) * M) * (A * η + η * |Real.log η|))
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun η : ℝ => A * η) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous fun η : ℝ => A * η := by fun_prop
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (this.tendsto 0)
    simpa using (h0.add tendsto_mul_abs_log).const_mul (2 * Real.pi * (|a| + |b|) * M)
  refine squeeze_zero_norm' ?_ hlim
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η ≤ r / 2 := by
    have h0 : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
    have h1 : ∀ᶠ η : ℝ in 𝓝[>] 0, η ≤ r / 2 :=
      mem_nhdsWithin_of_mem_nhds (eventually_le_nhds (by linarith))
    exact h0.and h1
  filter_upwards [hev] with η ⟨hη0, hηr⟩
  have hpt : ∀ θ : ℝ, ‖η * (a * (h (p + Analysis.polarPt η θ) * φ (p + Analysis.polarPt η θ)) *
        Real.cos θ + b * (h (p + Analysis.polarPt η θ) * φ (p + Analysis.polarPt η θ)) *
          Real.sin θ)‖ ≤ η * ((|a| + |b|) * ((A + |Real.log η|) * M)) := by
    intro θ
    set y := p + Analysis.polarPt η θ with hy
    have hyn : ‖y - p‖ = η := by
      rw [hy, add_sub_cancel_left, Analysis.norm_polarPt hη0.le]
    have hyp : y ≠ p := fun h' => by rw [h', sub_self, norm_zero] at hyn; exact hη0.ne hyn
    have hh := hA y hyp (hyn ▸ hηr)
    rw [hyn] at hh
    have hΦ := hM y
    have hcs : |a * Real.cos θ + b * Real.sin θ| ≤ |a| + |b| := by
      calc |a * Real.cos θ + b * Real.sin θ| ≤ |a * Real.cos θ| + |b * Real.sin θ| := abs_add_le _ _
        _ ≤ |a| + |b| := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
            (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    have hrew : η * (a * (h y * φ y) * Real.cos θ + b * (h y * φ y) * Real.sin θ) =
        η * ((h y * φ y) * (a * Real.cos θ + b * Real.sin θ)) := by ring
    rw [hrew, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hη0]
    have hA0 : 0 ≤ A + |Real.log η| := (abs_nonneg _).trans hh
    have h1 : |h y| * |φ y| ≤ (A + |Real.log η|) * M :=
      mul_le_mul hh hΦ (abs_nonneg _) hA0
    have h2 : |h y| * |φ y| * |a * Real.cos θ + b * Real.sin θ| ≤
        ((A + |Real.log η|) * M) * (|a| + |b|) :=
      mul_le_mul h1 hcs (abs_nonneg _) (mul_nonneg hA0 hM0)
    calc η * (|h y| * |φ y| * |a * Real.cos θ + b * Real.sin θ|)
        ≤ η * (((A + |Real.log η|) * M) * (|a| + |b|)) := by gcongr
      _ = η * ((|a| + |b|) * ((A + |Real.log η|) * M)) := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := -Real.pi) (b := Real.pi)
    (fun θ _ => hpt θ)
  refine hint.trans ?_
  rw [show |Real.pi - -Real.pi| = 2 * Real.pi by
    rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by positivity)]]
  nlinarith [mul_nonneg hM0 (abs_nonneg (Real.log η))]

theorem contDiffAt_of_local_form (hv : ContDiffOn ℝ ∞ v (ball p r))
    (hloc : ∀ x ∈ ball p r, x ≠ p → h x = v x - Real.log ‖x - p‖) {x : ℂ} (hx : x ∈ ball p r)
    (hxp : x ≠ p) : ContDiffAt ℝ 1 h x := by
  have hev : (fun y => v y - Real.log ‖y - p‖) =ᶠ[𝓝 x] h := by
    filter_upwards [isOpen_ball.mem_nhds hx, isOpen_ne.mem_nhds hxp] with y hy hyp
    exact (hloc y hy hyp).symm
  have hxp' : x - p ≠ 0 := sub_ne_zero.2 hxp
  have h1 : ContDiffAt ℝ 1 (fun y : ℂ => ‖y - p‖) x :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ hxp'
  have hlog : ContDiffAt ℝ 1 (fun y : ℂ => Real.log ‖y - p‖) x := h1.log (norm_ne_zero_iff.2 hxp')
  have hvx : ContDiffAt ℝ 1 v x :=
    (hv.contDiffAt (isOpen_ball.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  exact (hvx.sub hlog).congr_of_eventuallyEq hev.symm

theorem contDiffAt_mul_test (hsm : ∀ x ∈ ball p r, x ≠ p → ContDiffAt ℝ 1 h x)
    (hφ : ContDiff ℝ ∞ φ) (hsub : tsupport φ ⊆ ball p r) {x : ℂ} (hxp : x ≠ p) :
    ContDiffAt ℝ 1 (fun y => h y * φ y) x := by
  by_cases hx : x ∈ tsupport φ
  · exact (hsm x (hsub hx) hxp).mul ((hφ.of_le (by exact_mod_cast le_top)).contDiffAt)
  · have h2 : φ =ᶠ[𝓝 x] 0 := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx; exact hx
    have h3 : (fun y => h y * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [h2] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h3

theorem pd_mul_test (hsm : ∀ x ∈ ball p r, x ≠ p → ContDiffAt ℝ 1 h x)
    (hφ : ContDiff ℝ ∞ φ) (hsub : tsupport φ ⊆ ball p r) {x : ℂ} (hxp : x ≠ p) (w : ℂ) :
    Weyl.pd w (fun y => h y * φ y) x = h x * Weyl.pd w φ x + φ x * Weyl.pd w h x := by
  by_cases hx : x ∈ tsupport φ
  · have hd := (hsm x (hsub hx) hxp).differentiableAt (by norm_num)
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
    have := (hd.hasFDerivAt.mul hφd.hasFDerivAt).fderiv
    simp only [Weyl.pd]
    rw [show (fun y => h y * φ y) = h * φ from rfl, this]
    simp
  · have h2 : φ =ᶠ[𝓝 x] 0 := by
      rw [notMem_tsupport_iff_eventuallyEq] at hx; exact hx
    have h3 : (fun y => h y * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [h2] with y hy
      simp [hy]
    have h4 := h3.fderiv_eq (𝕜 := ℝ)
    have h5 := h2.fderiv_eq (𝕜 := ℝ)
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [Weyl.pd, h4, h5, hφx]

/-- **Near a charge** (`tsupport φ ⊆ ball p r`, `r` the radius of the local form): the exterior
divergence theorem on `{η ≤ ‖x - p‖}` plus dominated convergence as `η → 0`. -/
theorem gradId_near (hr : 0 < r) (hv : ContDiffOn ℝ ∞ v (ball p r))
    (hloc : ∀ x ∈ ball p r, x ≠ p → h x = v x - Real.log ‖x - p‖)
    (hH : LocallyIntegrable h volume) (hg : LocallyIntegrable (gradient h) volume)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hsub : tsupport φ ⊆ ball p r) :
    GradId h (gradient h) φ := by
  obtain ⟨A, hA⟩ := exists_abs_le_log hr hv hloc
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hφ.continuous
  have hM' : ∀ x, |φ x| ≤ M := fun x => by simpa using hM x
  have hsm := fun x (hx : x ∈ ball p r) (hxp : x ≠ p) => contDiffAt_of_local_form hv hloc hx hxp
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hK : IsCompact (tsupport φ) := hc
  -- integrability of the four kinds of terms
  have I1 : ∀ w : ℂ, Integrable (fun x => h x * Weyl.pd w φ x) := fun w => by
    have hcont : Continuous (Weyl.pd w φ) := (Weyl.contDiff_pd (m := 0) hφ1 (by norm_num) w).continuous
    have hcs : HasCompactSupport (Weyl.pd w φ) :=
      HasCompactSupport.intro hK (Weyl.pd_eq_zero_of_notMem hK hφ0 w)
    simpa using hH.integrable_smul_right_of_hasCompactSupport hcont hcs
  have J := integrable_smul_field hg hφ.continuous hc
  have I2re : Integrable (fun x => φ x * Weyl.pd 1 h x) := by
    simpa [gradient_re] using J.re
  have I2im : Integrable (fun x => φ x * Weyl.pd Complex.I h x) := by
    simpa [gradient_im] using J.im
  set G : ℝ → ℝ → ℂ → ℝ := fun a b x =>
    a * (h x * Weyl.pd 1 φ x + φ x * Weyl.pd 1 h x) +
      b * (h x * Weyl.pd Complex.I φ x + φ x * Weyl.pd Complex.I h x) with hGdef
  have hGi : ∀ a b, Integrable (G a b) := fun a b =>
    (((I1 1).add I2re).const_mul a).add (((I1 Complex.I).add I2im).const_mul b)
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η ≤ r / 2 := by
    have h0 : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
    have h1 : ∀ᶠ η : ℝ in 𝓝[>] 0, η ≤ r / 2 :=
      mem_nhdsWithin_of_mem_nhds (eventually_le_nhds (by linarith))
    exact h0.and h1
  have key : ∀ a b : ℝ, ∫ x, G a b x = 0 := by
    intro a b
    have hmeas : ∀ η : ℝ, MeasurableSet {y : ℂ | η ≤ ‖y - p‖} := fun η =>
      measurableSet_le measurable_const (by fun_prop)
    have hD : Tendsto (fun η : ℝ => ∫ x, {y : ℂ | η ≤ ‖y - p‖}.indicator (G a b) x)
        (𝓝[>] 0) (𝓝 (∫ x, G a b x)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖G a b x‖) ?_ ?_
        (hGi a b).norm ?_
      · exact Eventually.of_forall fun η => (hGi a b).aestronglyMeasurable.indicator (hmeas η)
      · exact Eventually.of_forall fun η => Eventually.of_forall fun x =>
          norm_indicator_le_norm_self _ _
      · have hae : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ p := by rw [ae_iff]; simp
        filter_upwards [hae] with x hx
        have hpos : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
        have : ∀ᶠ η : ℝ in 𝓝[>] 0, η ≤ ‖x - p‖ :=
          mem_nhdsWithin_of_mem_nhds (eventually_le_nhds hpos)
        refine tendsto_const_nhds.congr' (this.mono fun η hη => ?_)
        exact (indicator_of_mem (show x ∈ {y : ℂ | η ≤ ‖y - p‖} from hη) _).symm
    have hB := tendsto_boundary_term (φ := φ) (h := h) (p := p) hr hA hM' a b
    have hE : ∀ᶠ η : ℝ in 𝓝[>] 0, ∫ x, {y : ℂ | η ≤ ‖y - p‖}.indicator (G a b) x =
        -∫ θ in (-Real.pi)..Real.pi,
          η * (a * (h (p + Analysis.polarPt η θ) * φ (p + Analysis.polarPt η θ)) * Real.cos θ +
            b * (h (p + Analysis.polarPt η θ) * φ (p + Analysis.polarPt η θ)) * Real.sin θ) := by
      filter_upwards [hev] with η ⟨hη0, hηr⟩
      rw [integral_indicator (hmeas η)]
      have hdiv := Analysis.integral_exterior_div (p := p) (η := η) (R := r) hη0
        (by linarith) (Y₁ := fun y => a * (h y * φ y)) (Y₂ := fun y => b * (h y * φ y))
        (fun x hx => contDiffAt_const.mul (contDiffAt_mul_test hsm hφ hsub hx))
        (fun x hx => contDiffAt_const.mul (contDiffAt_mul_test hsm hφ hsub hx))
        (fun x hx => by
          have : φ x = 0 := hφ0 x fun hxK => by
            have := hsub hxK
            rw [mem_ball, dist_eq_norm] at this
            linarith
          simp [this])
      rw [← hdiv]
      refine setIntegral_congr_fun (hmeas η) fun x hx => ?_
      have hxp : x ≠ p := by
        intro hxp
        have : η ≤ ‖x - p‖ := hx
        rw [hxp, sub_self, norm_zero] at this
        linarith
      have hd := (contDiffAt_mul_test hsm hφ hsub hxp).differentiableAt (by norm_num)
      rw [(hd.hasFDerivAt.const_mul a).fderiv, (hd.hasFDerivAt.const_mul b).fderiv]
      have h1 := pd_mul_test hsm hφ hsub hxp 1
      have h2 := pd_mul_test hsm hφ hsub hxp Complex.I
      simp only [Weyl.pd] at h1 h2
      simp only [hGdef, Weyl.pd, smul_apply, smul_eq_mul, h1, h2]
    have hlim2 : Tendsto (fun η : ℝ => ∫ x, {y : ℂ | η ≤ ‖y - p‖}.indicator (G a b) x)
        (𝓝[>] 0) (𝓝 (-0)) := by
      refine (hB.neg).congr' (hE.mono fun η hη => hη.symm)
    rw [neg_zero] at hlim2
    exact tendsto_nhds_unique hD hlim2
  have e : ∀ w : ℂ, (w = 1 ∨ w = Complex.I) →
      ∫ x, h x * Weyl.pd w φ x = -∫ x, φ x * Weyl.pd w h x := by
    intro w hw
    have hint := (I1 w)
    rcases hw with rfl | rfl
    · have := key 1 0
      simp only [hGdef, one_mul, zero_mul, add_zero] at this
      rw [integral_add (I1 1) I2re] at this
      linarith
    · have := key 0 1
      simp only [hGdef, one_mul, zero_mul, zero_add] at this
      rw [integral_add (I1 Complex.I) I2im] at this
      linarith
  exact gradId_of_components hH hφ1 hc h hg (e 1 (Or.inl rfl)) (e Complex.I (Or.inr rfl))

end Near

/-- **The identity for every test function**, by induction on the finitely many charges in its
support, splitting off one charge at a time with a smooth bump function. -/
theorem gradId_of_subset {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}
    {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) :
    ∀ (S : Finset ℂ) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x ∈ chargeSet Γ a, x ∈ tsupport φ → x ∈ S) → GradId h (gradient h) φ := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro φ hφ hc hS
    refine gradId_of_subset_compl hP hφ hc fun x hx => ?_
    exact notMem_chargeSet_iff.1 fun hxP => by simpa using hS x hxP hx
  | insert q S hq ih =>
    intro φ hφ hc hS
    by_cases hqP : q ∈ chargeSet Γ a
    · obtain ⟨r, hr, v, hv, -, hloc⟩ := hP.exists_local_form hqP
      set χ : ContDiffBump q := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hχdef
      have hχ : ContDiff ℝ ∞ (χ : ℂ → ℝ) := χ.contDiff
      have hφ₁ : ContDiff ℝ ∞ (fun x => φ x * χ x) := hφ.mul hχ
      have hφ₂ : ContDiff ℝ ∞ (fun x => φ x * (1 - χ x)) := hφ.mul (contDiff_const.sub hχ)
      have hc₁ : HasCompactSupport (fun x => φ x * χ x) := hc.mul_right
      have hc₂ : HasCompactSupport (fun x => φ x * (1 - χ x)) := hc.mul_right
      have ts₁ : tsupport (fun x => φ x * χ x) ⊆ ball q r := by
        refine (tsupport_mul_subset_right (f := φ) (g := (χ : ℂ → ℝ))).trans ?_
        rw [χ.tsupport_eq]
        exact closedBall_subset_ball (by show r / 2 < r; linarith)
      have ts₂ : tsupport (fun x => φ x * (1 - χ x)) ⊆ tsupport φ ∩ (ball q (r / 4))ᶜ := by
        refine closure_minimal (fun x hx => ⟨subset_tsupport φ ?_, ?_⟩)
          ((isClosed_tsupport φ).inter isOpen_ball.isClosed_compl)
        · intro h0; exact hx (by simp [h0])
        · intro hb
          apply hx
          have : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hb)
          simp [this]
      have hS₂ : ∀ x ∈ chargeSet Γ a, x ∈ tsupport (fun x => φ x * (1 - χ x)) → x ∈ S := by
        intro x hxP hx
        have h2 := ts₂ hx
        rcases Finset.mem_insert.1 (hS x hxP h2.1) with rfl | hxS
        · exact absurd (mem_ball_self (by positivity : (0 : ℝ) < r / 4)) h2.2
        · exact hxS
      have e₁ := gradId_near hr hv (fun x hx hxq => (hloc x hx hxq).2) hP.locallyIntegrable
        hP.locallyIntegrable_gradient hφ₁ hc₁ ts₁
      have e₂ := ih _ hφ₂ hc₂ hS₂
      have := GradId.add hP.locallyIntegrable hP.locallyIntegrable_gradient hφ₁ hc₁ hφ₂ hc₂ e₁ e₂
      have e : (fun x => φ x * χ x + φ x * (1 - χ x)) = φ := by funext x; ring
      rwa [e] at this
    · refine ih φ hφ hc fun x hxP hx => ?_
      rcases Finset.mem_insert.1 (hS x hxP hx) with rfl | hxS
      · exact absurd hxP hqP
      · exact hxS

/-- **Lemma 6.4** (general torus potential). `h ∈ L¹_loc` and `∇h` is its distributional gradient. -/
theorem isDistGradient_of_isTorusPotential {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h)
    (hlf : ∀ R : ℝ, (chargeSet Γ a ∩ closedBall (0 : ℂ) R).Finite) :
    LocallyIntegrable h volume ∧ ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, h x • gradient φ x) = -(∫ x, φ x • gradient h x) := by
  refine ⟨hP.locallyIntegrable, fun φ hφ hc => ?_⟩
  have hfin : (chargeSet Γ a ∩ tsupport φ).Finite := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
    exact (hlf R).subset fun x hx => ⟨hx.1, hR hx.2⟩
  exact gradId_of_subset hP hfin.toFinset φ hφ hc
    (fun x hxP hx => hfin.mem_toFinset.2 ⟨hxP, hx⟩)

/-- **Lemma 6.4** (screening note, `lem:Etrigrad`), with the potential named: `h_tri = torusPotential Λ_tri 0` is
locally integrable and `E_tri = ∇ h_tri` is its distributional gradient. -/
theorem triangularField_isDistGradient_torusPotential :
    LocallyIntegrable (torusPotential triangularLattice (fun _ : Fin 1 => (0 : ℂ))) volume ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, torusPotential triangularLattice (fun _ : Fin 1 => (0 : ℂ)) x • gradient φ x) =
          -(∫ x, φ x • triangularField x) := by
  have hcov : ZLattice.covolume triangularLattice = ((1 : ℕ) : ℝ) := by
    simpa using Torus.covolume_triangularLattice
  have hP := isTorusPotential_torusPotential triangularLattice hcov
    (fun _ : Fin 1 => (0 : ℂ)) (fun i j _ => Subsingleton.elim i j)
  have hlf : ∀ R : ℝ, (chargeSet triangularLattice (fun _ : Fin 1 => (0 : ℂ)) ∩
      closedBall (0 : ℂ) R).Finite := by
    have hset : periodicSites triangularLattice (fun _ : Fin 1 => (0 : ℂ)) =
        chargeSet triangularLattice (fun _ : Fin 1 => (0 : ℂ)) := by
      ext x; exact mem_periodicSites_iff _ _
    intro R
    rw [← hset]
    exact locallyFiniteSites_periodicSites _ _ 0 R
  exact isDistGradient_of_isTorusPotential hP hlf

/-- **Lemma 6.4**, in the exact form of the clause of `configEnergy`: `E_tri` is a
distributional gradient of a locally integrable function. -/
theorem triangularField_isDistGradient :
    ∃ H : ℂ → ℝ, LocallyIntegrable H volume ∧ ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, H x • gradient φ x) = -(∫ x, φ x • triangularField x) :=
  ⟨_, triangularField_isDistGradient_torusPotential⟩

end Assembly

end SandierSerfaty

end
