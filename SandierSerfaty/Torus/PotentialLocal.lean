/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.RemovableSingularity
public import SandierSerfaty.Torus.PotentialIntegrable
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Local form of a torus potential near a charge

Let `h` satisfy `SandierSerfaty.IsTorusPotential Γ a h` and let `p` be a charge position
(`p - a i ∈ Γ` for some `i`).

* `IsTorusPotential.exists_local_form`: there are `r > 0` and `v` smooth on `ball p r`, with
  `Δ v = 2π` there, such that `h x = v x - log ‖x - p‖` for `x ∈ ball p r \ {p}`, and `ball p r`
  contains no other charge position. This is `Weyl.removable_singularity` applied to
  `h + log ‖· - p‖`, which has `Δ = 2π` and a finite limit at `p`.
* `IsTorusPotential.exists_norm_gradient_le`: `‖∇h x‖ ≤ C / ‖x - p‖` near `p`.
* `IsTorusPotential.locallyIntegrable_gradient`: `∇h` is locally integrable on `ℂ`.

The gradient is Mathlib's `gradient` on the real inner product space `ℂ`; its pairing with a vector `w`
is `fderiv ℝ h x w` (`Torus.inner_gradient_apply`).
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- The pairing of the gradient with a vector is the Fréchet derivative applied to it. -/
theorem inner_gradient_apply (f : ℂ → ℝ) (x w : ℂ) :
    inner ℝ (gradient f x) w = fderiv ℝ f x w := by
  rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := x)]
  simp

/-- The norm of the gradient is the norm of the Fréchet derivative. -/
theorem norm_gradient_eq (f : ℂ → ℝ) (x : ℂ) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

/-- The derivative of `log ‖· - p‖` away from `p`. -/
theorem hasFDerivAt_log_norm_sub {p x : ℂ} (hx : x ≠ p) :
    HasFDerivAt (fun y : ℂ => Real.log ‖y - p‖) ((‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p)) x := by
  have hn : ‖x - p‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hx))
  have h1 := (Weyl.hasFDerivAt_normSq_sub p x).log hn
  have h2 := h1.const_mul (1 / 2 : ℝ)
  have e : (fun y : ℂ => Real.log ‖y - p‖) = fun y => (1 / 2 : ℝ) * Real.log (‖y - p‖ ^ 2) := by
    funext y; rw [Real.log_pow]; push_cast; ring
  rw [e]
  convert h2 using 1
  ext w
  simp [two_smul]
  ring

/-- `log ‖· - p‖` is harmonic away from `p`. -/
theorem laplacian_log_norm_sub {p x : ℂ} (hx : x ≠ p) :
    Δ (fun y : ℂ => Real.log ‖y - p‖) x = 0 := by
  have hanal : AnalyticAt ℂ (fun y : ℂ => y - p) x :=
    (analyticAt_id.sub analyticAt_const)
  have := (hanal.harmonicAt_log_norm (sub_ne_zero.2 hx)).2.eq_of_nhds
  simpa using this

theorem isOpen_notMem_chargeSet (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] {N : ℕ} (a : Fin N → ℂ) :
    IsOpen {x : ℂ | ∀ i, x - a i ∉ Γ} := by
  have : {x : ℂ | ∀ i, x - a i ∉ Γ} = (chargeSet Γ a)ᶜ := by
    ext x; exact (notMem_chargeSet_iff).symm
  rw [this]; exact (isClosed_chargeSet Γ a).isOpen_compl

/-- If `h = v - log ‖· - p‖` on the punctured ball, with `v` smooth on `ball p r`, then at `x ≠ p` in
the ball the derivative of `h` is that of `v` minus `⟪x - p, ·⟫ / ‖x - p‖²`. -/
theorem fderiv_eq_of_eq_sub_log {h v : ℂ → ℝ} {p : ℂ} {r : ℝ} (hv : ContDiffOn ℝ ∞ v (ball p r))
    (hloc : ∀ x ∈ ball p r, x ≠ p → h x = v x - Real.log ‖x - p‖) {x : ℂ} (hx : x ∈ ball p r)
    (hxp : x ≠ p) :
    fderiv ℝ h x = fderiv ℝ v x - (‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p) := by
  have hev : h =ᶠ[𝓝 x] fun y => v y - Real.log ‖y - p‖ := by
    filter_upwards [isOpen_ball.mem_nhds hx, isOpen_ne.mem_nhds hxp] with y hy hyp
    exact hloc y hy hyp
  have hvd : DifferentiableAt ℝ v x :=
    (hv.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  rw [hev.fderiv_eq]
  exact (hvd.hasFDerivAt.sub (hasFDerivAt_log_norm_sub hxp)).fderiv

end Torus

/-- **Local form of a torus potential near a charge.** There are `r > 0` and a function `v`, smooth on
`ball p r` with `Δ v = 2π` there, such that `h x = v x - log ‖x - p‖` for `x ∈ ball p r \ {p}`, and no
other charge position lies in `ball p r`. -/
theorem IsTorusPotential.exists_local_form {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ}
    {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {p : ℂ}
    (hp : p ∈ Torus.chargeSet Γ a) :
    ∃ r > 0, ∃ v : ℂ → ℝ, ContDiffOn ℝ ∞ v (ball p r) ∧ (∀ x ∈ ball p r, Δ v x = 2 * Real.pi) ∧
      ∀ x ∈ ball p r, x ≠ p → x ∉ Torus.chargeSet Γ a ∧ h x = v x - Real.log ‖x - p‖ := by
  obtain ⟨c, hc⟩ := hP.exists_tendsto_of_mem_chargeSet hp
  have hbd : ∀ᶠ y in 𝓝[≠] p, |h y + Real.log ‖y - p‖| ≤ ‖c‖ + 1 := by
    have := (hc.norm).eventually (eventually_lt_nhds (a := ‖c‖) (b := ‖c‖ + 1) (by linarith))
    filter_upwards [this] with y hy
    exact hy.le
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 (hbd.and (Torus.eventually_notMem_chargeSet Γ a p))
  have hopen := Torus.isOpen_notMem_chargeSet Γ a
  have hcd : ∀ x ∈ ball p ε \ {p}, ContDiffAt ℝ ∞ h x := by
    intro x hx
    have hxn : x ∉ Torus.chargeSet Γ a := (hεs ⟨hx.1, hx.2⟩).2
    exact hP.2.1.contDiffAt (hopen.mem_nhds (Torus.notMem_chargeSet_iff.1 hxn))
  have hlog : ∀ x ∈ ball p ε \ {p}, ContDiffAt ℝ ∞ (fun y : ℂ => Real.log ‖y - p‖) x := by
    intro x hx
    have hxp : x - p ≠ 0 := sub_ne_zero.2 hx.2
    have h1 : ContDiffAt ℝ ∞ (fun y : ℂ => ‖y - p‖) x :=
      (contDiffAt_id.sub contDiffAt_const).norm ℝ hxp
    exact h1.log (norm_ne_zero_iff.2 hxp)
  have hu : ContDiffOn ℝ 2 (fun y => h y + Real.log ‖y - p‖) (ball p ε \ {p}) := fun x hx =>
    (((hcd x hx).add (hlog x hx)).of_le (by norm_num)).contDiffWithinAt
  have hΔ : ∀ x ∈ ball p ε \ {p}, Δ (fun y => h y + Real.log ‖y - p‖) x = 2 * Real.pi := by
    intro x hx
    have hxn : x ∉ Torus.chargeSet Γ a := (hεs ⟨hx.1, hx.2⟩).2
    have e : (fun y => h y + Real.log ‖y - p‖) = h + fun y : ℂ => Real.log ‖y - p‖ := rfl
    rw [e, ContDiffAt.laplacian_add ((hcd x hx).of_le (by norm_num))
      ((hlog x hx).of_le (by norm_num)), hP.2.2.1 x (Torus.notMem_chargeSet_iff.1 hxn),
      Torus.laplacian_log_norm_sub hx.2, add_zero]
  obtain ⟨v, hv, hveq, hvΔ⟩ := Weyl.removable_singularity isOpen_ball (mem_ball_self hε) (2 * Real.pi)
    hu hΔ ⟨‖c‖ + 1, by filter_upwards [hbd] with y hy using hy |>.trans' le_rfl⟩
  refine ⟨ε, hε, v, hv, hvΔ, fun x hx hxp => ⟨(hεs ⟨hx, hxp⟩).2, ?_⟩⟩
  have := hveq ⟨hx, hxp⟩
  linarith

/-- **Gradient bound near a charge:** `‖∇h x‖ ≤ C / ‖x - p‖` for `x` near `p`. -/
theorem IsTorusPotential.exists_norm_gradient_le {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ}
    {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {p : ℂ}
    (hp : p ∈ Torus.chargeSet Γ a) :
    ∃ r > 0, ∃ C : ℝ, ∀ x ∈ ball p r, x ≠ p → ‖gradient h x‖ ≤ C / ‖x - p‖ := by
  obtain ⟨r, hr, v, hv, -, hloc⟩ := hP.exists_local_form hp
  set r' : ℝ := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hsub : closedBall p r' ⊆ ball p r := closedBall_subset_ball (by linarith)
  have hcont : ContinuousOn (fun x => fderiv ℝ v x) (ball p r) :=
    hv.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p r').exists_bound_of_continuousOn (hcont.mono hsub)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p (mem_closedBall_self hr'0.le))
  refine ⟨r', hr'0, M * r' + 1, fun x hx hxp => ?_⟩
  have hxb : x ∈ ball p r := ball_subset_ball (by linarith) hx
  have hxn : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp)
  have hxr : ‖x - p‖ ≤ r' := by
    have := mem_ball.1 hx
    rw [dist_eq_norm] at this
    exact this.le
  have hfd : fderiv ℝ h x = fderiv ℝ v x - (‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p) :=
    Torus.fderiv_eq_of_eq_sub_log hv (fun y hy hyp => (hloc y hy hyp).2) hxb hxp
  rw [Torus.norm_gradient_eq, hfd]
  have h1 : ‖(‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p)‖ = (‖x - p‖)⁻¹ := by
    rw [norm_smul, innerSL_apply_norm, norm_inv, norm_pow, norm_norm]
    field_simp
  have h2 : ‖fderiv ℝ v x‖ ≤ M * r' / ‖x - p‖ := by
    refine (hM x (closedBall_subset_closedBall le_rfl (ball_subset_closedBall hx))).trans ?_
    rw [le_div_iff₀ hxn]
    exact mul_le_mul_of_nonneg_left hxr hM0
  calc ‖fderiv ℝ v x - (‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p)‖
      ≤ ‖fderiv ℝ v x‖ + ‖(‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p)‖ := norm_sub_le _ _
    _ ≤ M * r' / ‖x - p‖ + (‖x - p‖)⁻¹ := by rw [h1]; exact add_le_add h2 le_rfl
    _ = (M * r' + 1) / ‖x - p‖ := by field_simp

namespace Torus

/-- A measurable `ℂ`-valued function bounded by `C / ‖y - x‖` near `x` is integrable near `x`. -/
theorem integrableAtFilter_of_norm_le_inv {f : ℂ → ℂ} {x : ℂ} {r C : ℝ} (hr : 0 < r)
    (hmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ y ∈ ball x r, y ≠ x → ‖f y‖ ≤ C / ‖y - x‖) :
    IntegrableAtFilter f (𝓝 x) volume := by
  refine ⟨ball x r, ball_mem_nhds x hr, ?_⟩
  have hmp : MeasurePreserving (fun y : ℂ => x + y) volume volume :=
    measurePreserving_add_left volume x
  have hf : IntegrableOn (fun y => f (x + y)) (ball 0 r) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := C) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex]) ?_
      (hmeas.comp_measurePreserving hmp)
    filter_upwards [ae_restrict_of_ae ((Set.countable_singleton (0 : ℂ)).ae_notMem volume),
      ae_restrict_mem measurableSet_ball] with y hy0 hyb
    have hy0' : y ≠ 0 := hy0
    have hyb' : x + y ∈ ball x r := by simpa [mem_ball, dist_eq_norm] using hyb
    have := hbound (x + y) hyb' (by simpa using hy0')
    rw [Real.rpow_neg_one]
    simpa [div_eq_mul_inv] using this
  have hpre : (fun y : ℂ => x + y) ⁻¹' ball x r = ball 0 r := by
    ext y; simp [mem_ball, dist_eq_norm]
  exact (hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft x)
    (f := f) (s := ball x r)).1 (by rw [hpre]; exact hf)

end Torus

theorem aestronglyMeasurable_gradient (h : ℂ → ℝ) : AEStronglyMeasurable (gradient h) volume :=
  (((InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp
    (measurable_fderiv ℝ h)).aestronglyMeasurable)

/-- **The gradient of a torus potential is locally integrable.** -/
theorem IsTorusPotential.locallyIntegrable_gradient {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ]
    {N : ℕ} {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) :
    LocallyIntegrable (gradient h) volume := by
  have hopen := Torus.isOpen_notMem_chargeSet Γ a
  intro x
  by_cases hx : x ∈ Torus.chargeSet Γ a
  · obtain ⟨r, hr, C, hC⟩ := hP.exists_norm_gradient_le hx
    exact Torus.integrableAtFilter_of_norm_le_inv hr (aestronglyMeasurable_gradient h) hC
  · have hx' : x ∈ {x : ℂ | ∀ i, x - a i ∉ Γ} := Torus.notMem_chargeSet_iff.1 hx
    have hcont : ContinuousOn (gradient h) {x : ℂ | ∀ i, x - a i ∉ Γ} :=
      (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn
        (hP.2.1.continuousOn_fderiv_of_isOpen hopen (by simp))
    have := (hcont.locallyIntegrableOn (μ := volume) hopen.measurableSet) x hx'
    rwa [hopen.nhdsWithin_eq hx'] at this

end SandierSerfaty

end
