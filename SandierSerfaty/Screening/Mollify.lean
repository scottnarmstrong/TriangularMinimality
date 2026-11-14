/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.TruncLogCalculus
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth approximation of Lipschitz functions with compact support

For a `K`-Lipschitz function `φ : ℂ → ℝ` with compact support in an open set `U`, the mollifications
`ψₙ = ρₙ ⋆ φ` (`ρₙ` normalized bumps of radius `rₙ → 0`) are smooth with compact supports in a
fixed compact subset of `U`, converge uniformly (`|ψₙ - φ| ≤ K rₙ`), have gradients bounded by `K`,
and `∇ψₙ = ρₙ ⋆ ∇φ` (`gradient_mollify`, from Rademacher's theorem: the difference quotients of
`ψₙ` are averages of those of `φ`), so `∇ψₙ → ∇φ` almost everywhere (Lebesgue differentiation).
This is `exists_smooth_approx`; `tendsto_integral_inner_gradient` passes to the limit in
`∫ ⟪G, ∇ψₙ⟫` for `G` integrable on that compact set.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace ContinuousLinearMap
open scoped ENNReal NNReal ContDiff Convolution

public section

namespace SandierSerfaty

namespace Screening

/-! ### Gradients and supports -/

theorem gradient_eq_zero_of_notMem_tsupport {f : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport f) :
    gradient f x = 0 := by
  rw [gradient_congr_nhds (notMem_tsupport_iff_eventuallyEq.1 hx)]
  simp [gradient]

theorem norm_gradient_le_of_lipschitz {f : ℂ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : ℂ) :
    ‖gradient f x‖ ≤ K := by
  simp only [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hf

/-! ### Mollification -/

/-- `ρ ⋆ φ` for a normalized bump `ρ`. -/
@[expose] noncomputable def mollify (b : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ) : ℂ → ℝ :=
  b.normed volume ⋆[lsmul ℝ ℝ, volume] φ

theorem mollify_apply (b : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ) (x : ℂ) :
    mollify b φ x = ∫ t, b.normed volume (x - t) * φ t := by
  simp [mollify, convolution_eq_swap, lsmul_apply, smul_eq_mul]

theorem contDiff_mollify (b : ContDiffBump (0 : ℂ)) {φ : ℂ → ℝ} (hφ : Continuous φ) :
    ContDiff ℝ ∞ (mollify b φ) :=
  b.hasCompactSupport_normed.contDiff_convolution_left _ b.contDiff_normed
    hφ.locallyIntegrable

theorem mollify_eq_zero {b : ContDiffBump (0 : ℂ)} {φ : ℂ → ℝ} {x : ℂ}
    (hx : x ∉ cthickening b.rOut (tsupport φ)) : mollify b φ x = 0 := by
  rw [mollify_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : dist x t < b.rOut
  · have : φ t = 0 := by
      by_contra h
      exact hx (mem_cthickening_of_dist_le x t _ _ (subset_tsupport _ h) ht.le)
    simp [this]
  · have : b.normed volume (x - t) = 0 := by
      rw [← Function.notMem_support, b.support_normed_eq, mem_ball, dist_zero_right,
        ← dist_eq_norm]
      exact ht
    simp [this]

theorem tsupport_mollify_subset (b : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ) :
    tsupport (mollify b φ) ⊆ cthickening b.rOut (tsupport φ) :=
  closure_minimal (fun _x hx => by_contra fun h => hx (mollify_eq_zero h)) isClosed_cthickening

theorem abs_mollify_sub_le (b : ContDiffBump (0 : ℂ)) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (x : ℂ) : |mollify b φ x - φ x| ≤ K * b.rOut := by
  have h := b.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := K * b.rOut)
    hφ.continuous.aestronglyMeasurable fun y hy => by
      refine (hφ.dist_le_mul y x).trans ?_
      exact mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.2
  rwa [Real.dist_eq] at h

theorem integrable_normed_sub (b : ContDiffBump (0 : ℂ)) (x : ℂ) :
    Integrable (fun s => b.normed volume (x - s)) volume :=
  (b.integrable_normed (μ := volume)).comp_sub_left x

theorem integral_normed_sub (b : ContDiffBump (0 : ℂ)) (x : ℂ) :
    ∫ s, b.normed volume (x - s) = 1 := by
  rw [integral_sub_left_eq_self (fun s => b.normed volume s) volume x, b.integral_normed]

theorem hasCompactSupport_normed_sub (b : ContDiffBump (0 : ℂ)) (x : ℂ) :
    HasCompactSupport (fun s => b.normed volume (x - s)) :=
  b.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)

theorem continuous_normed_sub (b : ContDiffBump (0 : ℂ)) (x : ℂ) :
    Continuous (fun s => b.normed volume (x - s)) :=
  b.continuous_normed.comp (continuous_const.sub continuous_id)

/-- Translating the variable of integration in a mollification. -/
theorem mollify_add (b : ContDiffBump (0 : ℂ)) (φ : ℂ → ℝ) (x c : ℂ) :
    mollify b φ (x + c) = ∫ s, φ (s + c) * b.normed volume (x - s) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun t => b.normed volume (x + c - t) * φ t) c
  rw [mollify_apply, ← h]
  congr 1; ext s
  rw [mul_comm]; congr 2; abel

theorem integrable_mul_normed_sub (b : ContDiffBump (0 : ℂ)) {f : ℂ → ℝ} (hf : Continuous f)
    (x : ℂ) : Integrable (fun s => f s * b.normed volume (x - s)) volume :=
  (hf.mul (continuous_normed_sub b x)).integrable_of_hasCompactSupport
    (hasCompactSupport_normed_sub b x).mul_left

/-- **The gradient of a mollification** of a Lipschitz function: `∇(ρ ⋆ φ) = ρ ⋆ ∇φ`. -/
theorem gradient_mollify (b : ContDiffBump (0 : ℂ)) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (x : ℂ) :
    gradient (mollify b φ) x = ∫ s, b.normed volume (x - s) • gradient φ s := by
  have hdiff : DifferentiableAt ℝ (mollify b φ) x :=
    ((contDiff_mollify b hφ.continuous).differentiable (by simp)) x
  have hint : Integrable (fun s => b.normed volume (x - s) • gradient φ s) volume := by
    refine Integrable.mono' ((integrable_normed_sub b x).mul_const (K : ℝ))
      ((continuous_normed_sub b x).aestronglyMeasurable.smul
        (aestronglyMeasurable_gradient φ)) (Eventually.of_forall fun s => ?_)
    rw [norm_smul, Real.norm_of_nonneg (b.nonneg_normed _)]
    exact mul_le_mul_of_nonneg_left (norm_gradient_le_of_lipschitz hφ s) (b.nonneg_normed _)
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, real_inner_comm, ← integral_inner hint]
  -- the difference quotients of `ρ ⋆ φ` are averages of those of `φ`
  have hquot : ∀ τ : ℝ, τ⁻¹ • (mollify b φ (x + τ • v) - mollify b φ x) =
      ∫ s, (τ⁻¹ • (φ (s + τ • v) - φ s)) * b.normed volume (x - s) := by
    intro τ
    have h0 : mollify b φ x = ∫ s, φ (s + 0) * b.normed volume (x - s) := by
      rw [← mollify_add, add_zero]
    have hc : ∀ c : ℂ, Continuous fun s => φ (s + c) := fun c =>
      hφ.continuous.comp (continuous_id.add continuous_const)
    rw [mollify_add, h0, ← integral_sub (integrable_mul_normed_sub b (hc (τ • v)) x)
      (integrable_mul_normed_sub b (hc 0) x),
      ← integral_smul]
    congr 1; ext s
    simp only [add_zero, smul_eq_mul]
    ring
  have T1 := (hdiff.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
  simp only [hquot] at T1
  have T2 := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul (μ := volume)
    (integrable_normed_sub b x) v
  rw [tendsto_nhds_unique T1 T2]
  refine integral_congr_ae ?_
  filter_upwards [hφ.ae_differentiableAt_of_real (μ := volume)] with s hs
  rw [hs.lineDeriv_eq_fderiv, real_inner_smul_right, real_inner_comm, inner_gradient_left,
    mul_comm]

theorem norm_gradient_mollify_le (b : ContDiffBump (0 : ℂ)) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (x : ℂ) : ‖gradient (mollify b φ) x‖ ≤ K := by
  rw [gradient_mollify b hφ]
  calc ‖∫ s, b.normed volume (x - s) • gradient φ s‖
      ≤ ∫ s, b.normed volume (x - s) * K := by
        refine norm_integral_le_of_norm_le ((integrable_normed_sub b x).mul_const _)
          (Eventually.of_forall fun s => ?_)
        rw [norm_smul, Real.norm_of_nonneg (b.nonneg_normed _)]
        exact mul_le_mul_of_nonneg_left (norm_gradient_le_of_lipschitz hφ s) (b.nonneg_normed _)
    _ = K := by rw [integral_mul_const, integral_normed_sub, one_mul]

theorem gradient_mollify_eq_convolution (b : ContDiffBump (0 : ℂ)) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (x : ℂ) :
    gradient (mollify b φ) x = (b.normed volume ⋆[lsmul ℝ ℝ, volume] gradient φ) x := by
  rw [gradient_mollify b hφ, convolution_eq_swap]
  simp [lsmul_apply]

/-! ### The approximating sequence -/

/-- The bump of outer radius `ε / (n + 1)` and inner radius half of it. -/
@[expose] noncomputable def mollBump {ε : ℝ} (hε : 0 < ε) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := ε / (n + 1) / 2
  rOut := ε / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < ε / (n + 1) := by positivity
    linarith

theorem tendsto_mollBump_rOut {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (mollBump hε n).rOut) atTop (𝓝 0) := by
  simp only [mollBump]
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
  simp only [mul_zero, mul_one_div] at this
  exact this

/-- **Smooth approximation** of a compactly supported Lipschitz function inside an open set. -/
theorem exists_smooth_approx {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ (ψ : ℕ → ℂ → ℝ) (S : Set ℂ) (δ : ℕ → ℝ), IsCompact S ∧ S ⊆ U ∧ tsupport φ ⊆ S ∧
      Tendsto δ atTop (𝓝 0) ∧
      (∀ n, ContDiff ℝ ∞ (ψ n) ∧ HasCompactSupport (ψ n) ∧ tsupport (ψ n) ⊆ S) ∧
      (∀ n x, |ψ n x - φ x| ≤ δ n) ∧ (∀ n x, ‖gradient (ψ n) x‖ ≤ K) ∧
      (∀ᵐ x, Tendsto (fun n => gradient (ψ n) x) atTop (𝓝 (gradient φ x))) := by
  obtain ⟨ε, hε, hεU⟩ := hφc.isCompact.exists_cthickening_subset_open hU hφU
  set S := cthickening ε (tsupport φ)
  have hS : IsCompact S := hφc.isCompact.cthickening
  have hrε : ∀ n : ℕ, (mollBump hε n).rOut ≤ ε := fun n => by
    simp only [mollBump]
    exact div_le_self hε.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hsupp : ∀ n, tsupport (mollify (mollBump hε n) φ) ⊆ S := fun n =>
    (tsupport_mollify_subset _ φ).trans (cthickening_mono (hrε n) _)
  refine ⟨fun n => mollify (mollBump hε n) φ, S, fun n => K * (mollBump hε n).rOut, hS, hεU,
    self_subset_cthickening _, ?_, fun n => ⟨contDiff_mollify _ hφ.continuous,
      hS.of_isClosed_subset isClosed_closure (hsupp n), hsupp n⟩,
    fun n x => abs_mollify_sub_le _ hφ x, fun n x => norm_gradient_mollify_le _ hφ x, ?_⟩
  · simpa using (tendsto_mollBump_rOut hε).const_mul (K : ℝ)
  · have hloc : LocallyIntegrable (gradient φ) volume :=
      (memLp_top_of_bound (aestronglyMeasurable_gradient φ) K
        (Eventually.of_forall fun x => norm_gradient_le_of_lipschitz hφ x)).locallyIntegrable le_top
    have h2 : ∀ᶠ n in atTop, (mollBump hε n).rOut ≤ 2 * (mollBump hε n).rIn :=
      Eventually.of_forall fun n => by simp only [mollBump]; linarith
    filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (tendsto_mollBump_rOut hε) h2 hloc] with x hx
    simpa only [gradient_mollify_eq_convolution _ hφ x] using hx

/-! ### Passing to the limit in the pairing -/

/-- `⟪G, g⟫` is integrable when `G` is integrable on `S`, `g` is bounded and vanishes off `S`. -/
theorem integrable_inner_of_integrableOn {G g : ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hG : IntegrableOn G S) (hg : AEStronglyMeasurable g volume) {B : ℝ}
    (hgB : ∀ x, ‖g x‖ ≤ B) (hgS : ∀ x ∉ S, g x = 0) :
    Integrable (fun x => inner ℝ (G x) (g x)) volume := by
  have heq : (fun x => inner ℝ (G x) (g x)) = S.indicator (fun x => inner ℝ (G x) (g x)) := by
    ext x; by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hgS x hx, inner_zero_right]
  rw [heq, integrable_indicator_iff hS]
  refine Integrable.mono' (hG.norm.const_mul B) (hG.aestronglyMeasurable.inner hg.restrict)
    (Eventually.of_forall fun x => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hgB x) (norm_nonneg _)

/-- **Dominated convergence for the pairing.** -/
theorem tendsto_integral_inner_gradient {G : ℂ → ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (hG : IntegrableOn G S) {ψ : ℕ → ℂ → ℝ} {φ : ℂ → ℝ} {K : ℝ}
    (hψS : ∀ n, ∀ x ∉ S, gradient (ψ n) x = 0) (hbound : ∀ n x, ‖gradient (ψ n) x‖ ≤ K)
    (hlim : ∀ᵐ x, Tendsto (fun n => gradient (ψ n) x) atTop (𝓝 (gradient φ x))) :
    Tendsto (fun n => ∫ x, inner ℝ (G x) (gradient (ψ n) x)) atTop
      (𝓝 (∫ x, inner ℝ (G x) (gradient φ x))) := by
  refine tendsto_integral_of_dominated_convergence (S.indicator fun x => K * ‖G x‖)
    (fun n => ?_) ?_ (fun n => Eventually.of_forall fun x => ?_) ?_
  · exact (integrable_inner_of_integrableOn hS hG (aestronglyMeasurable_gradient _)
      (hbound n) (hψS n)).aestronglyMeasurable
  · exact (integrable_indicator_iff hS).2 (hG.norm.const_mul K)
  · by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      refine (norm_inner_le_norm _ _).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _)
    · rw [indicator_of_notMem hx, hψS n x hx, inner_zero_right, norm_zero]
  · filter_upwards [hlim] with x hx
    exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp hx

end Screening

end SandierSerfaty

end
