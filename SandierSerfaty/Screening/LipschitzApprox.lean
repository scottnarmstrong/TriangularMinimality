/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Mollify

/-!
# Lipschitz test functions without support condition

* `exists_smooth_approx_lipschitz`: the mollifications `ψₙ = ρₙ ⋆ φ` of a `K`-Lipschitz `φ : ℂ → ℝ`
  are smooth, `|ψₙ - φ| ≤ δₙ → 0` uniformly, `‖∇ψₙ‖ ≤ K`, and `∇ψₙ → ∇φ` a.e. (no support condition;
  the compactly supported version is `exists_smooth_approx`);
* `tendsto_setIntegral_mul_of_approx`: `∫_S f ψₙ → ∫_S f φ` for `f ∈ L¹(S)`, `S` compact.

Used to pass from smooth to Lipschitz test functions in the explicit-field toolbox of the screening note's §4.1
(rectangle solver, radial fields).
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal ContDiff

public section

namespace SandierSerfaty.Screening

/-! ### Smooth approximation of Lipschitz functions without support condition -/

/-- Mollifications of a Lipschitz function on `ℂ`: smooth, uniformly close, gradients bounded by the
Lipschitz constant and converging a.e. (no support condition). -/
theorem exists_smooth_approx_lipschitz {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∃ (ψ : ℕ → ℂ → ℝ) (δ : ℕ → ℝ), Tendsto δ atTop (𝓝 0) ∧ (∀ n, ContDiff ℝ ∞ (ψ n)) ∧
      (∀ n x, |ψ n x - φ x| ≤ δ n) ∧ (∀ n x, ‖gradient (ψ n) x‖ ≤ K) ∧
      (∀ᵐ x, Tendsto (fun n => gradient (ψ n) x) atTop (𝓝 (gradient φ x))) := by
  have h1 : (0 : ℝ) < 1 := one_pos
  refine ⟨fun n => mollify (mollBump h1 n) φ, fun n => K * (mollBump h1 n).rOut, ?_,
    fun n => contDiff_mollify _ hφ.continuous, fun n x => abs_mollify_sub_le _ hφ x,
    fun n x => norm_gradient_mollify_le _ hφ x, ?_⟩
  · simpa using (tendsto_mollBump_rOut h1).const_mul (K : ℝ)
  · have hloc : LocallyIntegrable (gradient φ) volume :=
      (memLp_top_of_bound (aestronglyMeasurable_gradient φ) K
        (Eventually.of_forall fun x => norm_gradient_le_of_lipschitz hφ x)).locallyIntegrable le_top
    have h2 : ∀ᶠ n in atTop, (mollBump h1 n).rOut ≤ 2 * (mollBump h1 n).rIn :=
      Eventually.of_forall fun n => by simp only [mollBump]; linarith
    filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (tendsto_mollBump_rOut h1) h2 hloc] with x hx
    simpa only [gradient_mollify_eq_convolution _ hφ x] using hx

/-- Passing to the limit in `∫_S f ψₙ` under uniform convergence on a compact set. -/
theorem tendsto_setIntegral_mul_of_approx {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} {S : Set X} (hS : IsCompact S)
    {f : X → ℝ} (hf : IntegrableOn f S μ) {ψ : ℕ → X → ℝ} {φ : X → ℝ} {δ : ℕ → ℝ}
    (hψ : ∀ n, Continuous (ψ n)) (hφ : Continuous φ) (hδ : Tendsto δ atTop (𝓝 0))
    (h : ∀ n x, |ψ n x - φ x| ≤ δ n) :
    Tendsto (fun n => ∫ x in S, f x * ψ n x ∂μ) atTop (𝓝 (∫ x in S, f x * φ x ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖(∫ x in S, f x * ψ n x ∂μ) - ∫ x in S, f x * φ x ∂μ‖ ≤
      δ n * ∫ x in S, ‖f x‖ ∂μ := by
    intro n
    rw [← integral_sub (hf.mul_continuousOn (hψ n).continuousOn hS)
      (hf.mul_continuousOn hφ.continuousOn hS), ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (Eventually.of_forall fun x => ?_)
    rw [← mul_sub, norm_mul, mul_comm, Real.norm_eq_abs (ψ n x - φ x)]
    exact mul_le_mul_of_nonneg_right (h n x) (norm_nonneg _)
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  simpa using hδ.mul_const (∫ x in S, ‖f x‖ ∂μ)

end SandierSerfaty.Screening

end
