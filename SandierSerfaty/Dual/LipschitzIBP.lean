/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PeriodicIntegral
public import SandierSerfaty.Geometry.VoronoiPeriodic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Periodic integration by parts for Lipschitz functions

* `integral_torusDomain_fderiv_lipschitz`: for a Lipschitz `Γ`-periodic `F`,
  `∫_D ∂_e F = 0` (the a.e. derivative; the difference quotients are bounded by the Lipschitz
  constant and converge a.e. by Rademacher's theorem). This is the Lipschitz analogue of
  `SandierSerfaty.Torus.integral_torusDomain_fderiv`, which replaces the divergence theorem for the
  periodic trial potential, glued from `C¹` pieces along Lipschitz interfaces (paper proof of `dual:gluing`).
* `lipschitzWith_of_locallyLipschitz_periodic`: a periodic locally Lipschitz function is Lipschitz.
* `LipschitzWith.mul_of_bounded`: product of bounded Lipschitz functions.
-/

open MeasureTheory Filter Topology Set Metric

public section

namespace SandierSerfaty

namespace Dual

section Prod

theorem LipschitzWith_mul_of_bounded {E : Type*} [PseudoMetricSpace E] {f g : E → ℝ}
    {Kf Kg : NNReal} {Mf Mg : ℝ} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfb : ∀ x, |f x| ≤ Mf) (hgb : ∀ x, |g x| ≤ Mg) :
    LipschitzWith (Real.toNNReal Mf * Kg + Real.toNNReal Mg * Kf) (fun x => f x * g x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfb x)
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgb x)
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ Mf * (Kg * dist x y) + Mg * (Kf * dist x y) := by
        gcongr
        · exact hfb x
        · exact hgb y
    _ = _ := by
        push_cast
        rw [Real.coe_toNNReal _ hMf, Real.coe_toNNReal _ hMg]; ring

end Prod

section Global

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- A `Γ`-periodic, locally Lipschitz function is (globally) Lipschitz. -/
theorem lipschitzWith_of_locallyLipschitz_periodic {f : ℂ → ℝ} (hf : LocallyLipschitz f)
    (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) : ∃ K, LipschitzWith K f := by
  obtain ⟨Rl, hRl⟩ := exists_forall_exists_mem_norm_sub_lt Γ
  obtain ⟨M, hM⟩ := Torus.exists_bound_of_periodic Γ hf.continuous hper
  obtain ⟨K₀, hK₀⟩ := (hf.locallyLipschitzOn (s := closedBall (0 : ℂ) (|Rl| + 1))).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall _ _)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨max K₀ (Real.toNNReal (2 * M)), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  by_cases hxy : 1 ≤ dist x y
  · rw [Real.dist_eq]
    calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM x) (hM y)
      _ = 2 * M * 1 := by ring
      _ ≤ (Real.toNNReal (2 * M) : ℝ) * dist x y := by
          rw [Real.coe_toNNReal _ (by positivity)]
          exact mul_le_mul_of_nonneg_left hxy (by positivity)
      _ ≤ ((max K₀ (Real.toNNReal (2 * M)) : NNReal) : ℝ) * dist x y := by
          gcongr; exact le_max_right _ _
  · rw [not_le] at hxy
    obtain ⟨γ, hγ, hγx⟩ := hRl x
    have hx' : x - γ ∈ closedBall (0 : ℂ) (|Rl| + 1) := by
      rw [mem_closedBall_zero_iff]; exact (hγx.le.trans (le_trans (le_abs_self _) (by linarith)))
    have hy' : y - γ ∈ closedBall (0 : ℂ) (|Rl| + 1) := by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖y - γ‖ ≤ ‖x - γ‖ + ‖y - x‖ := by
        calc ‖y - γ‖ = ‖(x - γ) + (y - x)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖y - x‖ < 1 := by rw [← dist_eq_norm, dist_comm]; exact hxy
      linarith [le_abs_self Rl]
    have := hK₀.dist_le_mul _ hx' _ hy'
    have e1 : f (x - γ) = f x := by
      have := hper γ hγ (x - γ); simpa using this.symm
    have e2 : f (y - γ) = f y := by
      have := hper γ hγ (y - γ); simpa using this.symm
    rw [e1, e2, show dist (x - γ) (y - γ) = dist x y by simp [dist_eq_norm]] at this
    refine this.trans ?_
    gcongr; exact le_max_left _ _

end Global

section IBP

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- **Periodic integration by parts for Lipschitz functions.** -/
theorem integral_torusDomain_fderiv_lipschitz {F : ℂ → ℝ} {K : NNReal} (hF : LipschitzWith K F)
    (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x) (e : ℂ) :
    ∫ x in torusDomain Γ, fderiv ℝ F x e = 0 := by
  set D := torusDomain Γ with hD
  have hfin : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (Torus.volume_torusDomain_ne_top Γ)⟩
  have hFint : IntegrableOn F D := Torus.integrableOn_torusDomain_of_periodic Γ hF.continuous hper
  let q : ℝ → ℂ → ℝ := fun t x => t⁻¹ * (F (x + t • e) - F x)
  have hq0 : ∀ t : ℝ, t ≠ 0 → ∫ x in D, q t x = 0 := by
    intro t ht
    have h1 : ∫ x in D, F (x + t • e) = ∫ x in D, F x := by
      have := Torus.integral_torusDomain_add Γ hper (t • e)
      simpa [add_comm] using this
    have hshift : Integrable (fun x => F (x + t • e)) (volume.restrict D) := by
      have := Torus.integrableOn_torusDomain_of_periodic Γ (f := fun x => F (x + t • e))
        (hF.continuous.comp (continuous_id.add continuous_const))
        (fun γ hγ x => by
          have := hper γ hγ (x + t • e)
          simpa [add_right_comm] using this)
      exact this
    simp only [q]
    rw [integral_const_mul, integral_sub hshift hFint, h1]; simp
  have hlim : ∀ᵐ x ∂(volume.restrict D),
      Tendsto (fun t => q t x) (𝓝[≠] 0) (𝓝 (fderiv ℝ F x e)) := by
    have hdiff : ∀ᵐ x ∂(volume : Measure ℂ), DifferentiableAt ℝ F x := hF.ae_differentiableAt
    filter_upwards [ae_restrict_of_ae hdiff] with x hx
    have h1 : HasDerivAt (fun t : ℝ => F (x + t • e)) (fderiv ℝ F x e) 0 := by
      have : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
      have h2 : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • e) := by
        simpa using hx.hasFDerivAt
      exact h2.comp_hasDerivAt 0 this
    have := h1.tendsto_slope_zero
    refine this.congr fun t => ?_
    simp [q]
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂(volume.restrict D), ‖q t x‖ ≤ K * ‖e‖ := by
    refine Eventually.of_forall fun t => Eventually.of_forall fun x => ?_
    by_cases ht : t = 0
    · simp only [q, ht, inv_zero, zero_mul, norm_zero]; positivity
    · have := hF.dist_le_mul (x + t • e) x
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
      simp only [q, Real.norm_eq_abs, abs_mul, abs_inv]
      rw [inv_mul_le_iff₀ (abs_pos.2 ht)]
      calc |F (x + t • e) - F x| ≤ K * (|t| * ‖e‖) := this
        _ = |t| * (K * ‖e‖) := by ring
        _ = _ := by ring
  have hdct := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict D)
    (l := 𝓝[≠] (0 : ℝ)) (F := q) (f := fun x => fderiv ℝ F x e) (bound := fun _ => (K : ℝ) * ‖e‖)
    ?_ hbound (integrable_const _) hlim
  · have h0 : Tendsto (fun t => ∫ x in D, q t x) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hq0 t ht).symm
    exact tendsto_nhds_unique hdct h0
  · refine Eventually.of_forall fun t => ?_
    simp only [q]
    exact (((hF.continuous.comp (continuous_id.add continuous_const)).sub hF.continuous).const_mul
      _).aestronglyMeasurable

end IBP

end Dual

end SandierSerfaty

end
