/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Scaling
public import SandierSerfaty.Sphere.PunctureSplit

/-!
# Scaling of admissibility (sphere note, Lemma 6.10, scaling transfer)

`Sphere.PunctureAdmissible.smul`: if `H` is admissible on `(G, P)` and `σ > 0`, then `z ↦ H (σ⁻¹ z)` is admissible
on `(σ G, σ P)`.  Used to pass from the chart potential `h_X` to the blown-up potential `H = h_X(· / s_n)`.
-/

open MeasureTheory Set Filter Topology
open scoped Pointwise

public section

namespace SandierSerfaty

namespace Sphere

theorem integrableOn_smul_set_iff {σ : ℝ} (hσ : 0 < σ) {f : ℂ → ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) :
    IntegrableOn f (σ • S) ↔ IntegrableOn (fun y => f (σ • y)) S := by
  have hSσ : MeasurableSet (σ • S) := by
    exact hS.const_smul₀ σ
  have hiff := integrable_comp_smul_iff (volume : Measure ℂ) ((σ • S).indicator f) hσ.ne'
  have e : (fun y : ℂ => (σ • S).indicator f (σ • y)) = S.indicator fun y => f (σ • y) := by
    ext y
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy, indicator_of_mem (Set.smul_mem_smul_set hy)]
    · have : σ • y ∉ σ • S := fun h => hy ((smul_mem_smul_set_iff₀ hσ.ne' S y).1 h)
      rw [indicator_of_notMem hy, indicator_of_notMem this]
  rw [← integrable_indicator_iff hSσ, ← integrable_indicator_iff hS, ← e]
  exact hiff.symm

theorem tendsto_smul_inv_nhdsNE {σ : ℝ} (hσ : 0 < σ) (p : ℂ) :
    Tendsto (fun x : ℂ => (σ⁻¹ : ℝ) • x) (𝓝[≠] (σ • p)) (𝓝[≠] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℂ => (σ⁻¹ : ℝ) • x) (𝓝 (σ • p)) (𝓝 ((σ⁻¹ : ℝ) • (σ • p))) :=
      (continuous_const_smul _).tendsto _
    rw [inv_smul_smul₀ hσ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx h
    apply hx
    exact (inv_smul_eq_iff₀ hσ.ne').1 h

/-- **Scaling transfer of admissibility.** -/
theorem PunctureAdmissible.smul {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) {σ : ℝ} (hσ : 0 < σ) :
    PunctureAdmissible (σ • G) (P.image fun p => σ • p) fun z => H ((σ⁻¹ : ℝ) • z) where
  isOpen := hH.isOpen.smul₀ hσ.ne'
  subset := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hq)
    exact Set.smul_mem_smul_set (hH.subset hp)
  c2 x hx hxP := by
    have hxG : (σ⁻¹ : ℝ) • x ∈ G := by
      rw [mem_smul_set_iff_inv_smul_mem₀ hσ.ne'] at hx; exact hx
    have hxP' : (σ⁻¹ : ℝ) • x ∉ (P : Set ℂ) := by
      intro h
      apply hxP
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨_, Finset.mem_coe.1 h, smul_inv_smul₀ hσ.ne' x⟩)
    exact (hH.c2 _ hxG hxP').comp x ((contDiff_const_smul (σ⁻¹ : ℝ)).contDiffAt)
  local_form q hq := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨s, hs, hform⟩ := hH.local_form p hp
    refine ⟨fun x => s ((σ⁻¹ : ℝ) • x) + Real.log σ, ?_, ?_⟩
    · have h1 : ContDiffAt ℝ 1 s ((σ⁻¹ : ℝ) • (σ • p)) := by
        rwa [inv_smul_smul₀ hσ.ne']
      exact (h1.comp (σ • p) ((contDiff_const_smul (σ⁻¹ : ℝ)).contDiffAt)).add contDiffAt_const
    · filter_upwards [(tendsto_smul_inv_nhdsNE hσ p).eventually hform,
        self_mem_nhdsWithin] with x hx hxne
      have hne : x - σ • p ≠ 0 := sub_ne_zero.2 hxne
      have e : (σ⁻¹ : ℝ) • x - p = (σ⁻¹ : ℝ) • (x - σ • p) := by
        rw [smul_sub, inv_smul_smul₀ hσ.ne']
      have hn : ‖(σ⁻¹ : ℝ) • x - p‖ = σ⁻¹ * ‖x - σ • p‖ := by
        rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hσ.le)]
      have hxn : 0 < ‖x - σ • p‖ := norm_pos_iff.2 hne
      rw [hx, hn, Real.log_mul (inv_pos.2 hσ).ne' hxn.ne', Real.log_inv]
      ring
  finite_energy ε hε := by
    have hset := smul_diff_iUnion_ball hσ G P ε
    rw [← hset]
    have hmeas : MeasurableSet (G \ ⋃ p ∈ P, Metric.ball p (ε / σ)) :=
      hH.isOpen.measurableSet.diff
        (Finset.measurableSet_biUnion P fun p _ => Metric.isOpen_ball.measurableSet)
    rw [integrableOn_smul_set_iff hσ hmeas]
    have h := hH.finite_energy (ε / σ) (div_pos hε hσ)
    have key : ∀ y : ℂ, ‖gradient (fun z => H ((σ⁻¹ : ℝ) • z)) (σ • y)‖ ^ 2 =
        (σ ^ 2)⁻¹ * ‖gradient H y‖ ^ 2 := by
      intro y
      rw [norm_gradient_comp_smul H hσ, inv_smul_smul₀ hσ.ne', mul_pow, inv_pow]
    exact IntegrableOn.congr_fun (h.const_mul ((σ ^ 2)⁻¹)) (fun y _ => (key y).symm) hmeas

end Sphere

end SandierSerfaty

end
