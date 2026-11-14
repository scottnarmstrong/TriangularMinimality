/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.TruncationIdentity
public import SandierSerfaty.Sphere.Lower.ChartTruncation

/-!
# Integrability of the truncated gradient (companion to the truncation identity)

`Lower.integrableOn_truncated_grad`: under the hypotheses of `Sphere.truncation_identity`, `|∇H_α|²` is integrable on `G`.
(The proof of the identity establishes this internally; it is needed here to compare `∫_G |∇H_α|²` with the sum of the
integrals over disjoint subsets.)
-/

open MeasureTheory Filter Topology Set SandierSerfaty.Analysis Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem integrableOn_truncated_grad {G : Set ℂ} {P : Finset ℂ} {H ϱ : ℂ → ℝ} {r : ℂ → ℝ}
    (hH : PunctureAdmissible G P H)
    (hΔ : ∀ x ∈ G, x ∉ (P : Set ℂ) → Laplacian.laplacian H x = 2 * Real.pi * ϱ x)
    (hr : ∀ p ∈ P, 0 < r p) (hsub : ∀ p ∈ P, Metric.closedBall p (r p) ⊆ G)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint (Metric.closedBall p (r p)) (Metric.closedBall q (r q))) :
    IntegrableOn (fun x => ‖gradient (fun y => H y - ∑ p ∈ P, truncLog (r p) (y - p)) x‖ ^ 2) G := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_radius_lower hr
  have hno : ∀ p ∈ P, ∀ q ∈ P, q ≠ p → q ∉ Metric.closedBall p (r p) := fun p hp q hq hqp hqm =>
    (Set.disjoint_left.1 (hdisj p hp q hq (Ne.symm hqp))) hqm
      (Metric.mem_closedBall_self (hr q hq).le)
  have hloc : ∀ p ∈ P, ∃ u : ℂ → ℝ, ContDiffAt ℝ 1 u p ∧
      (∀ x, x ≠ p → ‖x - p‖ ≤ r p → ContDiffAt ℝ 2 u x) ∧
      (∀ x, x ≠ p → ‖x - p‖ ≤ r p → Laplacian.laplacian u x = 2 * Real.pi * ϱ x) ∧
      (∀ x, x ≠ p → u x = H x + Real.log ‖x - p‖ - Real.log (r p)) ∧
      (∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < r p → H x = u x + truncLog (r p) (x - p)) :=
    fun p hp => exists_local_potential hH hΔ hp (hsub p hp) (hno p hp)
  choose! u hu1 hu2 hu3 hu4 hu5 using hloc
  set Hα : ℂ → ℝ := fun y => H y - ∑ p ∈ P, truncLog (r p) (y - p) with hHα
  set D₀ : Set ℂ := G \ ⋃ p ∈ P, Metric.ball p (r p) with hD₀
  have hGopen : IsOpen G := hH.isOpen
  have hD₀m : MeasurableSet D₀ :=
    hGopen.measurableSet.diff
      (Finset.measurableSet_biUnion P fun p _ => Metric.isOpen_ball.measurableSet)
  have hballG : ∀ p ∈ P, Metric.ball p (r p) ⊆ G := fun p hp =>
    Metric.ball_subset_closedBall.trans (hsub p hp)
  have hq_far : ∀ p ∈ P, ∀ y ∈ Metric.ball p (r p), ∀ q ∈ P, q ≠ p → r q ≤ ‖y - q‖ := by
    intro p hp y hy q hq hqp
    by_contra hlt
    rw [not_le] at hlt
    have h1 : y ∈ Metric.closedBall q (r q) := by rw [mem_closedBall_iff_norm]; exact hlt.le
    exact Set.disjoint_left.1 (hdisj p hp q hq (Ne.symm hqp)) (Metric.ball_subset_closedBall hy) h1
  have hα_far : ∀ y : ℂ, (∀ p ∈ P, r p ≤ ‖y - p‖) → Hα y = H y := by
    intro y hy
    simp only [hHα]
    rw [Finset.sum_eq_zero fun p hp => Screening.truncLog_eq_zero (hr p hp) (hy p hp), sub_zero]
  have hα_ball : ∀ p ∈ P, ∀ y ∈ Metric.ball p (r p), y ≠ p → Hα y = u p y := by
    intro p hp y hy hyp
    have hn : ‖y - p‖ < r p := mem_ball_iff_norm.1 hy
    have hn0 : 0 < ‖y - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hyp)
    simp only [hHα]
    rw [Finset.sum_eq_single p (fun q hq hqp => Screening.truncLog_eq_zero (hr q hq)
      (hq_far p hp y hy q hq hqp)) (fun h => absurd hp h), hu5 p hp y hn0 hn]
    ring
  have hsph : ∀ᵐ x : ℂ ∂volume, ∀ p ∈ P, ‖x - p‖ ≠ r p := by
    refine (Filter.eventually_all_finset P).2 fun p _ => ?_
    have h0 : volume (Metric.sphere p (r p)) = 0 := Measure.addHaar_sphere volume p (r p)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx h
    exact hx (mem_sphere_iff_norm.2 h)
  have hgD : ∀ᵐ x : ℂ ∂volume.restrict D₀, ‖gradient Hα x‖ ^ 2 = ‖gradient H x‖ ^ 2 := by
    refine (ae_restrict_iff' hD₀m).2 ?_
    filter_upwards [hsph] with x hx hxD
    have hfar : ∀ p ∈ P, r p < ‖x - p‖ := fun p hp => by
      have h1 : r p ≤ ‖x - p‖ := by
        by_contra hlt
        rw [not_le] at hlt
        exact hxD.2 (Set.mem_biUnion hp (mem_ball_iff_norm.2 hlt))
      exact lt_of_le_of_ne h1 (Ne.symm (hx p hp))
    have hopen : IsOpen (⋂ p ∈ P, {y : ℂ | r p < ‖y - p‖}) :=
      isOpen_biInter_finset fun p _ =>
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    have hev : Hα =ᶠ[𝓝 x] H := by
      filter_upwards [hopen.mem_nhds (Set.mem_iInter₂.2 fun p hp => hfar p hp)] with y hy
      exact hα_far y fun p hp => (Set.mem_iInter₂.1 hy p hp).le
    rw [Screening.gradient_congr_nhds hev]
  have hgB : ∀ p ∈ P, ∀ᵐ x : ℂ ∂volume.restrict (Metric.ball p (r p)),
      ‖gradient Hα x‖ ^ 2 = ‖gradient (u p) x‖ ^ 2 := by
    intro p hp
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 ?_
    filter_upwards [(Set.countable_singleton p).ae_notMem volume] with x hx hxb
    have hxp : x ≠ p := hx
    have hopen : IsOpen (Metric.ball p (r p) ∩ {y : ℂ | y ≠ p}) :=
      Metric.isOpen_ball.inter isOpen_ne
    have hev : Hα =ᶠ[𝓝 x] u p := by
      filter_upwards [hopen.mem_nhds ⟨hxb, hxp⟩] with y hy
      exact hα_ball p hp y hy.1 hy.2
    rw [Screening.gradient_congr_nhds hev]
  have hfin : ∀ η : ℝ, 0 < η →
      IntegrableOn (fun x => ‖gradient H x‖ ^ 2) (G \ ⋃ p ∈ P, Metric.ball p η) :=
    hH.finite_energy
  have hD₀η : D₀ ⊆ G \ ⋃ p ∈ P, Metric.ball p m := fun x hx =>
    ⟨hx.1, fun h => by
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 h
      exact hx.2 (Set.mem_biUnion hp (Metric.ball_subset_ball (hm p hp) hxp))⟩
  have iD : IntegrableOn (fun x => ‖gradient H x‖ ^ 2) D₀ := (hfin m hm0).mono_set hD₀η
  have iDα : IntegrableOn (fun x => ‖gradient Hα x‖ ^ 2) D₀ :=
    iD.congr_fun_ae (hgD.mono fun x hx => hx.symm)
  have iBα : ∀ p ∈ P, IntegrableOn (fun x => ‖gradient Hα x‖ ^ 2) (Metric.ball p (r p)) :=
    fun p hp => (integrableOn_norm_gradient_sq_at (hu1 p hp) (hu2 p hp)).congr_fun_ae
      ((hgB p hp).mono fun x hx => hx.symm)
  have hsetG : G = D₀ ∪ ⋃ p ∈ P, Metric.ball p (r p) := by
    refine Set.Subset.antisymm ?_ (Set.union_subset Set.sdiff_subset
      (Set.iUnion₂_subset fun p hp => hballG p hp))
    intro x hxG
    by_cases hex : ∃ p ∈ P, x ∈ Metric.ball p (r p)
    · obtain ⟨p, hp, hxp⟩ := hex
      exact Or.inr (Set.mem_biUnion hp hxp)
    · exact Or.inl ⟨hxG, fun h => hex (by
        obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 h; exact ⟨p, hp, hxp⟩)⟩
  rw [hsetG]
  exact iDα.union (integrableOn_finset_iUnion.2 iBα)

end Lower

end Sphere

end SandierSerfaty

end
