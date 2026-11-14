/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Maximum principles for real harmonic functions on the plane

Mathlib has the mean value property for harmonic functions on `ℂ`
(`InnerProductSpace.HarmonicOnNhd.circleAverage_eq`) but no maximum principle. This file derives the
maximum principles from it:

* `eq_of_circleAverage_eq_of_le`: a continuous function bounded above by `M` on a circle whose average
  is `M` equals `M` on the circle.
* `HarmonicOnNhd.eqOn_ball_of_le`: a harmonic function on a disk with an interior maximum equals the
  maximum on the whole disk.
* `HarmonicOnNhd.le_of_forall_frontier_le`: the weak maximum principle on a bounded open set.
* `HarmonicOnNhd.eqOn_of_isPreconnected`: the strong maximum principle on a preconnected open set.
-/

open Metric MeasureTheory Real Set Filter Topology

public section

namespace InnerProductSpace

/-- A continuous function bounded above by `M` on a circle with circle average `M` equals `M` on
the circle. -/
theorem eq_of_circleAverage_eq_of_le {f : ℂ → ℝ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere c r)) (hle : ∀ z ∈ sphere c r, f z ≤ M)
    (hav : circleAverage f c r = M) : ∀ z ∈ sphere c r, f z = M := by
  set g : ℝ → ℝ := fun θ => M - f (circleMap c r θ) with hg
  have hmem : ∀ θ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  have hfc : Continuous fun θ => f (circleMap c r θ) :=
    hf.comp_continuous (continuous_circleMap c r) hmem
  have hcont : Continuous g := continuous_const.sub hfc
  have hint : ∫ θ in (0:ℝ)..2*π, g θ = 0 := by
    rw [circleAverage, smul_eq_mul] at hav
    have h1 : ∫ θ in (0:ℝ)..2*π, g θ = 2 * π * M - ∫ θ in (0:ℝ)..2*π, f (circleMap c r θ) := by
      simp only [hg]
      rw [intervalIntegral.integral_sub (by simp) (hfc.intervalIntegrable _ _)]
      simp
    have h2 : ∫ θ in (0:ℝ)..2*π, f (circleMap c r θ) = 2 * π * M := by
      have : (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2*π, f (circleMap c r θ) = M := hav
      field_simp at this
      linarith
    rw [h1, h2]; ring
  have hnn : ∀ θ, 0 ≤ g θ := fun θ => sub_nonneg.2 (hle _ (hmem θ))
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae (μ := volume)
    (by positivity : (0:ℝ) ≤ 2*π)
    (Filter.Eventually.of_forall hnn) (hcont.intervalIntegrable _ _)).1 hint
  have heq := Measure.eqOn_of_ae_eq (s := Icc 0 (2*π)) (f := g) (g := fun _ => 0) (by
    rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := 2*π)).symm]; exact hae) hcont.continuousOn
    continuousOn_const
    (by rw [interior_Icc, closure_Ioo (by positivity)])
  intro z hz
  obtain ⟨θ₀, hθ₀⟩ : z ∈ Set.range (circleMap c r) := by
    rw [range_circleMap, abs_of_pos hr]; exact hz
  obtain ⟨θ, hθ, hθe⟩ := (periodic_circleMap c r).exists_mem_Ico₀ Real.two_pi_pos θ₀
  have := heq (Ico_subset_Icc_self hθ)
  simp only [hg] at this
  rw [← hθe, hθ₀] at this
  linarith

/-- A harmonic function on a disk that is bounded above by `M` and equals `M` at the center equals
`M` on the whole disk. -/
theorem HarmonicOnNhd.eqOn_ball_of_le {v : ℂ → ℝ} {x : ℂ} {d M : ℝ}
    (hv : HarmonicOnNhd v (ball x d)) (hle : ∀ z ∈ ball x d, v z ≤ M) (hx : v x = M) :
    ∀ y ∈ ball x d, v y = M := by
  intro y hy
  have hd : 0 < d := pos_of_mem_ball hy
  by_cases hyx : y = x
  · rw [hyx, hx]
  set s := dist y x with hs
  have hs0 : 0 < s := dist_pos.2 hyx
  have hsd : s < d := hy
  have hsub : closedBall x |s| ⊆ ball x d := by
    rw [abs_of_pos hs0]; exact closedBall_subset_ball hsd
  have hav : circleAverage v x s = M := by
    rw [(hv.mono hsub).circleAverage_eq, hx]
  have hcs : sphere x s ⊆ ball x d := fun z hz => hsub (by
    rw [abs_of_pos hs0]; exact sphere_subset_closedBall hz)
  refine eq_of_circleAverage_eq_of_le hs0 ((hv.mono hcs).continuousOn) (fun z hz => hle z (hcs hz)) hav y ?_
  exact mem_sphere.2 hs.symm

/-- **Weak maximum principle**: a harmonic function on a bounded open set, continuous on the closure,
is bounded above on the closure by its supremum over the frontier. -/
theorem HarmonicOnNhd.le_of_forall_frontier_le {U : Set ℂ} {v : ℂ → ℝ} {m : ℝ}
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hv : HarmonicOnNhd v U)
    (hc : ContinuousOn v (closure U)) (hfr : ∀ y ∈ frontier U, v y ≤ m) :
    ∀ x ∈ closure U, v x ≤ m := by
  have hK : IsCompact (closure U) := hb.isCompact_closure
  intro x hx
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hc
  refine le_trans (hx₀ hx) ?_
  by_cases hfx : x₀ ∈ frontier U
  · exact hfr _ hfx
  have hx₀U : x₀ ∈ U := by
    rw [hU.frontier_eq] at hfx
    by_contra h
    exact hfx ⟨hx₀K, h⟩
  have hUc : IsClosed Uᶜ := hU.isClosed_compl
  have hne : Uᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    rw [h] at hb
    exact NormedSpace.unbounded_univ ℝ ℂ hb
  have hdpos : 0 < infDist x₀ Uᶜ := (hUc.notMem_iff_infDist_pos hne).1 (by simpa using hx₀U)
  obtain ⟨y, hyU, hy⟩ := hUc.exists_infDist_eq_dist hne x₀
  set d := infDist x₀ Uᶜ with hd
  have hball : ball x₀ d ⊆ U := by
    intro z hz
    by_contra hzU
    have := infDist_le_dist_of_mem (x := x₀) (s := Uᶜ) (y := z) hzU
    rw [mem_ball] at hz
    rw [dist_comm] at hz
    linarith
  have hKb : ∀ z ∈ ball x₀ d, v z ≤ v x₀ := fun z hz => hx₀ (subset_closure (hball hz))
  have heq := (hv.mono hball).eqOn_ball_of_le hKb rfl
  have hyfr : y ∈ frontier U := by
    rw [hU.frontier_eq]
    refine ⟨?_, hyU⟩
    have : y ∈ closedBall x₀ d := by rw [mem_closedBall, dist_comm, ← hy]
    exact closure_mono hball (by rwa [closure_ball _ hdpos.ne'])
  have hclosed : IsClosed (closure U ∩ v ⁻¹' {v x₀}) :=
    hc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hsub : ball x₀ d ⊆ closure U ∩ v ⁻¹' {v x₀} := fun z hz =>
    ⟨subset_closure (hball hz), heq z hz⟩
  have hy' : y ∈ closure U ∩ v ⁻¹' {v x₀} := by
    apply (closure_minimal hsub hclosed)
    rw [closure_ball _ hdpos.ne', mem_closedBall, dist_comm, ← hy]
  have := hy'.2
  simp only [mem_preimage, mem_singleton_iff] at this
  rw [← this]
  exact hfr y hyfr

/-- **Strong maximum principle**: a harmonic function on a preconnected open set, bounded above by `M`
and attaining `M` somewhere, is identically `M`. -/
theorem HarmonicOnNhd.eqOn_of_isPreconnected {U : Set ℂ} {v : ℂ → ℝ} {M : ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hv : HarmonicOnNhd v U)
    (hle : ∀ z ∈ U, v z ≤ M) {x₀ : ℂ} (hx₀ : x₀ ∈ U) (hM : v x₀ = M) :
    ∀ x ∈ U, v x = M := by
  have key : ∀ z ∈ U, v z = M → z ∈ interior (U ∩ v ⁻¹' {M}) := by
    intro z hz hvz
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
    have := (hv.mono hεU).eqOn_ball_of_le (fun w hw => hle w (hεU hw)) hvz
    rw [mem_interior]
    exact ⟨ball z ε, fun w hw => ⟨hεU hw, this w hw⟩, isOpen_ball, mem_ball_self hε⟩
  have h := hconn.subset_of_closure_inter_subset (u := interior (U ∩ v ⁻¹' {M})) isOpen_interior
    ⟨x₀, hx₀, key x₀ hx₀ hM⟩ (by
      rintro z ⟨hzc, hzU⟩
      apply key z hzU
      obtain ⟨t, ht, hts⟩ := (continuousOn_iff_isClosed.1 (hv.continuousOn)) {M} isClosed_singleton
      have hsub : U ∩ v ⁻¹' {M} ⊆ t := by
        intro w hw
        have : w ∈ t ∩ U := by rw [← hts]; exact ⟨hw.2, hw.1⟩
        exact this.1
      have hz1 : z ∈ closure (U ∩ v ⁻¹' {M}) :=
        closure_mono (interior_subset : interior (U ∩ v ⁻¹' {M}) ⊆ U ∩ v ⁻¹' {M}) hzc
      have : z ∈ t := closure_minimal hsub ht hz1
      have hz' : z ∈ v ⁻¹' {M} ∩ U := by rw [hts]; exact ⟨this, hzU⟩
      exact hz'.1)
  intro x hx
  exact (interior_subset (h hx)).2

end InnerProductSpace

end
