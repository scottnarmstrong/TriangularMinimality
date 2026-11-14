/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.WeylLocal
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Weyl's lemma on `ℂ`

**Theorem** (`Weyl.weyl_lemma`). Let `U ⊆ ℂ` be open and `u : ℂ → ℝ` locally integrable on `U` with
`∫_U u Δψ = 0` for every smooth compactly supported `ψ` with `tsupport ψ ⊆ U` (that is,
`Weyl.IsWeaklyHarmonicOn U u`). Then there is `v` smooth on `U` with `v = u` almost everywhere on
`U` and `Δ v = 0` on `U`.

Proof: locally, `Weyl.exists_contDiff_ae_eq_of_isWeaklyHarmonicOn` applied to the truncation of `u`
to a disk; two such local representatives are continuous and agree a.e. on the overlap, hence agree
there, so they glue.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- Local form of Weyl's lemma on a small disk around each point of `U`. -/
theorem weyl_local_ball {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ}
    (hu : LocallyIntegrableOn u U volume) (hw : IsWeaklyHarmonicOn U u) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ r > 0, ball x₀ r ⊆ U ∧ ∃ v₀ : ℂ → ℝ, ContDiff ℝ ∞ v₀ ∧
      (∀ᵐ x ∂(volume.restrict (ball x₀ r)), v₀ x = u x) ∧ ∀ x ∈ ball x₀ r, Δ v₀ x = 0 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set r : ℝ := ε / 8 with hr
  have hr0 : 0 < r := by positivity
  have hcl : closedBall x₀ (4 * r) ⊆ U :=
    (closedBall_subset_ball (by rw [hr]; linarith)).trans hεU
  have hballU : ball x₀ (3 * r) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hcl
  have hint : IntegrableOn u (ball x₀ (3 * r)) volume :=
    (hu.integrableOn_compact_subset hcl (isCompact_closedBall _ _)).mono_set
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  set ut : ℂ → ℝ := (ball x₀ (3 * r)).indicator u with hut
  have hutint : Integrable ut volume := hint.integrable_indicator measurableSet_ball
  have hw' : IsWeaklyHarmonicOn (ball x₀ (3 * r)) ut := by
    intro ψ hψ hc hs
    have : ∫ x in ball x₀ (3 * r), ut x * Δ ψ x = ∫ x in ball x₀ (3 * r), u x * Δ ψ x := by
      refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
      simp [hut, Set.indicator_of_mem hx]
    rw [this]
    exact (hw.mono hballU) ψ hψ hc hs
  have hsub : ∀ x ∈ ball x₀ r, closedBall x r ⊆ ball x₀ (3 * r) := by
    intro x hx z hz
    rw [mem_ball] at hx
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < 3 * r := by linarith
  obtain ⟨v₀, hv, hae, hlap⟩ := exists_contDiff_ae_eq_of_isWeaklyHarmonicOn isOpen_ball hr0 hsub
    hutint.locallyIntegrable hw'
  refine ⟨r, hr0, (ball_subset_ball (by linarith)).trans hballU, v₀, hv, ?_, hlap⟩
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with x hx hxb
  rw [hx hxb]
  have : x ∈ ball x₀ (3 * r) := ball_subset_ball (by linarith) hxb
  simp [hut, Set.indicator_of_mem this]

/-- **Weyl's lemma.** -/
theorem weyl_lemma {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hw : IsWeaklyHarmonicOn U u) :
    ∃ v : ℂ → ℝ, ContDiffOn ℝ ∞ v U ∧ v =ᵐ[volume.restrict U] u ∧ ∀ x ∈ U, Δ v x = 0 := by
  have hloc : ∀ x₀ ∈ U, ∃ r > 0, ball x₀ r ⊆ U ∧ ∃ v₀ : ℂ → ℝ, ContDiff ℝ ∞ v₀ ∧
      (∀ᵐ x ∂(volume.restrict (ball x₀ r)), v₀ x = u x) ∧ ∀ x ∈ ball x₀ r, Δ v₀ x = 0 :=
    fun x₀ hx₀ => weyl_local_ball hU hu hw hx₀
  choose! r hr hrU v₀ hv₀s hv₀ae hv₀lap using hloc
  set v : ℂ → ℝ := fun x => v₀ x x with hvdef
  have hagree : ∀ x₀ ∈ U, ∀ y ∈ ball x₀ (r x₀), v y = v₀ x₀ y := by
    intro x₀ hx₀ y hy
    have hyU : y ∈ U := hrU x₀ hx₀ hy
    have hW : IsOpen (ball y (r y) ∩ ball x₀ (r x₀)) := isOpen_ball.inter isOpen_ball
    have hyW : y ∈ ball y (r y) ∩ ball x₀ (r x₀) := ⟨mem_ball_self (hr y hyU), hy⟩
    have hae : v₀ y =ᵐ[volume.restrict (ball y (r y) ∩ ball x₀ (r x₀))] v₀ x₀ := by
      have h1 := ae_restrict_of_ae_restrict_of_subset
        (inter_subset_left : ball y (r y) ∩ ball x₀ (r x₀) ⊆ ball y (r y)) (hv₀ae y hyU)
      have h2 := ae_restrict_of_ae_restrict_of_subset
        (inter_subset_right : ball y (r y) ∩ ball x₀ (r x₀) ⊆ ball x₀ (r x₀)) (hv₀ae x₀ hx₀)
      filter_upwards [h1, h2] with x hx1 hx2
      rw [hx1, hx2]
    exact Measure.eqOn_open_of_ae_eq hae hW (hv₀s y hyU).continuous.continuousOn
      (hv₀s x₀ hx₀).continuous.continuousOn hyW
  have hnhds : ∀ x₀ ∈ U, v =ᶠ[𝓝 x₀] v₀ x₀ := fun x₀ hx₀ =>
    Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self (hr x₀ hx₀)))
      (fun y hy => hagree x₀ hx₀ y hy)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro x₀ hx₀
    exact (((hv₀s x₀ hx₀).contDiffAt).congr_of_eventuallyEq (hnhds x₀ hx₀)).contDiffWithinAt
  · obtain ⟨t, htU, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
      (f := fun x => ball x (r x)) (s := U) (fun x hx =>
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hr x hx))))
    have hall : ∀ᵐ x ∂(volume.restrict (⋃ x₀ ∈ t, ball x₀ (r x₀))), v x = u x := by
      rw [ae_restrict_biUnion_iff _ htc]
      intro x₀ hx₀
      have hx₀U : x₀ ∈ U := htU hx₀
      filter_upwards [hv₀ae x₀ hx₀U, ae_restrict_mem measurableSet_ball] with x hx hxm
      rw [hagree x₀ hx₀U x hxm, hx]
    exact ae_restrict_of_ae_restrict_of_subset hcov hall
  · intro x₀ hx₀
    have := (laplacian_congr_nhds (hnhds x₀ hx₀)).eq_of_nhds
    rw [this]
    exact hv₀lap x₀ hx₀ x₀ (mem_ball_self (hr x₀ hx₀))

end SandierSerfaty.Weyl

end
