/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.TruncShift
public import SandierSerfaty.Sphere.Puncture
public import SandierSerfaty.Torus.PotentialLocal
public import SandierSerfaty.Analysis.HarmonicRemovable

/-!
# The truncation identity (sphere note, Lemma 3.10): the local potential

For `H` admissible on `(G, P)` with `Δ H = 2π ϱ` off `P`, a puncture `p` and a radius `α` with
`\bar B(p, α) ⊆ G` containing no other puncture, the function
`u(x) = H(x) + log ‖x - p‖ - log α` (`x ≠ p`), `u(p) = s(p) - log α` (`H = s - log ‖· - p‖` near `p`)
is `C¹` at `p`, `C²` and satisfies `Δ u = 2π ϱ` on `\bar B(p, α) ∖ {p}`, and `H = u + f_α(· - p)` on
`B(p, α) ∖ {p}` (`Sphere.exists_local_potential`).
-/

open MeasureTheory Filter Topology Set SandierSerfaty.Analysis Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem exists_local_potential {G : Set ℂ} {P : Finset ℂ} {H ϱ : ℂ → ℝ}
    (hH : PunctureAdmissible G P H)
    (hΔ : ∀ x ∈ G, x ∉ (P : Set ℂ) → Laplacian.laplacian H x = 2 * Real.pi * ϱ x)
    {p : ℂ} (hp : p ∈ P) {α : ℝ} (hsub : Metric.closedBall p α ⊆ G)
    (hno : ∀ q ∈ P, q ≠ p → q ∉ Metric.closedBall p α) :
    ∃ u : ℂ → ℝ, ContDiffAt ℝ 1 u p ∧
      (∀ x, x ≠ p → ‖x - p‖ ≤ α → ContDiffAt ℝ 2 u x) ∧
      (∀ x, x ≠ p → ‖x - p‖ ≤ α → Laplacian.laplacian u x = 2 * Real.pi * ϱ x) ∧
      (∀ x, x ≠ p → u x = H x + Real.log ‖x - p‖ - Real.log α) ∧
      (∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < α → H x = u x + truncLog α (x - p)) := by
  classical
  obtain ⟨s, hs1, hs⟩ := hH.local_form p hp
  set u : ℂ → ℝ := Function.update (fun x => H x + Real.log ‖x - p‖ - Real.log α) p
    (s p - Real.log α) with hu
  have hne : ∀ x, x ≠ p → u x = H x + Real.log ‖x - p‖ - Real.log α := fun x hx => by
    simp [hu, Function.update_of_ne hx]
  have hxG : ∀ x, x ≠ p → ‖x - p‖ ≤ α → x ∈ G ∧ x ∉ (P : Set ℂ) := by
    intro x hx hxα
    have hmem : x ∈ Metric.closedBall p α := by
      rw [mem_closedBall_iff_norm]; exact hxα
    refine ⟨hsub hmem, fun hxP => ?_⟩
    by_cases hxp : x = p
    · exact hx hxp
    · exact hno x hxP hxp hmem
  have hlog : ∀ x, x ≠ p → ContDiffAt ℝ 2 (fun y : ℂ => Real.log ‖y - p‖) x := fun x hx =>
    (InnerProductSpace.harmonicAt_log_norm_sub (c := p) hx).1
  have hev : ∀ x, x ≠ p → u =ᶠ[𝓝 x] H + ((fun y : ℂ => Real.log ‖y - p‖) + fun _ => -Real.log α) := by
    intro x hx
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [hne y hy]; simp only [Pi.add_apply]; ring
  refine ⟨u, ?_, ?_, ?_, hne, ?_⟩
  · -- C¹ at p
    have h1 : ContDiffAt ℝ 1 (fun x => s x - Real.log α) p := hs1.sub contDiffAt_const
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [eventually_nhdsWithin_iff.1 hs] with y hy
    by_cases hyp : y = p
    · subst hyp; simp [hu]
    · rw [hne y hyp, hy hyp]; ring
  · intro x hx hxα
    obtain ⟨hxG', hxP⟩ := hxG x hx hxα
    have hc : ContDiffAt ℝ 2 (fun _ : ℂ => -Real.log α) x := contDiffAt_const
    exact ((hH.c2 x hxG' hxP).add ((hlog x hx).add hc)).congr_of_eventuallyEq (hev x hx)
  · intro x hx hxα
    obtain ⟨hxG', hxP⟩ := hxG x hx hxα
    have hc2 := hH.c2 x hxG' hxP
    have hl := hlog x hx
    have hc : ContDiffAt ℝ 2 (fun _ : ℂ => -Real.log α) x := contDiffAt_const
    have hsum : ContDiffAt ℝ 2 ((fun y : ℂ => Real.log ‖y - p‖) + fun _ : ℂ => -Real.log α) x :=
      hl.add hc
    rw [(InnerProductSpace.laplacian_congr_nhds (hev x hx)).self_of_nhds,
      ContDiffAt.laplacian_add hc2 hsum, ContDiffAt.laplacian_add hl hc,
      Torus.laplacian_log_norm_sub hx, hΔ x hxG' hxP]
    simp
  · intro x hx0 hxα
    have hxp : x ≠ p := fun h => by rw [h, sub_self, norm_zero] at hx0; exact lt_irrefl _ hx0
    rw [hne x hxp, Screening.truncLog_eq_log_sub hx0 hxα.le]
    ring

/-! ### Integrability of `|∇u|²` on the disc -/

theorem integrableOn_norm_gradient_sq_at {u : ℂ → ℝ} {p : ℂ} {α : ℝ} (hu1 : ContDiffAt ℝ 1 u p)
    (hu2 : ∀ x, x ≠ p → ‖x - p‖ ≤ α → ContDiffAt ℝ 2 u x) :
    IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (Metric.ball p α) := by
  have hc : ContinuousOn (fun x => ‖gradient u x‖ ^ 2) (Metric.closedBall p α) := by
    intro x hx
    rw [mem_closedBall_iff_norm] at hx
    have c : ContinuousAt (pd₁ u) x ∧ ContinuousAt (pd₂ u) x := by
      by_cases h0 : x = p
      · subst h0
        have h1 := contDiffAt_pd (n := 0) (by simpa using hu1) 1
        have h2 := contDiffAt_pd (n := 0) (by simpa using hu1) Complex.I
        exact ⟨h1.continuousAt, h2.continuousAt⟩
      · have h2 : ContDiffAt ℝ (1 + 1 : ℕ) u x := by norm_num; exact hu2 x h0 hx
        exact ⟨(contDiffAt_pd (n := 1) h2 1).continuousAt,
          (contDiffAt_pd (n := 1) h2 Complex.I).continuousAt⟩
    refine ContinuousAt.continuousWithinAt ?_
    simp only [norm_gradient_sq]
    exact (c.1.pow 2).add (c.2.pow 2)
  exact (hc.integrableOn_compact (isCompact_closedBall p α)).mono_set Metric.ball_subset_closedBall

end Sphere

end SandierSerfaty

end
