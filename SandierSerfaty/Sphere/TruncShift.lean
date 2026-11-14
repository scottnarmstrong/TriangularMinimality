/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.TruncCenter

/-!
# Truncation identity near one puncture, general centre (sphere note, Lemma 3.10, local step)

`Sphere.tendsto_annulus_energy_at`: translation of `Sphere.tendsto_annulus_energy` to a puncture `p`.
-/

open MeasureTheory Filter Topology Set SandierSerfaty.Analysis Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem integral_shift_norm_set (F : ℂ → ℝ) (p : ℂ) (R : Set ℝ) :
    ∫ x in {x : ℂ | ‖x‖ ∈ R}, F (x + p) = ∫ x in {x : ℂ | ‖x - p‖ ∈ R}, F x := by
  have hmp := (measurePreserving_add_right (volume : Measure ℂ) p).setIntegral_preimage_emb
    (measurableEmbedding_addRight p) F {x : ℂ | ‖x - p‖ ∈ R}
  have hpre : (fun z : ℂ => z + p) ⁻¹' {x : ℂ | ‖x - p‖ ∈ R} = {x : ℂ | ‖x‖ ∈ R} := by
    ext z; simp
  rw [hpre] at hmp
  exact hmp

theorem integral_shift_ball (F : ℂ → ℝ) (p : ℂ) (α : ℝ) :
    ∫ x in Metric.ball (0 : ℂ) α, F (x + p) = ∫ x in Metric.ball p α, F x := by
  have hmp := (measurePreserving_add_right (volume : Measure ℂ) p).setIntegral_preimage_emb
    (measurableEmbedding_addRight p) F (Metric.ball p α)
  have hpre : (fun z : ℂ => z + p) ⁻¹' Metric.ball p α = Metric.ball 0 α := by
    ext z; simp
  rw [hpre] at hmp
  exact hmp

theorem norm_gradient_shift (f : ℂ → ℝ) (p x : ℂ) :
    ‖gradient (fun z => f (z + p)) x‖ = ‖gradient f (x + p)‖ := by
  rw [Screening.gradient_comp_add_right]

/-- **Truncation identity near one puncture** (centre `p`). -/
theorem tendsto_annulus_energy_at {u ϱ H₁ : ℂ → ℝ} {p : ℂ} {α : ℝ} (hα : 0 < α)
    (hu1 : ContDiffAt ℝ 1 u p)
    (hu2 : ∀ x, x ≠ p → ‖x - p‖ ≤ α → ContDiffAt ℝ 2 u x)
    (hϱ : ContinuousOn ϱ (Metric.closedBall p α))
    (hΔ : ∀ x, x ≠ p → ‖x - p‖ ≤ α → Laplacian.laplacian u x = 2 * Real.pi * ϱ x)
    (hH₁ : ∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < α → H₁ x = u x + truncLog α (x - p)) :
    Tendsto (fun η : ℝ => (1 / 2 : ℝ) * (∫ x in {x : ℂ | ‖x - p‖ ∈ Ico η α}, ‖gradient H₁ x‖ ^ 2) +
        Real.pi * Real.log η) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * (∫ x in Metric.ball p α, ‖gradient u x‖ ^ 2) +
        Real.pi * Real.log α -
        2 * Real.pi * ∫ x in Metric.ball p α, truncLog α (x - p) * ϱ x)) := by
  have hadd : ContDiff ℝ ∞ (fun z : ℂ => z + p) := contDiff_id.add contDiff_const
  have hmap : ∀ z : ℂ, ‖z‖ ≤ α → ‖z + p - p‖ ≤ α := fun z hz => by simpa using hz
  have h1 : ContDiffAt ℝ 1 (fun z => u (z + p)) 0 := by
    have h0 : ContDiffAt ℝ 1 u ((fun z : ℂ => z + p) 0) := by simpa using hu1
    exact h0.comp (0 : ℂ) (hadd.contDiffAt.of_le (by norm_num))
  have h2 : ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 (fun z => u (z + p)) x := fun x hx hxα =>
    (hu2 (x + p) (fun h => hx (by simpa using h)) (hmap x hxα)).comp x
      (hadd.contDiffAt.of_le (by norm_num))
  have h3 : ContinuousOn (fun z => ϱ (z + p)) (Metric.closedBall 0 α) :=
    hϱ.comp hadd.continuous.continuousOn (fun z hz => by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_closedBall_iff_norm]; exact hmap z hz)
  have h4 : ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ α →
      Laplacian.laplacian (fun z => u (z + p)) x = 2 * Real.pi * ϱ (x + p) := fun x hx hxα => by
    have := laplacian_comp_sub u (-p) x
    simp only [sub_neg_eq_add] at this
    rw [this]
    exact hΔ (x + p) (fun h => hx (by simpa using h)) (hmap x hxα)
  have h5 : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < α →
      (fun z => H₁ (z + p)) x = (fun z => u (z + p)) x + truncLog α x := fun x hx hxα => by
    have := hH₁ (x + p) (by simpa using hx) (by simpa using hxα)
    simpa using this
  have key := tendsto_annulus_energy hα h1 h2 h3 h4 h5
  have e1 : ∀ η : ℝ, ∫ x in {x : ℂ | ‖x‖ ∈ Ico η α}, ‖gradient (fun z => H₁ (z + p)) x‖ ^ 2 =
      ∫ x in {x : ℂ | ‖x - p‖ ∈ Ico η α}, ‖gradient H₁ x‖ ^ 2 := fun η => by
    simp only [norm_gradient_shift]
    exact integral_shift_norm_set (fun x => ‖gradient H₁ x‖ ^ 2) p _
  have e2 : ∫ x in Metric.ball (0 : ℂ) α, ‖gradient (fun z => u (z + p)) x‖ ^ 2 =
      ∫ x in Metric.ball p α, ‖gradient u x‖ ^ 2 := by
    simp only [norm_gradient_shift]
    exact integral_shift_ball (fun x => ‖gradient u x‖ ^ 2) p α
  have e3 : ∫ x in Metric.ball (0 : ℂ) α, truncLog α x * ϱ (x + p) =
      ∫ x in Metric.ball p α, truncLog α (x - p) * ϱ x := by
    have := integral_shift_ball (fun x => truncLog α (x - p) * ϱ x) p α
    simpa using this
  simp only [e1, e2, e3] at key
  exact key

end Sphere

end SandierSerfaty

end
