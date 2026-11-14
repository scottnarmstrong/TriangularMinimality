/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Complex.Basic

/-!
# Counting separated points (sphere note, Lemma 6.5)

If `|p - q| ≥ 1` for distinct `p, q ∈ S`, then for every `A ⊆ ℂ`, `#(S ∩ A) · π/4 ≤ |A + B(0, ½)|`.
The discs `B(p, ½)`, `p ∈ S ∩ A`, are disjoint and contained in `A + B(0, ½)`.
-/

open MeasureTheory Metric
open scoped ENNReal Pointwise Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- **Lemma 6.5 (counting separated points)**, in `ℝ≥0∞` form. -/
theorem card_filter_mul_le_volume {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖)
    (A : Set ℂ) :
    ((S.filter (· ∈ A)).card : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 4) ≤
      volume (A + ball (0 : ℂ) (1 / 2)) := by
  classical
  set T := S.filter (· ∈ A) with hT
  have hmeas : ∀ p ∈ T, MeasurableSet (ball p (1 / 2 : ℝ)) := fun p _ => measurableSet_ball
  have hdisj : (↑T : Set ℂ).Pairwise (Function.onFun Disjoint fun p => ball p (1 / 2 : ℝ)) := by
    intro p hp q hq hpq
    have hp' := (Finset.mem_filter.1 hp).1
    have hq' := (Finset.mem_filter.1 hq).1
    rw [Function.onFun, Set.disjoint_left]
    intro x hxp hxq
    have h1 : ‖p - q‖ < 1 := by
      calc ‖p - q‖ = dist p q := (dist_eq_norm p q).symm
        _ ≤ dist p x + dist x q := dist_triangle p x q
        _ < 1 / 2 + 1 / 2 := by
          have := mem_ball.1 hxp
          have := mem_ball.1 hxq
          rw [dist_comm p x]
          linarith
        _ = 1 := by norm_num
    exact absurd (hS p hp' q hq' hpq) (not_le.2 h1)
  have hsub : (⋃ p ∈ T, ball p (1 / 2 : ℝ)) ⊆ A + ball (0 : ℂ) (1 / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    refine Set.mem_add.2 ⟨p, (Finset.mem_filter.1 hp).2, x - p, ?_, by ring⟩
    simpa [dist_eq_norm] using hxp
  calc ((T.card : ℝ≥0∞)) * ENNReal.ofReal (Real.pi / 4)
      = ∑ p ∈ T, volume (ball p (1 / 2 : ℝ)) := by
        rw [Finset.sum_congr rfl (fun p _ => Complex.volume_ball p (1 / 2))]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        have h2 : (ENNReal.ofReal (1 / 2) : ℝ≥0∞) ^ 2 = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_pow (by norm_num)]
          norm_num
        rw [h2, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    _ = volume (⋃ p ∈ T, ball p (1 / 2 : ℝ)) := (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ _ := measure_mono hsub

end Lower

end Sphere

end SandierSerfaty

end
