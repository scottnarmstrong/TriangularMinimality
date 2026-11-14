/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartAgg

/-!
# The lower bound for one chart (sphere note, Theorem 6.14, per-chart form)

`Lower.chart_lower_step`: from the per-square bound of Proposition 6.13 on the good squares and the partition lemma,
`c_* #inner - (C₁ + |c_*|) #rest - ∑_{cells} err - π ∑ log₊ ≤ W_{B(0,ρ)}(H) + π ∑ log λ`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The error attached to a quantized square in Proposition 6.13 (with `ℓ = ℓ̃ = L`). -/
@[expose] noncomputable def cellErr {n : ℕ} (X : Fin n → ℂ) (L C ε δ : ℝ) (a : ℂ) (t : ℝ) (nb : ℕ)
    (v : ℂ → ℝ) : ℝ :=
  C * (stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t L + t * L +
      |(nb : ℝ) - (ptsIn X a t).card| + (ptsIn X a t).card * δ + t) +
    ε / 2 * (∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) +
    C / ε * ∫ x in sqAt a t, ‖gradC v x‖ ^ 2

theorem stripEnergy_nonneg (u : ℂ → ℝ) (a : ℂ) (t ℓt : ℝ) : 0 ≤ stripEnergy u a t ℓt :=
  setIntegral_nonneg ((measurableSet_sqShrink _ _ _).diff (measurableSet_sqShrink _ _ _))
    fun x _ => by positivity

theorem cellErr_nonneg {n : ℕ} (X : Fin n → ℂ) {L C ε δ : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hε : 0 < ε)
    (hδ : 0 ≤ δ) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) (nb : ℕ) (v : ℂ → ℝ) : 0 ≤ cellErr X L C ε δ a t nb v := by
  unfold cellErr
  have h1 := stripEnergy_nonneg (fun y => truncPot X (1 / 4) y - v y) a t L
  have h2 : 0 ≤ ∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_sqAt a t) fun x _ => by positivity
  have h3 : 0 ≤ ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_sqAt a t) fun x _ => by positivity
  have h4 : (0 : ℝ) ≤ ((ptsIn X a t).card : ℝ) := Nat.cast_nonneg _
  positivity

theorem chart_lower_step {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (h : ChartCtx n X ρ) (hR : 0 < R)
    {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ} (ht1 : ∀ j ∈ cellFin R θ ρ, 0 ≤ t j)
    (ht2 : ∀ j ∈ cellFin R θ ρ, t j ≤ R - 1 / 2) {Good : Finset (ℤ × ℤ)} (hG : Good ⊆ cellFin R θ ρ)
    {L C ε δ : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hgood : ∀ j ∈ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) * cStar ≤
      fnQ X (cellAt R θ j) (t j) + chartSum X (cellAt R θ j) (t j) +
        cellErr X L C ε δ (cellAt R θ j) (t j) (nb j) (v j)) :
    cStar * ((innerBlown X ρ).card : ℝ) -
      (constC1 + |cStar|) * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
        ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)).card : ℝ) -
      ∑ j ∈ cellFin R θ ρ, cellErr X L C ε δ (cellAt R θ j) (t j) (nb j) (v j) -
      Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
    punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
      Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ), Real.log (lam (X i)) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos h.one_le
  have hsq : ∀ j ∈ Good, ∀ x ∈ sqAt (cellAt R θ j) (t j), ‖x‖ ≤ ρ - 1 := fun j hj x hx =>
    sqAt_cell_norm_le h hR (hG hj) (by linarith [ht2 j (hG hj)]) hx
  have hdisj : ∀ j ∈ Good, ∀ j' ∈ Good, j ≠ j' →
      Disjoint (sqAt (cellAt R θ j) (t j)) (sqAt (cellAt R θ j') (t j')) := fun j hj j' hj' hne =>
    sqAt_disjoint hR θ hne (by linarith [ht2 j (hG hj)]) (by linarith [ht2 j' (hG hj')])
  have hpart := chart_partition_lower h.pos X h.inj h.sep hρ0 h.le h.ne Good (fun j => cellAt R θ j) t hsq hdisj
  have hcount := sum_card_ptsIn_add_card_rest X h.injz hR h.one_le t ht2 Good hG
  have hinner : ((innerBlown X ρ).card : ℝ) =
      ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) := by
    rw [card_innerBlown h.pos X h.inj ρ]
  set rest : ℝ := ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
      ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)).card : ℝ) with hrest
  have hrest0 : 0 ≤ rest := Nat.cast_nonneg _
  -- sum of the good square bounds
  have hs1 : ∑ j ∈ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) * cStar ≤
      ∑ j ∈ Good, (fnQ X (cellAt R θ j) (t j) + chartSum X (cellAt R θ j) (t j) +
        cellErr X L C ε δ (cellAt R θ j) (t j) (nb j) (v j)) := Finset.sum_le_sum hgood
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib] at hs1
  have hs2 : ∑ j ∈ Good, cellErr X L C ε δ (cellAt R θ j) (t j) (nb j) (v j) ≤
      ∑ j ∈ cellFin R θ ρ, cellErr X L C ε δ (cellAt R θ j) (t j) (nb j) (v j) :=
    Finset.sum_le_sum_of_subset_of_nonneg hG fun j hj _ =>
      cellErr_nonneg X hL hC hε hδ _ (ht1 j hj) _ _
  have hcs : cStar * rest ≤ |cStar| * rest := mul_le_mul_of_nonneg_right (le_abs_self _) hrest0
  have e : (∑ j ∈ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ)) * cStar =
      cStar * ∑ j ∈ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) := mul_comm _ _
  have e2 : cStar * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) =
      cStar * ∑ j ∈ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) + cStar * rest := by
    rw [← mul_add, ← hcount]
  rw [hinner]
  rw [Finset.sum_add_distrib] at hpart
  linarith [hpart, hs1, hs2, hcs, e, e2]

end Lower

end Sphere

end SandierSerfaty

end
