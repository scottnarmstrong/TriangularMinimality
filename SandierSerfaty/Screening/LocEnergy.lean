/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Monotonicity

/-!
# Lemma 4.13 in field form: the exact identity (I2)

`locEnergy_eq_add_truncInteraction`: `G_D(β) = G_D(α) + truncInteraction C α β` ([Serfaty, *Lectures on Coulomb and Riesz gases*, Lemma 4.13];
the comparison note's Proposition `prop:mono`), with the equation assumed only in `U`, all
points of `C` truncated (also those outside `U` or `D`), overlapping balls allowed, and only the
changed balls required to lie in `U ∩ D`. `locEnergy_le`: `G_D(β) ≤ G_D(α)`.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal ContDiff Real

public section

namespace SandierSerfaty

namespace Screening

theorem coe_ennreal_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ((ENNReal.ofReal r : ℝ≥0∞) : EReal) = r := by
  rw [EReal.coe_ennreal_ofReal, max_eq_left hr]

end Screening

open Screening in
/-- **I2: Lemma 4.13 in field form, exact.** -/
theorem locEnergy_eq_add_truncInteraction {D U : Set ℂ} (hU : IsOpen U) (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {m : ℝ} {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    {E : ℂ → ℂ} (hE : IsChargeField U m C E) {α β : ℂ → ℝ} (hα : ∀ p ∈ C, 0 < α p)
    (hαβ : ∀ p ∈ C, α p ≤ β p) (hβb : ∃ M, ∀ p ∈ C, β p ≤ M)
    (hball : ∀ p ∈ C, α p < β p → closedBall p (β p) ⊆ U ∩ D)
    (hL2 : ∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≠ ⊤) :
    locEnergy m C β E D = locEnergy m C α E D + ((truncInteraction C α β : ℝ) : EReal) := by
  obtain ⟨M0, hM0⟩ := hβb
  set M := max M0 0 with hMdef
  have hβM : ∀ p ∈ C, β p ≤ M := fun p hp => (hM0 p hp).trans (le_max_left _ _)
  have hαM : ∀ p ∈ C, α p ≤ M := fun p hp => (hαβ p hp).trans (hβM p hp)
  have hM0' : 0 ≤ M := le_max_right _ _
  have hβ : ∀ p ∈ C, 0 < β p := fun p hp => (hα p hp).trans_le (hαβ p hp)
  obtain ⟨R, hR⟩ := hDb.subset_closedBall 0
  set I : Set ℂ := {p ∈ C | α p < β p} with hIdef
  have hID : ∀ p ∈ I, p ∈ D := fun p hp =>
    ((hball p hp.1 hp.2) (mem_closedBall_self (hβ p hp.1).le)).2
  have hIfin : I.Finite := (hC R).subset fun p hp => ⟨hp.1, hR (hID p hp)⟩
  set IF := hIfin.toFinset with hIFdef
  have hIF : ∀ p, p ∈ IF ↔ p ∈ C ∧ α p < β p := fun p => hIfin.mem_toFinset
  have hIC : ∀ i ∈ IF, i ∈ C := fun i hi => ((hIF i).1 hi).1
  have hIlt : ∀ i ∈ IF, α i < β i := fun i hi => ((hIF i).1 hi).2
  set Q := (hC (R + M)).toFinset with hQdef
  have hQC : ∀ q ∈ Q, q ∈ C := fun q hq => mem_of_mem_toFinset _ hq
  have hIQ : IF ⊆ Q := fun i hi => (hC (R + M)).mem_toFinset.2 ⟨hIC i hi,
    mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1
      (hR (hID i ((hIF i).1 hi)))).trans (by linarith))⟩
  set F : ℂ → ℂ → ℝ := fun i y => truncDiff (α i) (β i) (y - i) with hFdef
  set B : Set ℂ := ⋃ i ∈ IF, closedBall i (β i) with hBdef
  have hBc : IsCompact B := IF.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hBUD : B ⊆ U ∩ D := iUnion₂_subset fun i hi => hball i (hIC i hi) (hIlt i hi)
  set gF : ℂ → ℂ := fun x => ∑ i ∈ IF, gradient (F i) x with hgFdef
  -- the truncated fields differ only on `B`, by `gF` a.e.
  have heq := truncField_eq_add hC hα hαβ hβM E hIF
  have hout : ∀ x ∉ B, truncField C β E x = truncField C α E x := by
    intro x hx
    rw [heq x, Finset.sum_eq_zero, add_zero]
    intro i hi
    have hxi : β i < ‖x - i‖ := by
      by_contra h
      exact hx (mem_iUnion₂.2 ⟨i, hi, mem_closedBall.2 (by rw [dist_eq_norm]; linarith)⟩)
    rw [gradient_truncLog_of_gt (hα i (hIC i hi)) (by linarith [hαβ i (hIC i hi)]),
      gradient_truncLog_of_gt (hβ i (hIC i hi)) hxi, sub_zero]
  have hae : truncField C β E =ᵐ[volume] fun x => truncField C α E x + gF x := by
    have h := (Filter.eventually_all_finset IF).2 fun i hi =>
      ae_gradient_truncDiff_sub (hα i (hIC i hi)) (hαβ i (hIC i hi)) i
    filter_upwards [h] with x hx
    rw [heq x]
    exact congrArg _ (Finset.sum_congr rfl fun i hi => (hx i hi).symm)
  have hgFm : AEStronglyMeasurable gF volume :=
    (Finset.measurable_sum IF fun i _ => measurable_gradient (F i)).aestronglyMeasurable
  have hgFc : ∀ x, ‖gF x‖ ≤ ∑ i ∈ IF, (α i)⁻¹ := fun x =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
      norm_gradient_truncDiff_sub_le (hα i (hIC i hi)) (hαβ i (hIC i hi)) i x)
  have hgF0 : ∀ x ∉ B, gF x = 0 := fun x hx => Finset.sum_eq_zero fun i hi =>
    gradient_truncDiff_sub_eq_zero fun h => hx (mem_iUnion₂.2 ⟨i, hi, h⟩)
  obtain ⟨r, hr0, hrX, hLα, hLβ⟩ := lintegral_norm_sq_perturb hD hBc.measurableSet
    (hBUD.trans inter_subset_right) hBc.measure_lt_top.ne
    (integrableOn_truncField hC hE.1 hα ⟨M, hαM⟩ hBc (hBUD.trans inter_subset_left)) hL2 hgFm
    hgFc hgF0 hout hae
  have hX := integral_inner_truncField_sum_gradient hU hC hE hα hαβ hβM hIC
    (fun i hi => (hball i (hIC i hi) (hIlt i hi)).trans inter_subset_left)
  have hY := integral_norm_sq_sum_gradient (fun i hi => hα i (hIC i hi))
    (fun i hi => hαβ i (hIC i hi))
  simp only [hgFdef, hFdef] at hrX hLβ
  rw [hX, hY] at hrX hLβ
  -- reduce to a real identity
  unfold locEnergy
  rw [hLα, hLβ, coe_ennreal_ofReal_of_nonneg hr0, coe_ennreal_ofReal_of_nonneg hrX]
  norm_cast
  -- the circle averages
  have hFfar : ∀ i ∈ IF, ∀ x, R < ‖x‖ → truncDiff (α i) (β i) (x - i) = 0 := fun i hi x hx =>
    truncDiff_sub_eq_zero_of_far fun h => absurd (mem_closedBall_zero_iff.1
      (hR ((hball i (hIC i hi) (hIlt i hi)) h).2)) (not_le.2 hx)
  have hfarQ : ∀ q ∈ C, q ∉ Q → R + M < ‖q‖ := fun q hq hqQ => lt_norm_of_notMem_toFinset _ hq hqQ
  have havg_far : ∀ i ∈ IF, ∀ q ∈ C, q ∉ Q → ∀ r, 0 < r → r ≤ M → avgF α β i q r = 0 :=
    fun i hi q hq hqQ r hr hrM => circleAverage_far (hFfar i hi) hr hrM (hfarQ q hq hqQ)
  have hXeq : (∑ i ∈ IF, 2 * π * ((∑ᶠ q ∈ C, avgF α β i q (α q)) -
      m * (π * (α i ^ 2 - β i ^ 2) / 2))) = ∑ i ∈ IF, 2 * π * ((∑ q ∈ Q, avgF α β i q (α q)) -
      m * (π * (α i ^ 2 - β i ^ 2) / 2)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [finsum_mem_eq_finsetSum hQC fun q hq hqQ =>
      havg_far i hi q hq hqQ _ (hα q hq) (hαM q hq)]
  -- the self-energy terms
  have hCD : (C ∩ D).Finite := (hC R).subset fun p hp => ⟨hp.1, hR hp.2⟩
  have htau : (∑ᶠ p ∈ C ∩ D, tauM m (β p)) - ∑ᶠ p ∈ C ∩ D, tauM m (α p) =
      ∑ i ∈ IF, (tauM m (β i) - tauM m (α i)) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hCD, finsum_mem_eq_finite_toFinset_sum _ hCD,
      ← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (fun i hi => hCD.mem_toFinset.2 ⟨hIC i hi, hID i ((hIF i).1 hi)⟩)
      fun p hp hpI => ?_).symm
    have hpC := (hCD.mem_toFinset.1 hp).1
    have : α p = β p := le_antisymm (hαβ p hpC) (not_lt.1 fun h' => hpI ((hIF p).2 ⟨hpC, h'⟩))
    rw [this, sub_self]
  -- the interaction
  have hint : truncInteraction C α β =
      π * ∑ i ∈ IF, ∑ q ∈ Q.erase i, (avgF α β i q (α q) + avgF α β i q (β q)) := by
    unfold truncInteraction
    rw [finsum_mem_eq_finite_toFinset_sum _ hIfin]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hαi := hα i (hIC i hi)
    have hαβi := hαβ i (hIC i hi)
    calc (∑ᶠ q ∈ C \ {i}, (Real.circleAverage (fun x => truncLog (α i) (x - i) -
            truncLog (β i) (x - i)) q (α q) + Real.circleAverage (fun x => truncLog (α i) (x - i) -
            truncLog (β i) (x - i)) q (β q)))
        = ∑ᶠ q ∈ C \ {i}, (avgF α β i q (α q) + avgF α β i q (β q)) :=
          finsum_mem_congr rfl fun q hq => by
            rw [circleAverage_truncLog_sub_eq hαi hαβi i q (hα q hq.1).ne',
              circleAverage_truncLog_sub_eq hαi hαβi i q (hβ q hq.1).ne']
            rfl
      _ = ∑ q ∈ Q.erase i, (avgF α β i q (α q) + avgF α β i q (β q)) := by
          refine finsum_mem_eq_finsetSum (C := C \ {i}) (S := Q.erase i) (fun q hq =>
            ⟨hQC q (Finset.mem_of_mem_erase hq), Finset.ne_of_mem_erase hq⟩) fun q hq hqQ => ?_
          have hqQ' : q ∉ Q := fun h => hqQ (Finset.mem_erase.2 ⟨hq.2, h⟩)
          rw [havg_far i hi q hq.1 hqQ' _ (hα q hq.1) (hαM q hq.1),
            havg_far i hi q hq.1 hqQ' _ (hβ q hq.1) (hβM q hq.1), add_zero]
  have halg := interaction_algebra hIQ α β m (fun i q => avgF α β i q (α q))
    (fun i q => avgF α β i q (β q))
    (fun i hi q hq hqI => by
      have hqC := hQC q hq
      have : α q = β q := le_antisymm (hαβ q hqC) (not_lt.1 fun h' => hqI ((hIF q).2 ⟨hqC, h'⟩))
      simp only [this])
    (fun i hi => circleAverage_truncDiff_self_α (hα i (hIC i hi)) (hαβ i (hIC i hi)) i)
    (fun i hi => circleAverage_truncDiff_self_β (hα i (hIC i hi)) (hαβ i (hIC i hi)) i)
  rw [hXeq, hint, ← halg]
  linarith [htau]

open Screening in
/-- **Monotonicity in the truncation radii** (book Lemma 4.13): `G_D(β) ≤ G_D(α)`. -/
theorem locEnergy_le {D U : Set ℂ} (hU : IsOpen U) (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {m : ℝ} {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    {E : ℂ → ℂ} (hE : IsChargeField U m C E) {α β : ℂ → ℝ} (hα : ∀ p ∈ C, 0 < α p)
    (hαβ : ∀ p ∈ C, α p ≤ β p) (hβb : ∃ M, ∀ p ∈ C, β p ≤ M)
    (hball : ∀ p ∈ C, α p < β p → closedBall p (β p) ⊆ U ∩ D) :
    locEnergy m C β E D ≤ locEnergy m C α E D := by
  by_cases hL2 : ∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) = ⊤
  · have : locEnergy m C α E D = ⊤ := by
      unfold locEnergy
      rw [hL2, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num), EReal.top_add_coe]
    rw [this]; exact le_top
  · rw [locEnergy_eq_add_truncInteraction hU hD hDb hC hE hα hαβ hβb hball hL2]
    have h := truncInteraction_nonpos C α β hα hαβ
    calc locEnergy m C α E D + ((truncInteraction C α β : ℝ) : EReal)
        ≤ locEnergy m C α E D + ((0 : ℝ) : EReal) := add_le_add_right (EReal.coe_le_coe_iff.2 h) _
      _ = locEnergy m C α E D := by rw [EReal.coe_zero, add_zero]

end SandierSerfaty

end
