/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.EvalSound

/-!
# Soundness of the row loops (integer level)

`outerLoop_sound`, `negLoop_sound`: if a row loop returns `true`, there are values `v j` (the midpoint values
`midVal … (k + j) = some (v j)`) such that the exact integer accumulators satisfy the tests:

* outer: at every node `i ≤ n` outside the hole, `thr ≤ 2 (acc + ∑_{j<i} (sm(k+j+1) - sm(k+j)) · (v j).v.toInt)`;
* negative part: `acc + ∑_{j<n} (sm(k+j+1) - sm(k+j)) · max 0 (-(v j).v.toInt) ≤ thr`.

The cast to the real numbers `Q = ∑ (σ_{j+1} - σ_j) v_j` is done in `Box.Outer`/`Box.Negative`.
-/

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query

theorem nodeOK_iff {thr : SInt} {skip : Bool} {acc : SInt} (h : nodeOK thr skip acc = true) :
    skip = true ∨ thr.toInt ≤ 2 * acc.toInt := by
  unfold nodeOK at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have := (SInt.ble_iff _ _).1 h
    rw [SInt.toInt_mulNat] at this
    push_cast at this
    linarith

theorem widthM_cast {sm : ℕ → ℕ} {k : ℕ} (h : sm k ≤ sm (k + 1)) :
    (widthM sm k : ℤ) = (sm (k + 1) : ℤ) - sm k := by
  unfold widthM
  exact Nat.cast_sub h

theorem toInt_step (acc : SInt) (w : ℕ) (x : SInt) :
    (SInt.add acc (SInt.mul ⟨false, w⟩ x)).toInt = acc.toInt + (w : ℤ) * x.toInt := by
  rw [SInt.toInt_add, SInt.toInt_mul]
  rfl

/-- **Soundness of the outer row.** -/
theorem outerLoop_sound (E : EvalData) (idx : ℕ → ℕ) (dm : ℕ) (sm : ℕ → ℕ) (thr : SInt) (inRow : Bool)
    (kl kr : ℕ) : ∀ n k acc, outerLoop E idx dm sm thr inRow kl kr n k acc = true →
    ∃ v : ℕ → Fx 128, (∀ j < n, midVal E idx dm sm (k + j) = some (v j) ∧ sm (k + j) ≤ sm (k + j + 1)) ∧
      ∀ i ≤ n, skipB inRow kl kr (k + i) = true ∨
        thr.toInt ≤ 2 * (acc.toInt + ∑ j ∈ Finset.range i,
          ((sm (k + j + 1) : ℤ) - sm (k + j)) * (v j).v.toInt) := by
  intro n
  induction n with
  | zero =>
    intro k acc h
    refine ⟨fun _ => default, fun j hj => absurd hj (by omega), fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    simp only [outerLoop] at h
    simpa using nodeOK_iff h
  | succ n ih =>
    intro k acc h
    simp only [outerLoop, Bool.and_eq_true] at h
    obtain ⟨⟨hn, hm⟩, hrest⟩ := h
    have hm' : sm k ≤ sm (k + 1) := Nat.le_of_ble_eq_true hm
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at hrest
    | some w =>
      simp only [hv] at hrest
      obtain ⟨v', hv', hnodes⟩ := ih (k + 1) _ hrest
      refine ⟨fun j => match j with | 0 => w | j' + 1 => v' j', ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact ⟨by simpa using hv, by simpa using hm'⟩
        | succ j' =>
          have := hv' j' (by omega)
          have e : k + (j' + 1) = k + 1 + j' := by omega
          simp only [e]
          exact this
      · intro i hi
        cases i with
        | zero =>
          have := nodeOK_iff hn
          simpa using this
        | succ i' =>
          have := hnodes i' (by omega)
          have e : k + (i' + 1) = k + 1 + i' := by omega
          rw [e]
          rcases this with h1 | h1
          · exact Or.inl h1
          · refine Or.inr ?_
            rw [toInt_step, widthM_cast hm'] at h1
            rw [Finset.sum_range_succ']
            have : ∑ j ∈ Finset.range i', ((sm (k + 1 + j + 1) : ℤ) - sm (k + 1 + j)) * (v' j).v.toInt =
                ∑ j ∈ Finset.range i', ((sm (k + (j + 1) + 1) : ℤ) - sm (k + (j + 1))) * (v' j).v.toInt := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [show k + (j + 1) = k + 1 + j by omega]
            rw [this] at h1
            simp only [Nat.add_zero]
            linarith

/-- **Soundness of the negative-part row.** -/
theorem negLoop_sound (E : EvalData) (idx : ℕ → ℕ) (dm : ℕ) (sm : ℕ → ℕ) (thr : SInt) :
    ∀ n k acc, negLoop E idx dm sm thr n k acc = true →
    ∃ v : ℕ → Fx 128, (∀ j < n, midVal E idx dm sm (k + j) = some (v j) ∧ sm (k + j) ≤ sm (k + j + 1)) ∧
      acc.toInt + ∑ j ∈ Finset.range n,
        ((sm (k + j + 1) : ℤ) - sm (k + j)) * max 0 (-(v j).v.toInt) ≤ thr.toInt := by
  intro n
  induction n with
  | zero =>
    intro k acc h
    refine ⟨fun _ => default, fun j hj => absurd hj (by omega), ?_⟩
    simp only [negLoop] at h
    simpa using (SInt.ble_iff _ _).1 h
  | succ n ih =>
    intro k acc h
    simp only [negLoop, Bool.and_eq_true] at h
    obtain ⟨hm, hrest⟩ := h
    have hm' : sm k ≤ sm (k + 1) := Nat.le_of_ble_eq_true hm
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at hrest
    | some w =>
      simp only [hv] at hrest
      obtain ⟨v', hv', hsum⟩ := ih (k + 1) _ hrest
      refine ⟨fun j => match j with | 0 => w | j' + 1 => v' j', ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact ⟨by simpa using hv, by simpa using hm'⟩
        | succ j' =>
          have := hv' j' (by omega)
          have e : k + (j' + 1) = k + 1 + j' := by omega
          simp only [e]
          exact this
      · have hneg : (negPart w).toInt = max 0 (-w.v.toInt) := by
          unfold negPart
          rw [SInt.toInt_max, SInt.toInt_neg]
          rfl
        rw [toInt_step, widthM_cast hm', hneg] at hsum
        rw [Finset.sum_range_succ']
        have : ∑ j ∈ Finset.range n, ((sm (k + 1 + j + 1) : ℤ) - sm (k + 1 + j)) * max 0 (-(v' j).v.toInt) =
            ∑ j ∈ Finset.range n, ((sm (k + (j + 1) + 1) : ℤ) - sm (k + (j + 1))) * max 0 (-(v' j).v.toInt) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show k + (j + 1) = k + 1 + j by omega]
        rw [this] at hsum
        simp only [Nat.add_zero]
        linarith

end SandierSerfaty.Certificate.Box
