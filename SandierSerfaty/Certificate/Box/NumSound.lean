/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumDef
public import SandierSerfaty.Certificate.Box.Outer

/-!
# Soundness of the `Nat`-level numeric checks

The real statements of `NumDef`'s Booleans, in the form used by `Box.certificateGoal_of_data`:

* `allLt_iff`, `monoB_sound`, `stepB_sound` (`sg sm (k + 1) - sg sm k ≤ sh / 2^128`);
* `leLitB_sound`, `geLitB_sound`: comparisons of a node `m / 2^128` with a rational literal `num / den`;
* `closeLoB_sound`, `closeHiB_sound`: the fourth-power closeness facts of a dyadic node to `p`, `x₀`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

theorem bigP_eq : (bigP : ℕ) = 2 ^ 128 := by
  simp [bigP, Nat.shiftLeft_eq]

theorem cast_bigP : ((bigP : ℕ) : ℝ) = 2 ^ 128 := by
  rw [bigP_eq]; norm_cast

theorem allLt_iff {f : ℕ → Bool} {n : ℕ} : allLt f n = true ↔ ∀ j < n, f j = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · exact h1 j h
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

theorem monoB_sound {sm : ℕ → ℕ} {n : ℕ} (h : monoB sm n = true) : ∀ j < n, sm j ≤ sm (j + 1) := by
  intro j hj
  exact Nat.le_of_ble_eq_true ((allLt_iff.1 h) j hj)

theorem stepB_sound {sm : ℕ → ℕ} {n sh : ℕ} (h : stepB sm n sh = true) :
    ∀ k < n, sg sm (k + 1) - sg sm k ≤ (sh : ℝ) / 2 ^ 128 := by
  intro k hk
  have h1 : sm (k + 1) ≤ sm k + sh := Nat.le_of_ble_eq_true ((allLt_iff.1 h) k hk)
  have h2 : (sm (k + 1) : ℝ) ≤ sm k + sh := by exact_mod_cast h1
  unfold sg
  rw [← sub_div, div_le_div_iff_of_pos_right (by positivity)]
  linarith

theorem leLitB_sound {m num den : ℕ} (hd : 0 < den) (h : leLitB m num den = true) :
    (m : ℝ) / 2 ^ 128 ≤ (num : ℝ) / den := by
  have h1 : m * den ≤ num * bigP := Nat.le_of_ble_eq_true h
  have h2 : (m : ℝ) * den ≤ num * ((bigP : ℕ) : ℝ) := by exact_mod_cast h1
  rw [cast_bigP] at h2
  rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hd)]
  exact h2

theorem geLitB_sound {m num den : ℕ} (hd : 0 < den) (h : geLitB m num den = true) :
    (num : ℝ) / den ≤ (m : ℝ) / 2 ^ 128 := by
  have h1 : num * bigP ≤ m * den := Nat.le_of_ble_eq_true h
  have h2 : (num : ℝ) * ((bigP : ℕ) : ℝ) ≤ m * den := by exact_mod_cast h1
  rw [cast_bigP] at h2
  rw [div_le_div_iff₀ (by exact_mod_cast hd) (by positivity)]
  exact h2

theorem subLeB_sound {m num den r : ℕ} (hd : 0 < den) (h : subLeB m num den r = true) :
    (m : ℝ) / 2 ^ 128 - (num : ℝ) / den ≤ (r : ℝ) / 2 ^ 128 := by
  have h1 : m * den ≤ num * bigP + r * den := Nat.le_of_ble_eq_true h
  have h2 : (m : ℝ) * den ≤ num * ((bigP : ℕ) : ℝ) + r * den := by exact_mod_cast h1
  rw [cast_bigP] at h2
  have hd' : (0 : ℝ) < den := by exact_mod_cast hd
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  rw [sub_le_iff_le_add, div_add_div _ _ hN.ne' hd'.ne', div_le_div_iff₀ hN (by positivity)]
  nlinarith

theorem nearB_sound {m num den r : ℕ} (hd : 0 < den) (h : nearB m num den r = true) :
    (m : ℝ) / 2 ^ 128 ≤ (num : ℝ) / den + ((r : ℝ) / 2 ^ 128) / 2 := by
  have h1 : 2 * m * den ≤ 2 * num * bigP + r * den := Nat.le_of_ble_eq_true h
  have h2 : 2 * (m : ℝ) * den ≤ 2 * num * ((bigP : ℕ) : ℝ) + r * den := by exact_mod_cast h1
  rw [cast_bigP] at h2
  have hd' : (0 : ℝ) < den := by exact_mod_cast hd
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  rw [div_div, div_add_div _ _ hd'.ne' (by positivity), div_le_div_iff₀ hN (by positivity)]
  nlinarith

theorem closeLoB_sound {m r q : ℕ} (hq : 0 < q) (h : closeLoB m r q = true) :
    0 ≤ (m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128 ∧ ((m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128) ^ 4 ≤ 1 / q := by
  simp only [closeLoB, Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  have hr : r ≤ m := Nat.le_of_ble_eq_true h0
  have h2 : q * (m - r) ^ 4 ≤ bigP ^ 4 := Nat.le_of_ble_eq_true h1
  have h3 : (q : ℝ) * ((m : ℝ) - r) ^ 4 ≤ (((bigP : ℕ) : ℝ)) ^ 4 := by
    have := (Nat.cast_le (α := ℝ)).2 h2
    push_cast [Nat.cast_sub hr] at this
    exact this
  rw [cast_bigP] at h3
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hrm : (r : ℝ) ≤ m := by exact_mod_cast hr
  have e : (m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128 = ((m : ℝ) - r) / 2 ^ 128 := by ring
  rw [e]
  refine ⟨div_nonneg (by linarith) hN.le, ?_⟩
  rw [div_pow, div_le_div_iff₀ (by positivity) hq']
  linarith

theorem closeHiB_sound {m r q : ℕ} (hq : 0 < q) (h : closeHiB m r q = true) :
    (1 : ℝ) / q ≤ ((m : ℝ) / 2 ^ 128 + (r : ℝ) / 2 ^ 128) ^ 4 := by
  have h2 : bigP ^ 4 ≤ q * (m + r) ^ 4 := Nat.le_of_ble_eq_true h
  have h3 : (((bigP : ℕ) : ℝ)) ^ 4 ≤ (q : ℝ) * ((m : ℝ) + r) ^ 4 := by
    have := (Nat.cast_le (α := ℝ)).2 h2
    push_cast at this
    exact this
  rw [cast_bigP] at h3
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : (m : ℝ) / 2 ^ 128 + (r : ℝ) / 2 ^ 128 = ((m : ℝ) + r) / 2 ^ 128 := by ring
  rw [e, div_pow, div_le_div_iff₀ hq' (by positivity)]
  linarith

end SandierSerfaty.Certificate.Box
