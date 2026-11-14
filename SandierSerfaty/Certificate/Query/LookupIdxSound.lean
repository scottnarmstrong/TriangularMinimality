/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.LookupIdx
public import SandierSerfaty.Certificate.Query.LookupSound

/-!
# Soundness of the checked-index lookup

For a table realized by real nodes (`ITable.Encl`) and a passing coverage check `coverOK T X i0 i1`:

* `exists_cell_idx`: every `t ∈ X` with `b ≤ t < l` lies in a right cell `[a_i, a_{i+1})` with `i0 ≤ i ≤ i1`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Calibration

theorem ITable.Encl.mono_le {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) :
    ∀ j, j ≤ T.n → ∀ i, i ≤ j → a i ≤ a j := by
  intro j
  induction j with
  | zero => intro _ i hi; obtain rfl : i = 0 := by omega
            exact le_rfl
  | succ j ih =>
    intro hj i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with h1 | h1
    · exact (ih (by omega) i (by omega)).trans (h.mono j (by omega))
    · rw [h1]

/-- A cell of the table with `t ∈ [a_i, a_{i+1})` for `t ∈ [b, l)` (as `Box.exists_right_cell_of_encl`, which lives
downstream of this module). -/
theorem ITable.Encl.exists_right_cell {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {t : ℝ}
    (ht : t ∈ Ico Calibration.b Calibration.l) : ∃ i, i < T.n ∧ a i ≤ t ∧ t < a (i + 1) := by
  classical
  have hn : 0 < T.n := by
    by_contra hn0
    have hn0' : T.n = 0 := by omega
    have := h.last
    rw [hn0', h.first] at this
    have hbl : Calibration.b < Calibration.l :=
      Calibration.b_lt_p.trans (Calibration.p_lt_R₀.trans Calibration.R₀_lt_l)
    linarith
  have h0 : a 0 ≤ t := by rw [h.first]; exact ht.1
  have hy : t < a T.n := by rw [h.last]; exact ht.2
  set j := Nat.findGreatest (fun i => a i ≤ t) (T.n - 1) with hj
  have hsp : a j ≤ t := Nat.findGreatest_spec (P := fun i => a i ≤ t) (Nat.zero_le _) h0
  have hjn : j ≤ T.n - 1 := Nat.findGreatest_le _
  refine ⟨j, by omega, hsp, ?_⟩
  rcases Nat.lt_or_ge j (T.n - 1) with h' | h'
  · have := Nat.findGreatest_is_greatest (P := fun i => a i ≤ t) (show j < j + 1 by omega)
      (by omega : j + 1 ≤ T.n - 1)
    exact not_le.1 this
  · have : j + 1 = T.n := by omega
    rw [this]; exact hy

/-- The hull of the cells `i, …, i + k` encloses `x` if the cell `i'` in that range does. -/
theorem hullCells_mem {T : ITable} {x : ℝ} {proj : Tup → IV 128}
    (hh : ∀ a b, proj (hullTup a b) = IV.hull (proj a) (proj b)) :
    ∀ (k i i' : ℕ), i ≤ i' → i' ≤ i + k → IV.Mem x (proj (T.cell i')) →
      IV.Mem x (proj (hullCells T i k))
  | 0, i, i', h1, h2, hx => by
    obtain rfl : i' = i := by omega
    exact hx
  | k + 1, i, i', h1, h2, hx => by
    simp only [hullCells]
    rw [hh]
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact IV.mem_hull_left hx
    · exact IV.mem_hull_right (hullCells_mem hh k (i + 1) i' h (by omega) hx)

theorem lookupIdx_some {T : ITable} {X : IV 128} {i0 i1 : ℕ} {c : Tup} (h : lookupIdx T X i0 i1 = some c) :
    coverOK T X i0 i1 = true ∧ c = hullCells T i0 (i1 - i0) := by
  unfold lookupIdx at h
  cases hc : coverOK T X i0 i1
  · simp [hc] at h
  · simp only [hc, Bool.cond_true, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩

theorem coverOK_iff {T : ITable} {X : IV 128} {i0 i1 : ℕ} (h : coverOK T X i0 i1 = true) :
    i0 ≤ i1 ∧ i1 < T.n ∧ (i0 = 0 ∨ SInt.ble (T.node i0).hi X.lo = true) ∧
      (i1 + 1 = T.n ∨ SInt.blt X.hi (T.node (i1 + 1)).lo = true) := by
  unfold coverOK at h
  cases h1 : Nat.ble i0 i1
  · simp [h1] at h
  cases h2 : Nat.blt i1 T.n
  · simp [h1, h2] at h
  cases h3 : coverLo T X i0
  · simp [h1, h2, h3] at h
  simp only [h1, h2, h3, Bool.cond_true] at h
  refine ⟨Nat.ble_eq.mp h1, Nat.blt_eq.mp h2, ?_, ?_⟩
  · unfold coverLo at h3
    cases h4 : Nat.beq i0 0
    · simp only [h4, Bool.cond_false] at h3; exact Or.inr h3
    · exact Or.inl (Nat.eq_of_beq_eq_true h4)
  · unfold coverHi at h
    cases h4 : Nat.beq (i1 + 1) T.n
    · simp only [h4, Bool.cond_false] at h; exact Or.inr h
    · exact Or.inl (Nat.eq_of_beq_eq_true h4)

/-- **The index range covers the cell of `t`**: a right cell `[a_i, a_{i+1})` with `i ∈ [i0, i1]`. -/
theorem exists_cell_idx {T : ITable} {a : ℕ → ℝ} (H : T.Encl a) {X : IV 128} {i0 i1 : ℕ}
    (hc : coverOK T X i0 i1 = true) {t : ℝ} (ht : t ∈ Ico Calibration.b Calibration.l) (hX : IV.Mem t X) :
    ∃ i, i0 ≤ i ∧ i ≤ i1 ∧ a i ≤ t ∧ t < a (i + 1) := by
  obtain ⟨hi01, hi1n, hlo, hhi⟩ := coverOK_iff hc
  obtain ⟨i, hi, hat, hta⟩ := H.exists_right_cell ht
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  refine ⟨i, ?_, ?_, hat, hta⟩
  · by_contra hlt
    have hlt : i + 1 ≤ i0 := by omega
    have h0 : i0 ≠ 0 := by omega
    have hle := (hlo.resolve_left h0)
    simp only [SInt.ble_iff] at hle
    have h1 : ((((T.node i0).hi.toInt : ℤ)) : ℝ) ≤ ((X.lo.toInt : ℤ) : ℝ) := by exact_mod_cast hle
    have h2 := (H.node i0 (by omega)).2
    have h3 := hX.1
    have h4 : a i0 * 2 ^ 128 ≤ t * 2 ^ 128 := by linarith
    have h5 : a i0 ≤ t := le_of_mul_le_mul_right h4 hN
    have h6 := H.mono_le i0 (by omega) (i + 1) hlt
    linarith
  · by_contra hgt
    have hgt : i1 + 1 ≤ i := by omega
    have hne : i1 + 1 ≠ T.n := by omega
    have hlt := hhi.resolve_left hne
    simp only [SInt.blt, Bool.not_eq_true'] at hlt
    have hlt' : ¬ ((T.node (i1 + 1)).lo.toInt ≤ X.hi.toInt) := by
      rw [← SInt.ble_iff]; simpa using hlt
    have h1 : ((X.hi.toInt : ℤ) : ℝ) < (((T.node (i1 + 1)).lo.toInt : ℤ) : ℝ) := by
      exact_mod_cast not_le.1 hlt'
    have h2 := (H.node (i1 + 1) (by omega)).1
    have h3 := hX.2
    have h4 : t * 2 ^ 128 < a (i1 + 1) * 2 ^ 128 := by linarith
    have h5 : t < a (i1 + 1) := lt_of_mul_lt_mul_right h4 hN.le
    have h6 := H.mono_le i (by omega) (i1 + 1) hgt
    linarith

end SandierSerfaty.Certificate.Query
