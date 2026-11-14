/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.A7
public import SandierSerfaty.Certificate.Box.CtxIdxSound

/-!
# The derivative assertion A7 with the checked-index lookup

`derivBounds_of_a7I`: the statement of `derivBounds_of_a7` with the rectangle rows `A7Data.rowI D ix` (the table read
through the proposed index range `ix j k` of each rectangle, verified by the kernel) in place of `A7Data.row`. The
conclusion `DerivBounds` and every other hypothesis are unchanged, so it can replace `derivBounds_of_a7` in the
downstream statements (`Box.Inner`, `Box.NumGoal`); the range function `ix` is untrusted data.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

theorem A7Data.rowI_iff {D : A7Data} {ix : Nat → Nat → Nat × Nat} {j : ℕ} :
    ∀ n, D.rowI ix j n = true ↔ ∀ k < n, D.rectI ix j k = true := by
  intro n
  induction n with
  | zero => simp [A7Data.rowI]
  | succ n ih =>
    simp only [A7Data.rowI, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h1 k h
      · rw [h]; exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

/-- **The pointwise facts of a passing rectangle** (checked-index version of `A7Data.point`). -/
theorem A7Data.pointI (hc : FiniteCore) (D : A7Data) (ix : Nat → Nat → Nat × Nat) {a : ℕ → ℝ} (H : Encl2 D.T a)
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ D.rad) (hl : IV.Mem Calibration.l D.lI)
    (hf0l : IV.Mem (f₀ Calibration.l) D.f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) D.k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) D.lsqI) (hlam : IV.Mem lam D.lamI) (hmu : IV.Mem mu D.muI)
    {dHi xHi : ℝ} (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : dHi ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0) (hspn : xHi ≤ (D.sp D.nk : ℝ) / 2 ^ 128)
    (hrows : ∀ j < D.nj, D.rowI ix j D.nk = true) {d s : ℝ} (hd : d ∈ Icc Calibration.b dHi)
    (hs : s ∈ Icc 0 xHi) :
    ∃ c : DCtx2, DMem2 d s c ∧ absLe (gdOf c.toDCtx) D.L1 = true ∧ absLe (gsOf c.toDCtx) D.L2 = true ∧
      absLe (gddOf c) D.L3 = true ∧ absLe (gssOf c) D.L4 = true := by
  obtain ⟨j, hj, hdj⟩ := exists_cell (a := fun j => (D.dp j : ℝ) / 2 ^ 128) hnj (hdp0.trans hd.1) (hd.2.trans hdpn)
  obtain ⟨k, hk, hsk⟩ := exists_cell (a := fun k => (D.sp k : ℝ) / 2 ^ 128) hnk
    (by simp [hsp0]; exact hs.1) (hs.2.trans hspn)
  have hrect := (A7Data.rowI_iff D.nk).1 (hrows j hj) k hk
  unfold A7Data.rectI at hrect
  cases hix : ix j k with
  | mk i0 i1 =>
    rw [hix] at hrect
    simp only [A7Data.test] at hrect
    cases hm : mkDCtx2I D.T D.f0lI D.k0I D.lsqI D.lI D.lamI D.muI D.rad
        (IV.ofNatPair (D.dp j) (D.dp (Nat.succ j))) (IV.ofNatPair (D.sp k) (D.sp (Nat.succ k))) i0 i1 with
    | none => rw [hm] at hrect; exact absurd hrect (by simp)
    | some c =>
      rw [hm] at hrect
      simp only [Bool.and_eq_true] at hrect
      obtain ⟨⟨r1, r2⟩, r3, r4⟩ := hrect
      have hDd : IV.Mem d (IV.ofNatPair (P := 128) (D.dp j) (D.dp (Nat.succ j))) := mem_ofNatPair hdj.1 hdj.2
      have hSs : IV.Mem s (IV.ofNatPair (P := 128) (D.sp k) (D.sp (Nat.succ k))) := mem_ofNatPair hsk.1 hsk.2
      obtain ⟨-, hmem⟩ := mkDCtx2I_sound hc H hrad hl hf0l hk0 hlsq hlam hmu hm hd.1 hDd hSs
      exact ⟨c, hmem, r1, r2, r3, r4⟩

/-- **A7 with the checked index**: `DerivBounds` from the rectangle checks `A7Data.rowI`. -/
theorem derivBounds_of_a7I (hc : FiniteCore) (D : A7Data) (ix : Nat → Nat → Nat × Nat) {a : ℕ → ℝ}
    (H : Encl2 D.T a) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ D.rad) (hl : IV.Mem Calibration.l D.lI)
    (hf0l : IV.Mem (f₀ Calibration.l) D.f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) D.k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) D.lsqI) (hlam : IV.Mem lam D.lamI) (hmu : IV.Mem mu D.muI)
    {dHi xHi : ℝ} (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : dHi ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0) (hspn : xHi ≤ (D.sp D.nk : ℝ) / 2 ^ 128)
    (hrows : ∀ j < D.nj, D.rowI ix j D.nk = true) :
    DerivBounds Calibration.b dHi xHi ((D.L1 : ℝ) / 2 ^ 128) ((D.L2 : ℝ) / 2 ^ 128) ((D.L3 : ℝ) / 2 ^ 128)
      ((D.L4 : ℝ) / 2 ^ 128) :=
  derivBounds_of_pt D fun _ _ hd hs =>
    A7Data.pointI hc D ix H hrad hl hf0l hk0 hlsq hlam hmu hnj hnk hdp0 hdpn hsp0 hspn hrows hd hs

end SandierSerfaty.Certificate.Box
