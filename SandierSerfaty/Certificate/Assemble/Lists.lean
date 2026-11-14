/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Assemble.Defs

/-!
# Gluing the shard theorems

Small Mathlib-free lemmas used by the generated aggregators of the opt-in library `SandierSerfatyCert`:

* `forall_lt_zero'`, `forall_lt_succ_of`: a statement `∀ c < N, P c` is built from the shard theorems
  `P 0, …, P (N - 1)` one step at a time;
* `allCells_append_of`: the core test of a concatenation of cell lists (one `decide +kernel` declaration per
  piece);
* `optEqB_sound`: `optEqB o I = true → o = some I` (a computed enclosure stated as a literal).
-/

public section

namespace SandierSerfaty.Certificate.Assemble

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis

theorem forall_lt_zero' {P : Nat → Prop} : ∀ c, c < 0 → P c := fun _ h => absurd h (Nat.not_lt_zero _)

theorem forall_lt_succ_of {P : Nat → Prop} {n : Nat} (h : ∀ c, c < n → P c) (hn : P n) : ∀ c, c < n + 1 → P c :=
  fun c hc => (Nat.lt_succ_iff_lt_or_eq.mp hc).elim (h c) fun e => e ▸ hn

theorem allCells_append_of {d : BasisData} {j : Nat} :
    ∀ {l1 l2 : List (IV 128)}, allCells d j l1 = true → allCells d j l2 = true → allCells d j (l1 ++ l2) = true
  | [], _, _, h2 => h2
  | X :: rest, l2, h1, h2 => by
    simp only [allCells, Bool.and_eq_true] at h1
    simp only [List.cons_append, allCells, Bool.and_eq_true]
    exact ⟨h1.1, allCells_append_of h1.2 h2⟩

theorem sintEqB_eq {a b : SInt} (h : sintEqB a b = true) : a = b := by
  obtain ⟨s, m⟩ := a
  obtain ⟨s', m'⟩ := b
  simp only [sintEqB, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hm : m = m' := Nat.eq_of_beq_eq_true h2
  cases s <;> cases s' <;> simp_all

theorem ivEqB_eq {a b : IV 128} (h : ivEqB a b = true) : a = b := by
  obtain ⟨lo, hi⟩ := a
  obtain ⟨lo', hi'⟩ := b
  simp only [ivEqB, Bool.and_eq_true] at h
  rw [sintEqB_eq h.1, sintEqB_eq h.2]

theorem optEqB_sound : ∀ {o : Option (IV 128)} {I : IV 128}, optEqB o I = true → o = some I
  | none, _, h => by simp [optEqB] at h
  | some a, _, h => by rw [ivEqB_eq h]

end SandierSerfaty.Certificate.Assemble
