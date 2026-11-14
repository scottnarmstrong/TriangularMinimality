/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Lookup
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import SandierSerfaty.Certificate.Table.Bridge

/-!
# Soundness of the interval lookup

`ITable.Encl T a` says that the real nodes `a 0, …, a n` realize the stored table: `a i` lies in the node interval
`T.node i`, the nodes are nondecreasing, `a 0 = b` and `a n = l`, and on each real cell `[a_i, a_{i+1}]` the
stored tuple `T.cell i` encloses `f̃₀, f̃₀', ẽ, ẽ'` (`f̃₀ = Cal.Trunc.f₀`, `ẽ = Cal.Trunc.e`). It is the output of
the table chunks (`Table.chunks_sound_trunc` and the derivative fields of `Table.TableEncloses`).

* `exists_cell`: every `t ∈ [b, l]` lies in a real cell;
* `lookup_f1`, `lookup_e1`, `lookup_f0`, `lookup_e0`: if `X` encloses `t ∈ [b, l]`, the lookup succeeds and its
  hull encloses `deriv f̃₀ t`, `deriv ẽ t`, `f̃₀ t`, `ẽ t`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Calibration

/-- The real nodes `a` realize the stored table `T`. -/
structure ITable.Encl (T : ITable) (a : ℕ → ℝ) : Prop where
  /-- `a i ∈ node i`. -/
  node : ∀ i, i ≤ T.n → IV.Mem (a i) (T.node i)
  /-- The nodes are nondecreasing. -/
  mono : ∀ i, i < T.n → a i ≤ a (i + 1)
  /-- The first node is `b`. -/
  first : a 0 = Calibration.b
  /-- The last node is `l`. -/
  last : a T.n = Calibration.l
  /-- `f̃₀` on the cells. -/
  f0 : ∀ i, i < T.n → ∀ t ∈ Icc (a i) (a (i + 1)), IV.Mem (Trunc.f₀ t) (T.cell i).f0
  /-- `f̃₀'` on the cells. -/
  f1 : ∀ i, i < T.n → ∀ t ∈ Icc (a i) (a (i + 1)), IV.Mem (deriv Trunc.f₀ t) (T.cell i).f1
  /-- `ẽ` on the cells. -/
  e0 : ∀ i, i < T.n → ∀ t ∈ Icc (a i) (a (i + 1)), IV.Mem (Trunc.e t) (T.cell i).e0
  /-- `ẽ'` on the cells. -/
  e1 : ∀ i, i < T.n → ∀ t ∈ Icc (a i) (a (i + 1)), IV.Mem (deriv Trunc.e t) (T.cell i).e1

theorem exists_cell {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {t : ℝ} (ht : t ∈ Icc Calibration.b Calibration.l) :
    ∃ i, i < T.n ∧ t ∈ Icc (a i) (a (i + 1)) := by
  classical
  have hS : ∃ k, k ≤ T.n ∧ t ≤ a k := ⟨T.n, le_rfl, by rw [h.last]; exact ht.2⟩
  set k := Nat.find hS with hk
  obtain ⟨hkn, hkt⟩ := Nat.find_spec hS
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · -- `t ≤ a 0 = b ≤ t`
    have h0' : t ≤ a 0 := by rw [← h0]; exact hkt
    have hteq : t = a 0 := le_antisymm h0' (by rw [h.first]; exact ht.1)
    have hn : 0 < T.n := by
      by_contra hn0
      have hn0' : T.n = 0 := by omega
      have := h.last
      rw [hn0', h.first] at this
      have hbl : Calibration.b < Calibration.l :=
        Calibration.b_lt_p.trans (Calibration.p_lt_R₀.trans Calibration.R₀_lt_l)
      linarith
    exact ⟨0, hn, hteq ▸ le_rfl, hteq ▸ h.mono 0 hn⟩
  · have hlt : a (k - 1) < t := by
      have := Nat.find_min hS (show k - 1 < k by omega)
      exact not_le.mp (fun h' => this ⟨by omega, h'⟩)
    refine ⟨k - 1, by omega, hlt.le, ?_⟩
    have : k - 1 + 1 = k := by omega
    rw [this]; exact hkt

/-- The cell `[a, b]` with `a ∈ v`, `b ∈ u` and `t ∈ [a, b]` meets any `X ∋ t`. -/
theorem meets_of_mem {v u X : IV 128} {a b t : ℝ} (ha : IV.Mem a v) (hb : IV.Mem b u) (hat : a ≤ t)
    (htb : t ≤ b) (ht : IV.Mem t X) : meets v u X = true := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  have h1 : a * 2 ^ 128 ≤ t * 2 ^ 128 := mul_le_mul_of_nonneg_right hat hN.le
  have h2 : t * 2 ^ 128 ≤ b * 2 ^ 128 := mul_le_mul_of_nonneg_right htb hN.le
  simp only [meets, Bool.and_eq_true, SInt.ble_iff]
  constructor
  · have : ((v.lo.toInt : ℤ) : ℝ) ≤ ((X.hi.toInt : ℤ) : ℝ) := by linarith [ha.1, ht.2]
    exact_mod_cast this
  · have : ((X.lo.toInt : ℤ) : ℝ) ≤ ((u.hi.toInt : ℤ) : ℝ) := by linarith [ht.1, hb.2]
    exact_mod_cast this

/-- **The scan collects the cells that meet `X`**, for a projection `proj` that commutes with the hull. -/
theorem lookupFrom_mem {T : ITable} {X : IV 128} {x : ℝ} {proj : Tup → IV 128}
    (hh : ∀ a b, proj (hullTup a b) = IV.hull (proj a) (proj b)) :
    ∀ (k : ℕ) (acc : Option Tup),
      ((∃ i, i < k ∧ meets (T.node i) (T.node (i + 1)) X = true ∧ IV.Mem x (proj (T.cell i))) ∨
        (∃ a, acc = some a ∧ IV.Mem x (proj a))) →
      ∃ a, lookupFrom T X k acc = some a ∧ IV.Mem x (proj a)
  | 0, acc, h => by
    rcases h with ⟨i, hi, -⟩ | h
    · omega
    · exact h
  | k + 1, acc, h => by
    simp only [lookupFrom]
    refine lookupFrom_mem hh k (addCell T X k acc) ?_
    rcases h with ⟨i, hi, hm, hx⟩ | ⟨a, hacc, hx⟩
    · by_cases hik : i < k
      · exact Or.inl ⟨i, hik, hm, hx⟩
      · have : i = k := by omega
        subst this
        right
        simp only [addCell, hm, Bool.cond_true]
        cases acc with
        | none => exact ⟨_, rfl, hx⟩
        | some a => exact ⟨_, rfl, by rw [hh]; exact IV.mem_hull_right hx⟩
    · right
      cases hm : meets (T.node k) (T.node (k + 1)) X
      · simp only [addCell, hm, Bool.cond_false]
        exact ⟨a, hacc, hx⟩
      · simp only [addCell, hm, Bool.cond_true]
        rw [hacc]
        exact ⟨_, rfl, by rw [hh]; exact IV.mem_hull_left hx⟩

/-- The lookup succeeds at `X ∋ t` and its hull encloses `x` whenever the cell of `t` does. -/
theorem lookup_mem {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {X : IV 128} {t x : ℝ}
    (ht : t ∈ Icc Calibration.b Calibration.l) (hX : IV.Mem t X) {proj : Tup → IV 128}
    (hh : ∀ a b, proj (hullTup a b) = IV.hull (proj a) (proj b))
    (hx : ∀ i, i < T.n → t ∈ Icc (a i) (a (i + 1)) → IV.Mem x (proj (T.cell i))) :
    ∃ c, lookup T X = some c ∧ IV.Mem x (proj c) := by
  obtain ⟨i, hi, hti⟩ := exists_cell h ht
  refine lookupFrom_mem hh T.n none (Or.inl ⟨i, hi, ?_, hx i hi hti⟩)
  exact meets_of_mem (h.node i hi.le) (h.node (i + 1) hi) hti.1 hti.2 hX

theorem lookup_f1 {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {X : IV 128} {t : ℝ}
    (ht : t ∈ Icc Calibration.b Calibration.l) (hX : IV.Mem t X) :
    ∃ c, lookup T X = some c ∧ IV.Mem (deriv Trunc.f₀ t) c.f1 :=
  lookup_mem h ht hX (proj := Tup.f1) (fun _ _ => rfl) fun i hi hti => h.f1 i hi t hti

theorem lookup_e1 {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {X : IV 128} {t : ℝ}
    (ht : t ∈ Icc Calibration.b Calibration.l) (hX : IV.Mem t X) :
    ∃ c, lookup T X = some c ∧ IV.Mem (deriv Trunc.e t) c.e1 :=
  lookup_mem h ht hX (proj := Tup.e1) (fun _ _ => rfl) fun i hi hti => h.e1 i hi t hti

theorem lookup_f0 {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {X : IV 128} {t : ℝ}
    (ht : t ∈ Icc Calibration.b Calibration.l) (hX : IV.Mem t X) :
    ∃ c, lookup T X = some c ∧ IV.Mem (Trunc.f₀ t) c.f0 :=
  lookup_mem h ht hX (proj := Tup.f0) (fun _ _ => rfl) fun i hi hti => h.f0 i hi t hti

theorem lookup_e0 {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {X : IV 128} {t : ℝ}
    (ht : t ∈ Icc Calibration.b Calibration.l) (hX : IV.Mem t X) :
    ∃ c, lookup T X = some c ∧ IV.Mem (Trunc.e t) c.e0 :=
  lookup_mem h ht hX (proj := Tup.e0) (fun _ _ => rfl) fun i hi hti => h.e0 i hi t hti

end SandierSerfaty.Certificate.Query
