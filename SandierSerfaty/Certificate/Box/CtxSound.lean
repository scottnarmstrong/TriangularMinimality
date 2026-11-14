/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxDef
public import SandierSerfaty.Certificate.Box.Rows
public import SandierSerfaty.Certificate.Box.Radial2
public import SandierSerfaty.Certificate.Query.ConstSound
public import SandierSerfaty.Certificate.Query.TableBridge

/-!
# Soundness of the radial lookup with second derivatives and the exterior (A7, A10)

* `ITable.Encl2`: the table realized by real nodes, with the second-derivative fields of the cells for the truncated
  `f̃₀` (two-sided) and `ẽ` (right derivative of `ẽ'` on `[a_i, a_{i+1})`);
* `ExactEncl t rad c`: the exact `f₀, f₀', e, e', f₀''` and a right derivative of `e'` lie in the tuple `c` widened by
  `rad`;
* `lookupX_sound`: for every `t ≥ b` in the query interval `X`, `lookupX` succeeds and its tuple satisfies
  `ExactEncl t rad` (table cell of `t` for `t < l`, exterior tuple for `t ≥ l`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The table realized by real nodes, with the second derivatives of the truncated radial functions on the cells. -/
structure Encl2 (T : ITable) (a : ℕ → ℝ) : Prop where
  /-- The first-order realization. -/
  base : T.Encl a
  /-- `f̃₀''` on the cells (two-sided). -/
  f2 : ∀ i, i < T.n → ∀ t ∈ Icc (a i) (a (i + 1)), ∃ F, HasDerivAt (deriv Trunc.f₀) F t ∧
    IV.Mem F (T.cell i).f2
  /-- A right derivative of `ẽ'` on `[a_i, a_{i+1})`. -/
  e2 : ∀ i, i < T.n → ∀ t ∈ Ico (a i) (a (i + 1)), ∃ E, HasDerivWithinAt (deriv Trunc.e) E (Ici t) t ∧
    IV.Mem E (T.cell i).e2

/-- The exact radial functions at `t` lie in the tuple `c` widened by `rad`. -/
@[expose] def ExactEncl (t : ℝ) (rad : ℕ) (c : Tup) : Prop :=
  IV.Mem (f₀ t) (IV.addRad c.f0 rad) ∧ IV.Mem (deriv f₀ t) (IV.addRad c.f1 rad) ∧
    IV.Mem (e t) (IV.addRad c.e0 rad) ∧ IV.Mem (deriv e t) (IV.addRad c.e1 rad) ∧
    IV.Mem (deriv (deriv f₀) t) (IV.addRad c.f2 rad) ∧
    ∃ E, HasDerivWithinAt (deriv e) E (Ici t) t ∧ IV.Mem E (IV.addRad c.e2 rad)

/-- The truncated radial functions at `t` lie in the tuple `c` (and `ẽ'` has the right derivative `E`). -/
@[expose] def TruncEncl (t : ℝ) (c : Tup) : Prop :=
  IV.Mem (Trunc.f₀ t) c.f0 ∧ IV.Mem (deriv Trunc.f₀ t) c.f1 ∧ IV.Mem (Trunc.e t) c.e0 ∧
    IV.Mem (deriv Trunc.e t) c.e1 ∧ IV.Mem (deriv (deriv Trunc.f₀) t) c.f2 ∧
    ∃ E, HasDerivWithinAt (deriv Trunc.e) E (Ici t) t ∧ IV.Mem E c.e2

/-- The exact radial functions at `t ≥ l` lie in the tuple `c` (the exterior tuple). -/
@[expose] def ExtEncl (t : ℝ) (c : Tup) : Prop :=
  IV.Mem (f₀ t) c.f0 ∧ IV.Mem (deriv f₀ t) c.f1 ∧ IV.Mem (e t) c.e0 ∧ IV.Mem (deriv e t) c.e1 ∧
    IV.Mem (deriv (deriv f₀) t) c.f2 ∧ ∃ E, HasDerivWithinAt (deriv e) E (Ici t) t ∧ IV.Mem E c.e2

theorem TruncEncl.hull_left {t : ℝ} {a : Tup} (h : TruncEncl t a) (b : Tup) : TruncEncl t (hullTup a b) := by
  obtain ⟨h0, h1, h2, h3, h4, E, hE, h5⟩ := h
  exact ⟨IV.mem_hull_left h0, IV.mem_hull_left h1, IV.mem_hull_left h2, IV.mem_hull_left h3,
    IV.mem_hull_left h4, E, hE, IV.mem_hull_left h5⟩

theorem ExtEncl.hull_right {t : ℝ} {b : Tup} (h : ExtEncl t b) (a : Tup) : ExtEncl t (hullTup a b) := by
  obtain ⟨h0, h1, h2, h3, h4, E, hE, h5⟩ := h
  exact ⟨IV.mem_hull_right h0, IV.mem_hull_right h1, IV.mem_hull_right h2, IV.mem_hull_right h3,
    IV.mem_hull_right h4, E, hE, IV.mem_hull_right h5⟩

theorem memEq {x y : ℝ} {a : IV 128} (h : IV.Mem x a) (e : x = y) : IV.Mem y a := e ▸ h

theorem mem_addRad_self {x : ℝ} {I : IV 128} (h : IV.Mem x I) (r : ℕ) : IV.Mem x (IV.addRad I r) :=
  IV.mem_addRad h (by simp)

theorem ExtEncl.exact {t : ℝ} {c : Tup} (h : ExtEncl t c) (rad : ℕ) : ExactEncl t rad c := by
  obtain ⟨h0, h1, h2, h3, h4, E, hE, h5⟩ := h
  exact ⟨mem_addRad_self h0 _, mem_addRad_self h1 _, mem_addRad_self h2 _, mem_addRad_self h3 _,
    mem_addRad_self h4 _, E, hE, mem_addRad_self h5 _⟩

/-- **From the truncated to the exact functions** (`tail:uniform-error`, widening by `rad ≥ 10⁻¹¹ 2^128`). -/
theorem TruncEncl.exact (hc : FiniteCore) {t : ℝ} (ht : t ∈ Ico Calibration.b Calibration.l) {c : Tup}
    (h : TruncEncl t c) {rad : ℕ} (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) : ExactEncl t rad c := by
  obtain ⟨h0, h1, h2, h3, h4, E, hE, h5⟩ := h
  have htI : t ∈ Icc Calibration.b Calibration.l := ⟨ht.1, ht.2.le⟩
  obtain ⟨u0, u2, u1, u3, u4, -⟩ := uniform_error_of_finiteCore hc htI
  obtain ⟨E', hE', hEE⟩ := exists_e_right_deriv hc ht hE
  refine ⟨mem_of_abs_lt h0 u0 hrad, mem_of_abs_lt h1 u1 hrad, mem_of_abs_lt h2 u2 hrad, mem_of_abs_lt h3 u3 hrad,
    mem_of_abs_lt h4 u4 hrad, E', hE', mem_of_abs_lt h5 hEE hrad⟩

/-! ### The right cell of a point -/

theorem exists_cell_right_strict {a : ℕ → ℝ} {n : ℕ} (hn : 0 < n) {y : ℝ}
    (h0 : a 0 ≤ y) (hy : y < a n) : ∃ j, j < n ∧ a j ≤ y ∧ y < a (j + 1) := by
  classical
  set j := Nat.findGreatest (fun i => a i ≤ y) (n - 1) with hj
  have hsp : a j ≤ y := Nat.findGreatest_spec (P := fun i => a i ≤ y) (Nat.zero_le _) h0
  have hjn : j ≤ n - 1 := Nat.findGreatest_le _
  refine ⟨j, by omega, hsp, ?_⟩
  rcases Nat.lt_or_ge j (n - 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun i => a i ≤ y) (show j < j + 1 by omega) (by omega : j + 1 ≤ n - 1)
    exact not_le.1 this
  · have : j + 1 = n := by omega
    rw [this]; exact hy

/-- A cell of the table with `t ∈ [a_i, a_{i+1})` for `t ∈ [b, l)`. -/
theorem exists_right_cell_of_encl {T : ITable} {a : ℕ → ℝ} (h : T.Encl a) {t : ℝ}
    (ht : t ∈ Ico Calibration.b Calibration.l) : ∃ i, i < T.n ∧ a i ≤ t ∧ t < a (i + 1) := by
  have hn : 0 < T.n := by
    by_contra hn0
    have hn0' : T.n = 0 := by omega
    have := h.last
    rw [hn0', h.first] at this
    have hbl : Calibration.b < Calibration.l :=
      Calibration.b_lt_p.trans (Calibration.p_lt_R₀.trans Calibration.R₀_lt_l)
    linarith
  obtain ⟨j, hj, h1, h2⟩ := exists_cell_right_strict (a := a) hn (y := t) (by rw [h.first]; exact ht.1)
    (by rw [h.last]; exact ht.2)
  exact ⟨j, hj, h1, h2⟩

/-! ### The lookup -/

/-- **The table part of the lookup**: for `t ∈ [b, l)` and `X ∋ t` the hull of the cells meeting `X` encloses the
truncated radial functions at `t`. -/
theorem lookup_trunc {T : ITable} {a : ℕ → ℝ} (H : Encl2 T a) {X : IV 128} {t : ℝ}
    (ht : t ∈ Ico Calibration.b Calibration.l) (hX : IV.Mem t X) :
    ∃ c, lookup T X = some c ∧ TruncEncl t c := by
  obtain ⟨i, hi, hat, hta⟩ := exists_right_cell_of_encl H.base ht
  have hti : t ∈ Icc (a i) (a (i + 1)) := ⟨hat, hta.le⟩
  have hmeets := meets_of_mem (H.base.node i hi.le) (H.base.node (i + 1) hi) hat hta.le hX
  have m0 := H.base.f0 i hi t hti
  have m1 := H.base.f1 i hi t hti
  have m2 := H.base.e0 i hi t hti
  have m3 := H.base.e1 i hi t hti
  obtain ⟨F, hF, m4⟩ := H.f2 i hi t hti
  obtain ⟨E, hE, m5⟩ := H.e2 i hi t ⟨hat, hta⟩
  have m4' : IV.Mem (deriv (deriv Trunc.f₀) t) (T.cell i).f2 := by rw [hF.deriv]; exact m4
  have key : ∀ (proj : Tup → IV 128) (x : ℝ), (∀ a b, proj (hullTup a b) = IV.hull (proj a) (proj b)) →
      IV.Mem x (proj (T.cell i)) → ∃ c, lookup T X = some c ∧ IV.Mem x (proj c) :=
    fun proj x hh hx => lookupFrom_mem hh T.n none (Or.inl ⟨i, hi, hmeets, hx⟩)
  obtain ⟨c, hc, n0⟩ := key Tup.f0 _ (fun _ _ => rfl) m0
  have get : ∀ (proj : Tup → IV 128) (x : ℝ), (∀ a b, proj (hullTup a b) = IV.hull (proj a) (proj b)) →
      IV.Mem x (proj (T.cell i)) → IV.Mem x (proj c) := by
    intro proj x hh hx
    obtain ⟨c', hc', m⟩ := key proj x hh hx
    rw [hc] at hc'
    cases hc'
    exact m
  exact ⟨c, hc, n0, get Tup.f1 _ (fun _ _ => rfl) m1, get Tup.e0 _ (fun _ _ => rfl) m2,
    get Tup.e1 _ (fun _ _ => rfl) m3, get Tup.f2 _ (fun _ _ => rfl) m4', E, hE,
    get Tup.e2 _ (fun _ _ => rfl) m5⟩

/-- **The exterior tuple** encloses the exact radial functions at `t ≥ l`. -/
theorem extTup_encl {f0lI k0I lsqI X : IV 128} {t : ℝ} (ht : Calibration.l ≤ t) (hX : IV.Mem t X)
    (hf0l : IV.Mem (f₀ Calibration.l) f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) lsqI) : ExtEncl t (extTup f0lI k0I lsqI X) := by
  have h0 : IV.Mem (0 : ℝ) (IV.ofNat 0 : IV 128) := by simpa using IV.mem_ofNat (P := 128) 0
  refine ⟨?_, ?_, ?_, ?_, ?_, 0, e_right_deriv_ext ht, h0⟩
  · have := IV.mem_add hf0l (IV.mem_mul hk0 (IV.mem_sub (IV.mem_sq hX) hlsq))
    refine memEq this ?_
    rw [f₀_of_ge ht]; ring
  · have := IV.mem_mulNat (IV.mem_mul hk0 hX) 2
    refine memEq this ?_
    rw [deriv_f₀_of_ge ht]; push_cast; ring
  · rw [e_of_ge ht]; exact h0
  · rw [deriv_e_of_ge ht]; exact h0
  · have := IV.mem_mulNat hk0 2
    refine memEq this ?_
    rw [(f₀_second_ext ht).deriv]; push_cast; ring

/-- **The soundness of the lookup with the exterior**: for every `t ≥ b` in the query interval `X`. -/
theorem lookupX_sound (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (H : Encl2 T a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {f0lI k0I lsqI lI X : IV 128} {t : ℝ}
    (hbt : Calibration.b ≤ t) (hX : IV.Mem t X) (hl : IV.Mem Calibration.l lI)
    (hf0l : IV.Mem (f₀ Calibration.l) f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) lsqI) :
    ∃ c, lookupX T f0lI k0I lsqI lI X = some c ∧ ExactEncl t rad c := by
  unfold lookupX
  rcases lt_or_ge t Calibration.l with hlt | hge
  · obtain ⟨c0, hc0, h0⟩ := lookup_trunc H ⟨hbt, hlt⟩ hX
    cases hb : SInt.ble lI.lo X.hi
    · simp only [Bool.cond_false]
      exact ⟨c0, hc0, h0.exact hc ⟨hbt, hlt⟩ hrad⟩
    · simp only [Bool.cond_true]
      rw [hc0]
      exact ⟨_, rfl, (h0.hull_left _).exact hc ⟨hbt, hlt⟩ hrad⟩
  · have hb : SInt.ble lI.lo X.hi = true := by
      have hN : (0 : ℝ) < 2 ^ 128 := by positivity
      have h1 : Calibration.l * 2 ^ 128 ≤ t * 2 ^ 128 := mul_le_mul_of_nonneg_right hge hN.le
      simp only [SInt.ble_iff]
      have : ((lI.lo.toInt : ℤ) : ℝ) ≤ ((X.hi.toInt : ℤ) : ℝ) := by linarith [hl.1, hX.2]
      exact_mod_cast this
    simp only [hb, Bool.cond_true]
    have hE := extTup_encl hge hX hf0l hk0 hlsq
    cases hc0 : lookup T X with
    | none => exact ⟨_, rfl, hE.exact rad⟩
    | some c0 => exact ⟨_, rfl, (hE.hull_right c0).exact rad⟩

end SandierSerfaty.Certificate.Box
