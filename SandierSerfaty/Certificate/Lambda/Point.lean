/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Lambda.Eval
public import SandierSerfaty.Certificate.Lambda.Deriv
public import SandierSerfaty.Certificate.Box.Encl2
public import SandierSerfaty.Certificate.Query.LamSound

/-!
# Soundness of the point evaluations of the fine `λ` quadrature

* `FRealized F a`: the table realization of the box layer (`Box.TableRealized`) together with the node tuples:
  `nt i` encloses the segment model and its derivative witnesses at the right node `a_{i+1}` (`NodeEncl`, the
  node half of `Table.TableEncloses`);
* `NodeEncl.exact`: the node tuple widened by `rad` encloses `f₀, f₀', e, e'` at the node
  (`Tails.uniform_error_of_finiteCore`);
* `f2_right`, `e2_right`: on `[a_i, a_{i+2})` the right derivatives of `f₀'` and of `e'` lie in the widened hulls
  `f2Hull`, `e2Hull` of the two cells (`Box.Encl2`, `Box.exists_e_right_deriv`);
* `fAt_sound`, `eAt_sound`, `f1At_sound`: the second- (first-) order expansions at `a_{i+1}`
  (`Lambda.exists_second_order`, `exists_first_order`) for `t` in a point set `X` passing `pairOK`;
* `bounds_of_lookup`: the sup bounds `C, C', E, E'` on `[p, R₀]` from one lookup.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### Interval facts -/

/-- The lower end of `I` as a real. -/
@[expose] noncomputable def ivLo (I : IV 128) : ℝ := ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128

/-- The upper end of `I` as a real. -/
@[expose] noncomputable def ivHi (I : IV 128) : ℝ := ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128

theorem mem_iff_bounds {x : ℝ} {I : IV 128} : IV.Mem x I ↔ ivLo I ≤ x ∧ x ≤ ivHi I := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  unfold IV.Mem ivLo ivHi
  rw [div_le_iff₀ hN, le_div_iff₀ hN]

/-- The real value `max(|lo|, |hi|)/2^128` of `magIV I`. -/
@[expose] noncomputable def magV (I : IV 128) : ℝ := (Nat.max I.lo.mag I.hi.mag : ℝ) / 2 ^ 128

theorem mem_magIV (I : IV 128) : IV.Mem (magV I) (magIV I) := by
  have := IV.mem_point (P := 128) ⟨false, Nat.max I.lo.mag I.hi.mag⟩
  simpa [magV, magIV, SInt.toInt_false] using this

theorem abs_le_magV {x : ℝ} {I : IV 128} (h : IV.Mem x I) : |x| ≤ magV I := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  obtain ⟨h1, h2⟩ := h
  have a1 : |((I.lo.toInt : ℤ) : ℝ)| = I.lo.mag := by rw [← Int.cast_abs, SInt.abs_toInt]; simp
  have a2 : |((I.hi.toInt : ℤ) : ℝ)| = I.hi.mag := by rw [← Int.cast_abs, SInt.abs_toInt]; simp
  have hm1 : (I.lo.mag : ℝ) ≤ (Nat.max I.lo.mag I.hi.mag : ℕ) := by exact_mod_cast le_max_left _ _
  have hm2 : (I.hi.mag : ℝ) ≤ (Nat.max I.lo.mag I.hi.mag : ℕ) := by exact_mod_cast le_max_right _ _
  unfold magV
  rw [le_div_iff₀ hN, ← abs_of_pos hN, ← abs_mul, abs_le]
  constructor
  · have := neg_abs_le ((I.lo.toInt : ℤ) : ℝ); rw [a1] at this; linarith
  · have := le_abs_self ((I.hi.toInt : ℤ) : ℝ); rw [a2] at this; linarith

theorem mem_symHi {δ ε : ℝ} {E : IV 128} (hE : IV.Mem ε E) (h : |δ| ≤ ε) : IV.Mem δ (symHi E) := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  obtain ⟨-, h2⟩ := hE
  have h' := abs_le.1 h
  refine ⟨?_, ?_⟩
  · show (((SInt.neg E.hi).toInt : ℤ) : ℝ) ≤ δ * 2 ^ 128
    rw [SInt.toInt_neg, Int.cast_neg]; nlinarith
  · show δ * 2 ^ 128 ≤ ((E.hi.toInt : ℤ) : ℝ); nlinarith

theorem mem_of_mem_iff {x y : ℝ} {I : IV 128} (h : IV.Mem x I) (e : x = y) : IV.Mem y I := e ▸ h

/-! ### The realization with node tuples -/

/-- The node tuple `nt` encloses the model of some segment `j ∋ y` with its derivative witnesses at `y`. -/
@[expose] def NodeEncl (y : ℝ) (nt : Tup) : Prop :=
  ∃ j, j ≤ 6 ∧ y ∈ seg j ∧ TupEncl {y} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) nt

/-- **The fine table is realized**: the box realization (`Box.TableRealized`) and the node tuples at the right
nodes. -/
structure FRealized (F : FTable) (a : ℕ → ℝ) : Prop where
  /-- Nodes and cells. -/
  tab : TableRealized F.T a
  /-- The node tuple of cell `i` at `a_{i+1}`. -/
  nt : ∀ i, i < F.T.n → NodeEncl (a (i + 1)) (F.nt i)

/-- **The exact functions at a node** from its node tuple widened by `rad`. -/
theorem NodeEncl.exact (hc : FiniteCore) {y : ℝ} {nt : Tup} (h : NodeEncl y nt)
    (hy : y ∈ Icc Calibration.b Calibration.l) {rad : ℕ} (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) :
    IV.Mem (f₀ y) (IV.addRad nt.f0 rad) ∧ IV.Mem (deriv f₀ y) (IV.addRad nt.f1 rad) ∧
      IV.Mem (e y) (IV.addRad nt.e0 rad) ∧ IV.Mem (deriv e y) (IV.addRad nt.e1 rad) := by
  obtain ⟨j, hj, hys, F₁, F₂, E₁, E₂, hd, hm⟩ := h
  obtain ⟨m0, m1, -, n0, n1, -⟩ := hm y rfl
  obtain ⟨d0, -, e0, -⟩ := hd y rfl
  have a0 : IV.Mem (Trunc.f₀ y) nt.f0 := by rw [trunc_f₀_eq_F0m hj hys]; exact m0
  have a1 : IV.Mem (deriv Trunc.f₀ y) nt.f1 := by rw [deriv_trunc_f₀_eq hc hj hys d0]; exact m1
  have a2 : IV.Mem (Trunc.e y) nt.e0 := by rw [trunc_e_eq_Em hj hys]; exact n0
  have a3 : IV.Mem (deriv Trunc.e y) nt.e1 := by rw [deriv_trunc_e_eq hj hys e0]; exact n1
  obtain ⟨u0, u2, u1, u3, -⟩ := uniform_error_of_finiteCore hc hy
  exact ⟨mem_of_abs_lt a0 u0 hrad, mem_of_abs_lt a1 u1 hrad, mem_of_abs_lt a2 u2 hrad,
    mem_of_abs_lt a3 u3 hrad⟩

theorem FRealized.lt {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {i : ℕ} (hi : i < F.T.n) : a i < a (i + 1) := by
  obtain ⟨j, hj⟩ := h.tab.cell i hi
  exact hj.lt

theorem FRealized.le_add {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {i : ℕ} :
    ∀ k, i + k ≤ F.T.n → a i ≤ a (i + k)
  | 0, _ => le_rfl
  | k + 1, hk => (h.le_add k (by omega)).trans (by
      have := h.lt (i := i + k) (by omega); rw [← add_assoc]; exact this.le)

theorem FRealized.mem_bl {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {i : ℕ} (hi : i ≤ F.T.n) :
    a i ∈ Icc Calibration.b Calibration.l := by
  constructor
  · have := h.le_add (i := 0) i (by omega); rw [zero_add, h.tab.first] at this; exact this
  · have := h.le_add (i := i) (F.T.n - i) (by omega)
    rw [show i + (F.T.n - i) = F.T.n by omega, h.tab.last] at this; exact this

/-- **The pair check**: `t ∈ X` lies in `[a_i, a_{i+2}]` and both cells exist. -/
theorem pairOK_sound {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {i : ℕ} {X : IV 128} {t : ℝ}
    (hp : pairOK F i X = true) (ht : IV.Mem t X) : i + 1 < F.T.n ∧ a i ≤ t ∧ t ≤ a (i + 2) := by
  simp only [pairOK, Bool.and_eq_true] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have hn : i + 1 < F.T.n := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true h1)
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  have na := h.tab.node i (by omega)
  have nb := h.tab.node (i + 2) (by omega)
  have c2 : ((F.T.node i).hi.toInt : ℝ) ≤ (X.lo.toInt : ℝ) := by exact_mod_cast (SInt.ble_iff _ _).1 h2
  have c3 : (X.hi.toInt : ℝ) ≤ ((F.T.node (i + 2)).lo.toInt : ℝ) := by exact_mod_cast (SInt.ble_iff _ _).1 h3
  refine ⟨hn, ?_, ?_⟩
  · have : a i * 2 ^ 128 ≤ t * 2 ^ 128 := by linarith [na.2, ht.1]
    exact le_of_mul_le_mul_right this hN
  · have : t * 2 ^ 128 ≤ a (i + 2) * 2 ^ 128 := by linarith [nb.1, ht.2]
    exact le_of_mul_le_mul_right this hN

/-! ### The jets on a pair of cells -/

/-- The right derivatives of `f₀'` on `[a_i, a_{i+2})` lie in `f2Hull`. -/
theorem f2_right (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {i : ℕ} (hi : i + 1 < F.T.n) :
    ∀ x ∈ Ico (a i) (a (i + 2)), ∃ E, HasDerivWithinAt (deriv f₀) E (Ici x) x ∧ IV.Mem E (f2Hull F rad i) := by
  intro x hx
  have H := h.tab.encl2 hc
  have hxbl : x ∈ Icc Calibration.b Calibration.l :=
    ⟨(h.mem_bl (i := i) (by omega)).1.trans hx.1, hx.2.le.trans (h.mem_bl (i := i + 2) (by omega)).2⟩
  have hx0 : 0 < x := lt_of_lt_of_le Calibration.b_pos hxbl.1
  obtain ⟨-, -, -, -, u4, -⟩ := uniform_error_of_finiteCore hc hxbl
  refine ⟨deriv (deriv f₀) x, (Box.hasDerivAt_deriv_f₀ hx0).hasDerivWithinAt, ?_⟩
  rcases le_total x (a (i + 1)) with hx1 | hx1
  · obtain ⟨G, hG, hm⟩ := H.f2 i (by omega) x ⟨hx.1, hx1⟩
    rw [hG.deriv] at u4
    exact mem_of_abs_lt (IV.mem_hull_left hm) u4 hrad
  · obtain ⟨G, hG, hm⟩ := H.f2 (i + 1) hi x ⟨hx1, hx.2.le⟩
    rw [hG.deriv] at u4
    exact mem_of_abs_lt (IV.mem_hull_right hm) u4 hrad

/-- The right derivatives of `e'` on `[a_i, a_{i+2})` lie in `e2Hull`. -/
theorem e2_right (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {i : ℕ} (hi : i + 1 < F.T.n) :
    ∀ x ∈ Ico (a i) (a (i + 2)), ∃ E, HasDerivWithinAt (deriv e) E (Ici x) x ∧ IV.Mem E (e2Hull F rad i) := by
  intro x hx
  have H := h.tab.encl2 hc
  have hxbl : x ∈ Ico Calibration.b Calibration.l :=
    ⟨(h.mem_bl (i := i) (by omega)).1.trans hx.1, lt_of_lt_of_le hx.2 (h.mem_bl (i := i + 2) (by omega)).2⟩
  rcases lt_or_ge x (a (i + 1)) with hx1 | hx1
  · obtain ⟨E, hE, hm⟩ := H.e2 i (by omega) x ⟨hx.1, hx1⟩
    obtain ⟨E', hE', hEE⟩ := exists_e_right_deriv hc hxbl hE
    exact ⟨E', hE', mem_of_abs_lt (IV.mem_hull_left hm) hEE hrad⟩
  · obtain ⟨E, hE, hm⟩ := H.e2 (i + 1) hi x ⟨hx1, hx.2⟩
    obtain ⟨E', hE', hEE⟩ := exists_e_right_deriv hc hxbl hE
    exact ⟨E', hE', mem_of_abs_lt (IV.mem_hull_right hm) hEE hrad⟩

/-- The interval form of a right-derivative range. -/
theorem range_of_mem {G : ℝ → ℝ} {lo hi : ℝ} {I : IV 128}
    (h : ∀ x ∈ Ico lo hi, ∃ E, HasDerivWithinAt G E (Ici x) x ∧ IV.Mem E I) :
    ∀ x ∈ Ico lo hi, ∃ E, HasDerivWithinAt G E (Ici x) x ∧ ivLo I ≤ E ∧ E ≤ ivHi I := fun x hx => by
  obtain ⟨E, hE, hm⟩ := h x hx
  exact ⟨E, hE, mem_iff_bounds.1 hm⟩

theorem lo_le_hi_of {G : ℝ → ℝ} {lo hi : ℝ} {I : IV 128} (hlh : lo < hi)
    (h : ∀ x ∈ Ico lo hi, ∃ E, HasDerivWithinAt G E (Ici x) x ∧ IV.Mem E I) : ivLo I ≤ ivHi I := by
  obtain ⟨E, -, hm⟩ := h lo ⟨le_rfl, hlh⟩
  exact (mem_iff_bounds.1 hm).1.trans (mem_iff_bounds.1 hm).2

/-! ### The point evaluations -/

/-- The data of a checked pair: `t ∈ [a_i, a_{i+2}]`, the node `y = a_{i+1}` in between, the offset. -/
theorem pair_data {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {i : ℕ} {X : IV 128} {t : ℝ}
    (hp : pairOK F i X = true) (ht : IV.Mem t X) :
    i + 1 < F.T.n ∧ a i < a (i + 2) ∧ t ∈ Icc (a i) (a (i + 2)) ∧ a (i + 1) ∈ Icc (a i) (a (i + 2)) ∧
      Icc (a i) (a (i + 2)) ⊆ Ioi 0 ∧ IV.Mem (t - a (i + 1)) (offset F i X) ∧
      a (i + 1) ∈ Icc Calibration.b Calibration.l := by
  obtain ⟨hn, h1, h2⟩ := pairOK_sound h hp ht
  have l1 := h.lt (i := i) (by omega)
  have l2 := h.lt (i := i + 1) hn
  refine ⟨hn, l1.trans l2, ⟨h1, h2⟩, ⟨l1.le, l2.le⟩, fun x hx => ?_,
    IV.mem_sub ht (h.tab.node (i + 1) (by omega)), h.mem_bl (by omega)⟩
  exact lt_of_lt_of_le Calibration.b_pos ((h.mem_bl (i := i) (by omega)).1.trans hx.1)

theorem mem_taylor2 {v d1 θ D : ℝ} {V D1 C2 DI : IV 128} (hv : IV.Mem v V) (hd : IV.Mem d1 D1)
    (hθ : IV.Mem θ C2) (hD : IV.Mem D DI) : IV.Mem (v + d1 * D + θ * D ^ 2 / 2) (taylor2 V D1 C2 DI) := by
  have := IV.mem_add (IV.mem_add hv (IV.mem_mul hd hD)) (IV.mem_divPow2 (IV.mem_mul hθ (IV.mem_sq hD)) 1)
  exact mem_of_mem_iff this (by ring)

/-- **`f₀` at a checked point.** -/
theorem fAt_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {i : ℕ} {X : IV 128} {t : ℝ} (hp : pairOK F i X = true)
    (ht : IV.Mem t X) : IV.Mem (f₀ t) (fAt F rad i X) := by
  obtain ⟨hn, hlt, htI, hyI, hpos, hD, hybl⟩ := pair_data h hp ht
  have hR := f2_right hc h hrad hn
  obtain ⟨θ, h1, h2, hθ⟩ := exists_second_order (F := f₀) (F₁ := deriv f₀)
    (fun x hx => (differentiableAt_f₀ (hpos hx)).hasDerivAt) (continuousOn_deriv_f₀.mono hpos)
    (range_of_mem hR) (lo_le_hi_of hlt hR) hyI htI
  obtain ⟨n0, n1, -, -⟩ := (h.nt i (by omega)).exact hc hybl hrad
  rw [hθ]
  exact mem_taylor2 n0 n1 (mem_iff_bounds.2 ⟨h1, h2⟩) hD

/-- **`e` at a checked point.** -/
theorem eAt_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {i : ℕ} {X : IV 128} {t : ℝ} (hp : pairOK F i X = true)
    (ht : IV.Mem t X) : IV.Mem (e t) (eAt F rad i X) := by
  obtain ⟨hn, hlt, htI, hyI, hpos, hD, hybl⟩ := pair_data h hp ht
  have hR := e2_right hc h hrad hn
  obtain ⟨θ, h1, h2, hθ⟩ := exists_second_order (F := e) (F₁ := deriv e)
    (fun x hx => (differentiableAt_e (hpos hx)).hasDerivAt) (continuousOn_deriv_e.mono hpos)
    (range_of_mem hR) (lo_le_hi_of hlt hR) hyI htI
  obtain ⟨-, -, n0, n1⟩ := (h.nt i (by omega)).exact hc hybl hrad
  rw [hθ]
  exact mem_taylor2 n0 n1 (mem_iff_bounds.2 ⟨h1, h2⟩) hD

/-- **`f₀'` at a checked point.** -/
theorem f1At_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {i : ℕ} {X : IV 128} {t : ℝ} (hp : pairOK F i X = true)
    (ht : IV.Mem t X) : IV.Mem (deriv f₀ t) (f1At F rad i X) := by
  obtain ⟨hn, hlt, htI, hyI, hpos, hD, hybl⟩ := pair_data h hp ht
  have hR := f2_right hc h hrad hn
  obtain ⟨θ, h1, h2, hθ⟩ := exists_first_order (F₁ := deriv f₀) (continuousOn_deriv_f₀.mono hpos)
    (range_of_mem hR) (lo_le_hi_of hlt hR) hyI htI
  obtain ⟨-, n1, -, -⟩ := (h.nt i (by omega)).exact hc hybl hrad
  rw [hθ]
  exact IV.mem_add n1 (IV.mem_mul (mem_iff_bounds.2 ⟨h1, h2⟩) hD)

theorem fPt_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {X v : IV 128} {t : ℝ} (hv : fPt F rad X = some v)
    (ht : IV.Mem t X) : IV.Mem (f₀ t) v := by
  unfold fPt fPtAt at hv
  cases hp : pairOK F (locate F X 0) X <;> simp only [hp, Bool.cond_true, Bool.cond_false, Option.some.injEq,
    reduceCtorEq] at hv
  exact hv ▸ fAt_sound hc h hrad hp ht

theorem ePt_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {X v : IV 128} {t : ℝ} (hv : ePt F rad X = some v)
    (ht : IV.Mem t X) : IV.Mem (e t) v := by
  unfold ePt ePtAt at hv
  cases hp : pairOK F (locate F X 0) X <;> simp only [hp, Bool.cond_true, Bool.cond_false, Option.some.injEq,
    reduceCtorEq] at hv
  exact hv ▸ eAt_sound hc h hrad hp ht

theorem f1Pt_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {X v : IV 128} {t : ℝ} (hv : f1Pt F rad X = some v)
    (ht : IV.Mem t X) : IV.Mem (deriv f₀ t) v := by
  unfold f1Pt f1PtAt at hv
  cases hp : pairOK F (locate F X 0) X <;> simp only [hp, Bool.cond_true, Bool.cond_false, Option.some.injEq,
    reduceCtorEq] at hv
  exact hv ▸ f1At_sound hc h hrad hp ht

/-! ### The derivative bounds from a lookup -/

/-- The lookup over a set containing `t ∈ [b, l)` encloses the exact functions at `t` (widened by `rad`). -/
theorem lookup_exact (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {X : IV 128} {c : Tup} (hl : lookup F.T X = some c) {t : ℝ}
    (ht : t ∈ Ico Calibration.b Calibration.l) (hX : IV.Mem t X) : ExactEncl t rad c := by
  obtain ⟨c', hc', hT⟩ := lookup_trunc (h.tab.encl2 hc) ht hX
  rw [hl] at hc'
  cases hc'
  exact hT.exact hc ht hrad

theorem Icc_p_R₀_sub {t : ℝ} (ht : t ∈ Icc p R₀) : t ∈ Ico Calibration.b Calibration.l :=
  ⟨(Calibration.b_lt_p.trans_le ht.1).le, lt_of_le_of_lt ht.2 Calibration.R₀_lt_l⟩

/-- **The sup bounds on `[p, R₀]`** from the lookup over `[p, R₀]`. -/
theorem bounds_of_lookup (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (h : FRealized F a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {d : BasisData} (hd : d.Valid) {c : Tup}
    (hl : lookup F.T (IV.hull d.p d.r0) = some c) :
    (∀ t ∈ Icc p R₀, |deriv f₀ t| ≤ magV (IV.addRad c.f1 rad)) ∧
      (∀ t ∈ Icc p R₀, |deriv (deriv f₀) t| ≤ magV (IV.addRad c.f2 rad)) ∧
      (∀ t ∈ Icc p R₀, |deriv e t| ≤ magV (IV.addRad c.e1 rad)) ∧
      (∀ t ∈ Ico p R₀, ∃ E₂, HasDerivWithinAt (deriv e) E₂ (Ici t) t ∧ |E₂| ≤ magV (IV.addRad c.e2 rad)) := by
  have hx : ∀ t ∈ Icc p R₀, ExactEncl t rad c := fun t ht =>
    lookup_exact hc h hrad hl (Icc_p_R₀_sub ht) (mem_hull_between hd.mp hd.mr0 ht.1 ht.2)
  refine ⟨fun t ht => abs_le_magV (hx t ht).2.1, fun t ht => abs_le_magV (hx t ht).2.2.2.2.1,
    fun t ht => abs_le_magV (hx t ht).2.2.2.1, fun t ht => ?_⟩
  obtain ⟨E, hE, hm⟩ := (hx t ⟨ht.1, ht.2.le⟩).2.2.2.2.2
  exact ⟨E, hE, abs_le_magV hm⟩

/-! ### The node tuples of a chunk -/

end SandierSerfaty.Certificate.Lambda
