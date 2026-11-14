/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.IV
public import SandierSerfaty.Certificate.Arith.SIntLemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Soundness of the exact-endpoint intervals

`IV.Mem x I` says that the real `x` lies in `I`: `I.lo ≤ x·2^P ≤ I.hi` (endpoints read through
`SInt.toInt`). Every interval operation of `SandierSerfaty.Certificate.Arith.IV` has an inclusion law
`Mem x a → Mem y b → Mem (x ∘ y) (a.op b)` (with the side conditions that the operation's docstring states,
for instance `0 < b.lo` for `divPos`), and every Boolean test has a soundness law (`ltB_sound`, ...).
-/

public section

namespace SandierSerfaty.Certificate.Arith

namespace IV

open SInt

variable {P : ℕ}

/-- The real `x` lies in the interval `a`: `a.lo ≤ x·2^P ≤ a.hi`. -/
@[expose] def Mem (x : ℝ) (a : IV P) : Prop :=
  ((a.lo.toInt : ℤ) : ℝ) ≤ x * 2 ^ P ∧ x * 2 ^ P ≤ ((a.hi.toInt : ℤ) : ℝ)

theorem two_pow_pos' (k : ℕ) : (0 : ℝ) < 2 ^ k := by positivity

/-! ### Exact constructions -/

theorem mem_point (a : SInt) : Mem (((a.toInt : ℤ) : ℝ) / 2 ^ P) (point a : IV P) := by
  have := two_pow_pos' P
  simp only [Mem, point]
  rw [div_mul_cancel₀ _ this.ne']
  exact ⟨le_rfl, le_rfl⟩

theorem mem_ofNat (n : ℕ) : Mem (n : ℝ) (ofNat n : IV P) := by
  simp [Mem, ofNat, point, SInt.toInt_mk, Nat.shiftLeft_eq]

theorem mem_ofFrac (num : SInt) {den : ℕ} (hden : 0 < den) :
    Mem (((num.toInt : ℤ) : ℝ) / den) (ofFrac num den : IV P) := by
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have h1 := fdiv_mul_le (shiftLeft num P) hden
  have h2 := le_cdiv_mul (shiftLeft num P) hden
  rw [toInt_shiftLeft] at h1 h2
  have h1' : ((fdiv (shiftLeft num P) den).toInt : ℝ) * den ≤ (num.toInt : ℝ) * 2 ^ P := by
    exact_mod_cast h1
  have h2' : (num.toInt : ℝ) * 2 ^ P ≤ ((cdiv (shiftLeft num P) den).toInt : ℝ) * den := by
    exact_mod_cast h2
  have e : (num.toInt : ℝ) / den * 2 ^ P = (num.toInt : ℝ) * 2 ^ P / den := by ring
  simp only [Mem, ofFrac, e]
  constructor
  · rw [le_div_iff₀ hd]; exact h1'
  · rw [div_le_iff₀ hd]; exact h2'

/-! ### Exact operations -/

theorem mem_add {x y : ℝ} {a b : IV P} (ha : Mem x a) (hb : Mem y b) : Mem (x + y) (add a b) := by
  simp only [Mem, add, toInt_add, Int.cast_add] at *
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

theorem mem_neg {x : ℝ} {a : IV P} (ha : Mem x a) : Mem (-x) (neg a) := by
  simp only [Mem, neg, toInt_neg, Int.cast_neg] at *
  constructor <;> nlinarith [ha.1, ha.2]

theorem mem_sub {x y : ℝ} {a b : IV P} (ha : Mem x a) (hb : Mem y b) : Mem (x - y) (sub a b) := by
  simp only [Mem, sub, toInt_sub, Int.cast_sub] at *
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

theorem mem_addRad {x y : ℝ} {a : IV P} {r : ℕ} (ha : Mem x a) (hy : |y - x| * 2 ^ P ≤ r) :
    Mem y (addRad a r) := by
  have hp := two_pow_pos' P
  have h1 : (y - x) * 2 ^ P ≤ r :=
    (mul_le_mul_of_nonneg_right (le_abs_self (y - x)) hp.le).trans hy
  have h2 : -((y - x) * 2 ^ P) ≤ r := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le (y - x)) hp.le
    linarith
  simp only [Mem, addRad, toInt_sub, toInt_add, toInt_false, Int.cast_sub, Int.cast_add,
    Int.cast_natCast] at *
  constructor <;> nlinarith [ha.1, ha.2]

theorem mem_mulPow2 {x : ℝ} {a : IV P} (ha : Mem x a) (k : ℕ) : Mem (x * 2 ^ k) (mulPow2 a k) := by
  have hk := two_pow_pos' k
  simp only [Mem, mulPow2, toInt_shiftLeft, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at *
  constructor <;> nlinarith [ha.1, ha.2]

theorem mem_mulNat {x : ℝ} {a : IV P} (ha : Mem x a) (n : ℕ) : Mem (x * n) (mulNat a n) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Mem, mulNat, toInt_mulNat, Int.cast_mul, Int.cast_natCast] at *
  constructor <;> nlinarith [ha.1, ha.2]

/-! ### Rounded operations -/

/-- Floor division below a real: if `L ≤ z·d` (with `0 < d`) then `⌊L/d⌋ ≤ z`. -/
theorem fdiv_le_of {z : ℝ} {L : SInt} {d : ℕ} (hd : 0 < d) (hL : ((L.toInt : ℤ) : ℝ) ≤ z * d) :
    (((fdiv L d).toInt : ℤ) : ℝ) ≤ z := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (((fdiv L d).toInt : ℤ) : ℝ) * d ≤ L.toInt := by exact_mod_cast fdiv_mul_le L hd
  exact le_of_mul_le_mul_right (h1.trans hL) hd'

/-- Ceiling division above a real: if `z·d ≤ H` (with `0 < d`) then `z ≤ ⌈H/d⌉`. -/
theorem le_cdiv_of {z : ℝ} {H : SInt} {d : ℕ} (hd : 0 < d) (hH : z * d ≤ ((H.toInt : ℤ) : ℝ)) :
    z ≤ (((cdiv H d).toInt : ℤ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : ((H.toInt : ℤ) : ℝ) ≤ ((cdiv H d).toInt : ℝ) * d := by exact_mod_cast le_cdiv_mul H hd
  exact le_of_mul_le_mul_right (hH.trans h2) hd'

/-- Floor/ceiling rescaling of a real enclosure: if `L ≤ z·d ≤ H` (with `0 < d`), then
`⌊L/d⌋ ≤ z ≤ ⌈H/d⌉`. -/
theorem fdiv_cdiv_bounds {z : ℝ} {L H : SInt} {d : ℕ} (hd : 0 < d)
    (hL : ((L.toInt : ℤ) : ℝ) ≤ z * d) (hH : z * d ≤ ((H.toInt : ℤ) : ℝ)) :
    (((fdiv L d).toInt : ℤ) : ℝ) ≤ z ∧ z ≤ (((cdiv H d).toInt : ℤ) : ℝ) :=
  ⟨fdiv_le_of hd hL, le_cdiv_of hd hH⟩

theorem mem_divNat {x : ℝ} {a : IV P} (ha : Mem x a) {n : ℕ} (hn : 0 < n) :
    Mem (x / n) (divNat a n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : x / n * 2 ^ P * n = x * 2 ^ P := by field_simp
  obtain ⟨h1, -⟩ := fdiv_cdiv_bounds (z := x / n * 2 ^ P) (H := a.hi) hn (by rw [e]; exact ha.1)
    (by rw [e]; exact ha.2)
  obtain ⟨-, h2⟩ := fdiv_cdiv_bounds (z := x / n * 2 ^ P) (L := a.lo) hn (by rw [e]; exact ha.1)
    (by rw [e]; exact ha.2)
  exact ⟨h1, h2⟩

theorem mem_divPow2 {x : ℝ} {a : IV P} (ha : Mem x a) (k : ℕ) : Mem (x / 2 ^ k) (divPow2 a k) := by
  have h := mem_divNat ha (Nat.two_pow_pos k)
  have e : divPow2 a k = divNat a (2 ^ k) := by
    simp only [divPow2, divNat, fshift_eq_fdiv, cshift_eq_cdiv]
  rw [e]
  simpa using h

/-- Rescaling of corner products: if `L ≤ z·2^P·2^P ≤ H` then `z ∈ ofCorners L H`. -/
theorem mem_ofCorners {z : ℝ} {L H : SInt} (hL : ((L.toInt : ℤ) : ℝ) ≤ z * 2 ^ P * 2 ^ P)
    (hH : z * 2 ^ P * 2 ^ P ≤ ((H.toInt : ℤ) : ℝ)) : Mem z (ofCorners L H : IV P) := by
  have e : ofCorners L H = (⟨fdiv L (2 ^ P), cdiv H (2 ^ P)⟩ : IV P) := by
    simp only [ofCorners, fshift_eq_fdiv, cshift_eq_cdiv]
  rw [e]
  have hc : ((2 ^ P : ℕ) : ℝ) = 2 ^ P := by push_cast; ring
  obtain ⟨h1, h2⟩ := fdiv_cdiv_bounds (z := z * 2 ^ P) (Nat.two_pow_pos P) (by rw [hc]; exact hL)
    (by rw [hc]; exact hH)
  exact ⟨h1, h2⟩

/-- Corner bounds of a product `X·Y` for `al ≤ X ≤ ah`, `bl ≤ Y ≤ bh`, by sign class. -/
private theorem corner_bounds {al ah bl bh X Y : ℝ} (h1 : al ≤ X) (h2 : X ≤ ah) (h3 : bl ≤ Y)
    (h4 : Y ≤ bh) :
    (0 ≤ al → 0 ≤ bl → al * bl ≤ X * Y ∧ X * Y ≤ ah * bh) ∧
    (0 ≤ al → bh ≤ 0 → ah * bl ≤ X * Y ∧ X * Y ≤ al * bh) ∧
    (0 ≤ al → bl ≤ 0 → 0 ≤ bh → ah * bl ≤ X * Y ∧ X * Y ≤ ah * bh) ∧
    (ah ≤ 0 → 0 ≤ bl → al * bh ≤ X * Y ∧ X * Y ≤ ah * bl) ∧
    (ah ≤ 0 → bh ≤ 0 → ah * bh ≤ X * Y ∧ X * Y ≤ al * bl) ∧
    (ah ≤ 0 → bl ≤ 0 → 0 ≤ bh → al * bh ≤ X * Y ∧ X * Y ≤ al * bl) ∧
    (al ≤ 0 → 0 ≤ ah → 0 ≤ bl → al * bh ≤ X * Y ∧ X * Y ≤ ah * bh) ∧
    (al ≤ 0 → 0 ≤ ah → bh ≤ 0 → ah * bl ≤ X * Y ∧ X * Y ≤ al * bl) ∧
    (al ≤ 0 → 0 ≤ ah → bl ≤ 0 → 0 ≤ bh →
      min (al * bh) (ah * bl) ≤ X * Y ∧ X * Y ≤ max (al * bl) (ah * bh)) := by
  refine ⟨fun p q => ⟨?_, ?_⟩, fun p q => ⟨?_, ?_⟩, fun p q r => ⟨?_, ?_⟩, fun p q => ⟨?_, ?_⟩,
    fun p q => ⟨?_, ?_⟩, fun p q r => ⟨?_, ?_⟩, fun p q r => ⟨?_, ?_⟩, fun p q r => ⟨?_, ?_⟩,
    fun p q r s => ⟨?_, ?_⟩⟩
  all_goals try
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2)
      (sub_nonneg.2 h4), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h4),
      mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3)]
  · rcases le_total 0 X with hX | hX
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans (by nlinarith)
  · rcases le_total 0 X with hX | hX
    · exact (by nlinarith : X * Y ≤ ah * bh).trans (le_max_right _ _)
    · exact (by nlinarith : X * Y ≤ al * bl).trans (le_max_left _ _)

private theorem isNeg_false_nonneg {a : SInt} (h : a.isNeg = false) : (0 : ℝ) ≤ ((a.toInt : ℤ) : ℝ) := by
  exact_mod_cast toInt_nonneg_of_isNeg_false h

private theorem isNeg_true_nonpos {a : SInt} (h : a.isNeg = true) : ((a.toInt : ℤ) : ℝ) ≤ 0 := by
  exact_mod_cast toInt_nonpos_of_isNeg_true h

theorem mem_mul {x y : ℝ} {a b : IV P} (ha : Mem x a) (hb : Mem y b) : Mem (x * y) (mul a b) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  have e : x * y * 2 ^ P * 2 ^ P = (x * 2 ^ P) * (y * 2 ^ P) := by ring
  obtain ⟨cPP, cPN, cPM, cNP, cNN, cNM, cMP, cMN, cMM⟩ := corner_bounds h1 h2 h3 h4
  unfold mul
  cases hal : a.lo.isNeg <;> cases hah : a.hi.isNeg <;> cases hbl : b.lo.isNeg <;>
    cases hbh : b.hi.isNeg <;>
    simp only [Bool.cond_true, Bool.cond_false] <;>
    apply mem_ofCorners <;>
    simp only [e, toInt_mul, Int.cast_mul, toInt_min, toInt_max, Int.cast_min, Int.cast_max] <;>
    first
    | exact (cPP (isNeg_false_nonneg hal) (isNeg_false_nonneg hbl)).1
    | exact (cPP (isNeg_false_nonneg hal) (isNeg_false_nonneg hbl)).2
    | exact (cPN (isNeg_false_nonneg hal) (isNeg_true_nonpos hbh)).1
    | exact (cPN (isNeg_false_nonneg hal) (isNeg_true_nonpos hbh)).2
    | exact (cPM (isNeg_false_nonneg hal) (isNeg_true_nonpos hbl) (isNeg_false_nonneg hbh)).1
    | exact (cPM (isNeg_false_nonneg hal) (isNeg_true_nonpos hbl) (isNeg_false_nonneg hbh)).2
    | exact (cNP (isNeg_true_nonpos hah) (isNeg_false_nonneg hbl)).1
    | exact (cNP (isNeg_true_nonpos hah) (isNeg_false_nonneg hbl)).2
    | exact (cNN (isNeg_true_nonpos hah) (isNeg_true_nonpos hbh)).1
    | exact (cNN (isNeg_true_nonpos hah) (isNeg_true_nonpos hbh)).2
    | exact (cNM (isNeg_true_nonpos hah) (isNeg_true_nonpos hbl) (isNeg_false_nonneg hbh)).1
    | exact (cNM (isNeg_true_nonpos hah) (isNeg_true_nonpos hbl) (isNeg_false_nonneg hbh)).2
    | exact (cMP (isNeg_true_nonpos hal) (isNeg_false_nonneg hah) (isNeg_false_nonneg hbl)).1
    | exact (cMP (isNeg_true_nonpos hal) (isNeg_false_nonneg hah) (isNeg_false_nonneg hbl)).2
    | exact (cMN (isNeg_true_nonpos hal) (isNeg_false_nonneg hah) (isNeg_true_nonpos hbh)).1
    | exact (cMN (isNeg_true_nonpos hal) (isNeg_false_nonneg hah) (isNeg_true_nonpos hbh)).2
    | exact (cMM (isNeg_true_nonpos hal) (isNeg_false_nonneg hah) (isNeg_true_nonpos hbl)
        (isNeg_false_nonneg hbh)).1
    | exact (cMM (isNeg_true_nonpos hal) (isNeg_false_nonneg hah) (isNeg_true_nonpos hbl)
        (isNeg_false_nonneg hbh)).2

theorem mem_sq {x : ℝ} {a : IV P} (ha : Mem x a) : Mem (x ^ 2) (sq a) := by
  obtain ⟨h1, h2⟩ := ha
  have e : x ^ 2 * 2 ^ P * 2 ^ P = (x * 2 ^ P) * (x * 2 ^ P) := by ring
  unfold sq
  cases hal : a.lo.isNeg <;> cases hah : a.hi.isNeg <;>
    simp only [Bool.cond_true, Bool.cond_false] <;>
    apply mem_ofCorners <;>
    simp only [e, toInt_mul, Int.cast_mul, toInt_max, Int.cast_max, toInt_zero, Int.cast_zero]
  all_goals
    have l1 := isNeg_false_nonneg (a := a.lo)
    have l2 := isNeg_true_nonpos (a := a.lo)
    have u1 := isNeg_false_nonneg (a := a.hi)
    have u2 := isNeg_true_nonpos (a := a.hi)
  · have := l1 hal; nlinarith
  · have := l1 hal; nlinarith
  · have := l1 hal; nlinarith
  · have := l1 hal; nlinarith
  · exact mul_self_nonneg _
  · rcases le_total 0 (x * 2 ^ P) with hX | hX
    · exact (by nlinarith [u1 hah] : _ ≤ _).trans (le_max_right _ _)
    · exact (by nlinarith [l2 hal] : _ ≤ _).trans (le_max_left _ _)
  · have := u2 hah; nlinarith
  · have := u2 hah; nlinarith

theorem mem_divPos {x y : ℝ} {a b : IV P} (hpos : SInt.pos b.lo = true) (ha : Mem x a)
    (hb : Mem y b) : Mem (x / y) (divPos a b) := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  obtain ⟨hbm, hbn⟩ := pos_mag hpos
  have hp := two_pow_pos' P
  have eL : ((b.lo.toInt : ℤ) : ℝ) = b.lo.mag := by rw [toInt_eq, hbn]; simp
  have hbl : (0 : ℝ) < ((b.lo.toInt : ℤ) : ℝ) := by rw [eL]; exact_mod_cast hbm
  have hY : 0 < y * 2 ^ P := lt_of_lt_of_le hbl h3
  have hbh : (0 : ℝ) < ((b.hi.toInt : ℤ) : ℝ) := lt_of_lt_of_le hY h4
  have hbhn : b.hi.isNeg = false := by
    cases hc : b.hi.isNeg
    · rfl
    · have := isNeg_true_nonpos hc; linarith
  have eH : ((b.hi.toInt : ℤ) : ℝ) = b.hi.mag := by rw [toInt_eq, hbhn]; simp
  have hbhm : 0 < b.hi.mag := by have := eH ▸ hbh; exact_mod_cast this
  have hy0 : y ≠ 0 := by
    rintro rfl; simp at hY
  have hzY : x / y * 2 ^ P * (y * 2 ^ P) = x * 2 ^ P * 2 ^ P := by field_simp
  -- the shape of every case: `L·Y ≤ X·dl` and `X·dh ≤ H·Y`
  have fin : ∀ (L H : SInt) (dl dh : ℕ), 0 < dl → 0 < dh →
      ((L.toInt : ℤ) : ℝ) * (y * 2 ^ P) ≤ x * 2 ^ P * dl →
      x * 2 ^ P * dh ≤ ((H.toInt : ℤ) : ℝ) * (y * 2 ^ P) →
      Mem (x / y) (⟨fdiv (shiftLeft L P) dl, cdiv (shiftLeft H P) dh⟩ : IV P) := by
    intro L H dl dh hdl hdh hL hH
    have hzl : ((shiftLeft L P).toInt : ℝ) ≤ x / y * 2 ^ P * dl := by
      rw [toInt_shiftLeft]; push_cast
      apply le_of_mul_le_mul_right _ hY
      calc (L.toInt : ℝ) * 2 ^ P * (y * 2 ^ P) = ((L.toInt : ℝ) * (y * 2 ^ P)) * 2 ^ P := by ring
        _ ≤ (x * 2 ^ P * dl) * 2 ^ P := mul_le_mul_of_nonneg_right hL hp.le
        _ = x / y * 2 ^ P * dl * (y * 2 ^ P) := by linear_combination (-(dl : ℝ)) * hzY
    have hzh : x / y * 2 ^ P * dh ≤ ((shiftLeft H P).toInt : ℝ) := by
      rw [toInt_shiftLeft]; push_cast
      apply le_of_mul_le_mul_right _ hY
      calc x / y * 2 ^ P * dh * (y * 2 ^ P) = (x * 2 ^ P * dh) * 2 ^ P := by
            linear_combination (dh : ℝ) * hzY
        _ ≤ ((H.toInt : ℝ) * (y * 2 ^ P)) * 2 ^ P := mul_le_mul_of_nonneg_right hH hp.le
        _ = (H.toInt : ℝ) * 2 ^ P * (y * 2 ^ P) := by ring
    exact ⟨(fdiv_le_of hdl hzl), (le_cdiv_of hdh hzh)⟩
  unfold divPos
  cases hal : a.lo.isNeg <;> cases hah : a.hi.isNeg <;> simp only [Bool.cond_true, Bool.cond_false]
  · have hal0 := isNeg_false_nonneg hal
    refine fin _ _ _ _ hbhm hbm ?_ ?_
    · rw [← eH]; nlinarith
    · rw [← eL]; nlinarith
  · have hal0 := isNeg_false_nonneg hal
    refine fin _ _ _ _ hbhm hbm ?_ ?_
    · rw [← eH]; nlinarith
    · rw [← eL]; nlinarith
  · have hal0 := isNeg_true_nonpos hal
    have hah0 := isNeg_false_nonneg hah
    refine fin _ _ _ _ hbm hbm ?_ ?_
    · rw [← eL]
      rcases le_total 0 (x * 2 ^ P) with hX | hX <;> nlinarith
    · rw [← eL]
      rcases le_total 0 (x * 2 ^ P) with hX | hX <;> nlinarith
  · have hah0 := isNeg_true_nonpos hah
    refine fin _ _ _ _ hbm hbhm ?_ ?_
    · rw [← eL]; nlinarith
    · rw [← eH]; nlinarith

/-! ### Hull and tests -/

theorem mem_hull_left {x : ℝ} {a b : IV P} (ha : Mem x a) : Mem x (hull a b) := by
  simp only [Mem, hull, toInt_min, toInt_max, Int.cast_min, Int.cast_max] at *
  exact ⟨(min_le_left _ _).trans ha.1, ha.2.trans (le_max_left _ _)⟩

theorem mem_hull_right {x : ℝ} {a b : IV P} (hb : Mem x b) : Mem x (hull a b) := by
  simp only [Mem, hull, toInt_min, toInt_max, Int.cast_min, Int.cast_max] at *
  exact ⟨(min_le_right _ _).trans hb.1, hb.2.trans (le_max_right _ _)⟩

theorem ltB_sound {x y : ℝ} {a b : IV P} (h : ltB a b = true) (ha : Mem x a) (hb : Mem y b) :
    x < y := by
  have h' : ((a.hi.toInt : ℤ) : ℝ) < b.lo.toInt := by exact_mod_cast (blt_iff _ _).mp h
  have hp := two_pow_pos' P
  have := ha.2.trans_lt (h'.trans_le hb.1)
  exact lt_of_mul_lt_mul_right this hp.le

theorem leB_sound {x y : ℝ} {a b : IV P} (h : leB a b = true) (ha : Mem x a) (hb : Mem y b) :
    x ≤ y := by
  have h' : ((a.hi.toInt : ℤ) : ℝ) ≤ b.lo.toInt := by exact_mod_cast (ble_iff _ _).mp h
  have hp := two_pow_pos' P
  have := ha.2.trans (h'.trans hb.1)
  exact le_of_mul_le_mul_right this hp

theorem posB_sound {x : ℝ} {a : IV P} (h : posB a = true) (ha : Mem x a) : 0 < x := by
  have h' : (0 : ℝ) < a.lo.toInt := by exact_mod_cast (pos_iff _).mp h
  have hp := two_pow_pos' P
  exact pos_of_mul_pos_left (h'.trans_le ha.1) hp.le

theorem mem_of_subsetB {x : ℝ} {a b : IV P} (h : subsetB a b = true) (ha : Mem x a) : Mem x b := by
  simp only [subsetB, Bool.and_eq_true] at h
  have h1 : ((b.lo.toInt : ℤ) : ℝ) ≤ a.lo.toInt := by exact_mod_cast (ble_iff _ _).mp h.1
  have h2 : ((a.hi.toInt : ℤ) : ℝ) ≤ b.hi.toInt := by exact_mod_cast (ble_iff _ _).mp h.2
  exact ⟨h1.trans ha.1, ha.2.trans h2⟩

/-! ### Square roots checked by squaring -/

theorem mem_sqrt_of_sqrtCheck {x : ℝ} {a : IV P} {l h : ℕ} (hc : sqrtCheck a l h = true)
    (ha : Mem x a) : Mem (Real.sqrt x) (ofNatPair l h : IV P) := by
  simp only [sqrtCheck, Bool.and_eq_true] at hc
  obtain ⟨hhi, hh, hl⟩ := hc
  have hp := two_pow_pos' P
  have hP2 : (0 : ℝ) < 2 ^ P * 2 ^ P := by positivity
  have hsq : Real.sqrt x * 2 ^ P = Real.sqrt (x * 2 ^ P * 2 ^ P) := by
    rw [mul_assoc x, Real.sqrt_mul' _ hP2.le, Real.sqrt_mul_self hp.le]
  simp only [Mem, ofNatPair, toInt_false, Int.cast_natCast]
  rw [hsq]
  constructor
  · cases hlo : a.lo.isNeg
    · rw [hlo] at hl
      simp only [Bool.cond_false, Nat.ble_eq, nat_shiftLeft_eq] at hl
      have hl' : ((l : ℝ)) * l ≤ (a.lo.mag : ℝ) * 2 ^ P := by exact_mod_cast hl
      have hlo' : ((a.lo.toInt : ℤ) : ℝ) = a.lo.mag := by rw [toInt_eq, hlo]; simp
      have hX := ha.1
      rw [hlo'] at hX
      apply Real.le_sqrt_of_sq_le
      nlinarith
    · rw [hlo] at hl
      simp only [Bool.cond_true, Nat.beq_eq] at hl
      rw [hl]; simp
  · have hh' : (a.hi.mag : ℝ) * 2 ^ P ≤ (h : ℝ) * h := by
      simp only [Nat.ble_eq, nat_shiftLeft_eq] at hh
      exact_mod_cast hh
    have hhi' : ((a.hi.toInt : ℤ) : ℝ) ≤ a.hi.mag := by
      rw [toInt_eq]; split_ifs <;> simp
    have hX := ha.2
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith

end IV

end SandierSerfaty.Certificate.Arith
