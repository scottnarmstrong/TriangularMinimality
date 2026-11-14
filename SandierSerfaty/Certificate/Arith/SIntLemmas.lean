/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.SInt
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Laws of the sign-magnitude integers

Every operation of `SandierSerfaty.Certificate.Arith.SInt` is related to `Int` through `SInt.toInt`:
addition, negation, subtraction, products and left shifts are exact (`toInt_add`, ...); the floor and ceiling
divisions and shifts satisfy the one-sided bounds `fdiv_mul_le`, `le_cdiv_mul`, `fshift_mul_le`,
`le_cshift_mul`; truncation `tshift` is within one unit; and the Boolean comparisons decide
`≤` and `<` (`ble_iff`, `blt_iff`, ...). These are the integer-level laws behind the interval and fixed-point
laws of `IVLemmas` and `FxLemmas`.
-/

public section

namespace SandierSerfaty.Certificate.Arith

namespace SInt

/-! ### Normal forms of the `Nat` primitives -/

theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nat_shiftRight_eq (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b :=
  Nat.shiftRight_eq_div_pow a b

theorem nat_shiftLeft_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem cond_eq_ite' {α : Type*} (c : Bool) (x y : α) : cond c x y = if c = true then x else y := by
  cases c <;> rfl

@[simp] theorem toInt_mk (b : Bool) (m : ℕ) : (⟨b, m⟩ : SInt).toInt = if b then -(m : ℤ) else m := by
  cases b <;> rfl

theorem toInt_false (m : ℕ) : (⟨false, m⟩ : SInt).toInt = m := rfl

theorem toInt_true (m : ℕ) : (⟨true, m⟩ : SInt).toInt = -(m : ℤ) := rfl

theorem toInt_eq (a : SInt) : a.toInt = if a.isNeg then -(a.mag : ℤ) else a.mag := by
  cases a; exact toInt_mk _ _

theorem toInt_nonneg_of_isNeg_false {a : SInt} (h : a.isNeg = false) : 0 ≤ a.toInt := by
  rw [toInt_eq, h]; simp

theorem toInt_nonpos_of_isNeg_true {a : SInt} (h : a.isNeg = true) : a.toInt ≤ 0 := by
  rw [toInt_eq, h]; simp

theorem abs_toInt (a : SInt) : |a.toInt| = a.mag := by
  rw [toInt_eq]; split_ifs <;> simp

@[simp] theorem toInt_ofNat (n : ℕ) : (ofNat n).toInt = n := rfl

@[simp] theorem toInt_zero : zero.toInt = 0 := rfl

/-! ### Exact operations -/

@[simp] theorem toInt_neg (a : SInt) : (neg a).toInt = -a.toInt := by
  rcases a with ⟨_ | _, m⟩ <;> simp [neg]

theorem toInt_subMag (an : Bool) (am bm : ℕ) :
    (subMag an am bm).toInt = (⟨an, am⟩ : SInt).toInt - (⟨an, bm⟩ : SInt).toInt := by
  unfold subMag
  rw [cond_eq_ite']
  cases an <;> by_cases h : bm ≤ am <;> simp [h, Nat.sub_eq] <;> omega

@[simp] theorem toInt_add (a b : SInt) : (add a b).toInt = a.toInt + b.toInt := by
  rcases a with ⟨_ | _, m⟩ <;> rcases b with ⟨_ | _, n⟩ <;>
    simp only [add, Bool.cond_false, Bool.cond_true, toInt_subMag, toInt_mk, Nat.add_eq] <;> simp <;> omega

@[simp] theorem toInt_sub (a b : SInt) : (sub a b).toInt = a.toInt - b.toInt := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem toInt_mul (a b : SInt) : (mul a b).toInt = a.toInt * b.toInt := by
  rcases a with ⟨_ | _, m⟩ <;> rcases b with ⟨_ | _, n⟩ <;> simp [mul, xorSign, Nat.mul_eq]

@[simp] theorem toInt_mulNat (a : SInt) (n : ℕ) : (mulNat a n).toInt = a.toInt * n := by
  rcases a with ⟨_ | _, m⟩ <;> simp [mulNat, Nat.mul_eq]

@[simp] theorem toInt_shiftLeft (a : SInt) (k : ℕ) : (shiftLeft a k).toInt = a.toInt * 2 ^ k := by
  rcases a with ⟨_ | _, m⟩ <;> simp [shiftLeft, Nat.shiftLeft_eq]

/-! ### Rounded divisions and shifts -/

theorem cdivNat_eq (m d : ℕ) : cdivNat m d = (m + d - 1) / d := rfl

/-- `⌈m/d⌉·d ≥ m`. -/
theorem le_cdivNat_mul (m d : ℕ) (hd : 0 < d) : m ≤ cdivNat m d * d := by
  rw [cdivNat_eq]
  have h1 := Nat.div_add_mod (m + d - 1) d
  have h2 := Nat.mod_lt (m + d - 1) hd
  have h3 : d * ((m + d - 1) / d) = (m + d - 1) / d * d := Nat.mul_comm _ _
  omega

theorem cshiftNat_eq (m k : ℕ) : cshiftNat m k = cdivNat m (2 ^ k) := by
  simp only [cshiftNat, cdivNat, nat_shiftRight_eq, nat_shiftLeft_eq, Nat.add_eq, Nat.sub_eq,
    nat_div_eq, one_mul]

/-- Floor division: `⌊a/d⌋·d ≤ a`. -/
theorem fdiv_mul_le (a : SInt) {d : ℕ} (hd : 0 < d) : (fdiv a d).toInt * d ≤ a.toInt := by
  rcases a with ⟨_ | _, m⟩
  · simp only [fdiv, Bool.cond_false, toInt_mk, nat_div_eq]
    simp only [Bool.false_eq_true, ite_false]
    exact_mod_cast Nat.div_mul_le_self m d
  · simp only [fdiv, Bool.cond_true, toInt_mk, ite_true]
    have := le_cdivNat_mul m d hd
    have : (m : ℤ) ≤ (cdivNat m d : ℤ) * d := by exact_mod_cast this
    linarith

/-- Ceiling division: `a ≤ ⌈a/d⌉·d`. -/
theorem le_cdiv_mul (a : SInt) {d : ℕ} (hd : 0 < d) : a.toInt ≤ (cdiv a d).toInt * d := by
  rcases a with ⟨_ | _, m⟩
  · simp only [cdiv, Bool.cond_false, toInt_mk]
    simp only [Bool.false_eq_true, ite_false]
    exact_mod_cast le_cdivNat_mul m d hd
  · simp only [cdiv, Bool.cond_true, toInt_mk, ite_true, nat_div_eq]
    have := Nat.div_mul_le_self m d
    have : ((m / d : ℕ) : ℤ) * d ≤ m := by exact_mod_cast this
    linarith

theorem fshift_eq_fdiv (a : SInt) (k : ℕ) : fshift a k = fdiv a (2 ^ k) := by
  rcases a with ⟨_ | _, m⟩ <;> simp [fshift, fdiv, cshiftNat_eq, Nat.shiftRight_eq_div_pow, nat_div_eq]

theorem cshift_eq_cdiv (a : SInt) (k : ℕ) : cshift a k = cdiv a (2 ^ k) := by
  rcases a with ⟨_ | _, m⟩ <;> simp [cshift, cdiv, cshiftNat_eq, Nat.shiftRight_eq_div_pow, nat_div_eq]

/-- Floor shift: `⌊a/2^k⌋·2^k ≤ a`. -/
theorem fshift_mul_le (a : SInt) (k : ℕ) : (fshift a k).toInt * 2 ^ k ≤ a.toInt := by
  rw [fshift_eq_fdiv]
  exact_mod_cast fdiv_mul_le a (Nat.two_pow_pos k)

/-- Ceiling shift: `a ≤ ⌈a/2^k⌉·2^k`. -/
theorem le_cshift_mul (a : SInt) (k : ℕ) : a.toInt ≤ (cshift a k).toInt * 2 ^ k := by
  rw [cshift_eq_cdiv]
  exact_mod_cast le_cdiv_mul a (Nat.two_pow_pos k)

/-- Truncation toward zero: `|trunc(a/2^k)·2^k - a| < 2^k`. -/
theorem abs_tshift_mul_sub_lt (a : SInt) (k : ℕ) :
    |(tshift a k).toInt * 2 ^ k - a.toInt| < 2 ^ k := by
  have hp : (0 : ℤ) < 2 ^ k := by positivity
  have h1 := Nat.div_mul_le_self a.mag (2 ^ k)
  have h2 := Nat.lt_div_mul_add (a := a.mag) (Nat.two_pow_pos k)
  have c1 : ((a.mag / 2 ^ k : ℕ) : ℤ) * 2 ^ k ≤ a.mag := by exact_mod_cast h1
  have c2 : (a.mag : ℤ) < ((a.mag / 2 ^ k : ℕ) : ℤ) * 2 ^ k + 2 ^ k := by exact_mod_cast h2
  rcases a with ⟨_ | _, m⟩ <;>
    simp only [tshift, toInt_mk, nat_shiftRight_eq, Bool.false_eq_true, ite_false, ite_true] at c1 c2 ⊢ <;>
    rw [abs_lt] <;> constructor <;> linarith

/-! ### Comparisons -/

theorem ble_iff (a b : SInt) : ble a b = true ↔ a.toInt ≤ b.toInt := by
  rcases a with ⟨_ | _, m⟩ <;> rcases b with ⟨_ | _, n⟩ <;>
    simp [ble, Nat.add_eq]
  omega

theorem blt_iff (a b : SInt) : blt a b = true ↔ a.toInt < b.toInt := by
  unfold blt
  rw [Bool.not_eq_true', ← Bool.not_eq_true, ble_iff, not_le]

theorem nonneg_iff (a : SInt) : nonneg a = true ↔ 0 ≤ a.toInt := by
  rcases a with ⟨_ | _, m⟩ <;> simp [nonneg]

theorem pos_iff (a : SInt) : pos a = true ↔ 0 < a.toInt := by
  rcases a with ⟨_ | _, m⟩ <;> simp [pos]

theorem pos_mag {a : SInt} (h : pos a = true) : 0 < a.mag ∧ a.isNeg = false := by
  rcases a with ⟨_ | _, m⟩ <;> simp_all [pos]

theorem toInt_min (a b : SInt) : (min a b).toInt = Min.min a.toInt b.toInt := by
  unfold min
  cases h : ble a b
  · have : ¬ a.toInt ≤ b.toInt := by rw [← ble_iff, h]; simp
    simp only [Bool.cond_false]
    rw [min_eq_right (le_of_lt (not_le.mp this))]
  · have : a.toInt ≤ b.toInt := (ble_iff a b).mp h
    simp only [Bool.cond_true]
    rw [min_eq_left this]

theorem toInt_max (a b : SInt) : (max a b).toInt = Max.max a.toInt b.toInt := by
  unfold max
  cases h : ble a b
  · have : ¬ a.toInt ≤ b.toInt := by rw [← ble_iff, h]; simp
    simp only [Bool.cond_false]
    rw [max_eq_left (le_of_lt (not_le.mp this))]
  · have : a.toInt ≤ b.toInt := (ble_iff a b).mp h
    simp only [Bool.cond_true]
    rw [max_eq_right this]

end SInt

end SandierSerfaty.Certificate.Arith
