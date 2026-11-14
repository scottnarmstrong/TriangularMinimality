/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.Fx
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import SandierSerfaty.Certificate.Arith.Interface

/-!
# Error laws of the midpoint fixed point

`Fx.val a = a.v / 2^P`. The exact operations of `SandierSerfaty.Certificate.Arith.Fx` satisfy equalities
(`val_add`, ...); the truncated product, quotient and shift are within one ulp `2^-P` of the exact result
(`abs_val_mul_sub_lt`, `abs_val_div_sub_lt`, `abs_val_divPow2_sub_lt`); a checked square root is within one
ulp (`abs_sqrt_sub_lt_of_sqrtCheck`). These are the per-operation laws from which a static error budget
is assembled.
-/

public section

namespace SandierSerfaty.Certificate.Arith

namespace Fx

open SInt

variable {P : ℕ}

/-- The real denoted by a fixed-point number. -/
@[expose] noncomputable def val (a : Fx P) : ℝ := ((a.v.toInt : ℤ) : ℝ) / 2 ^ P

theorem val_def (a : Fx P) : a.val = ((a.v.toInt : ℤ) : ℝ) / 2 ^ P := rfl

private theorem two_pow_pos'' (k : ℕ) : (0 : ℝ) < 2 ^ k := by positivity

theorem val_mul_two_pow (a : Fx P) : a.val * 2 ^ P = a.v.toInt := by
  rw [val_def, div_mul_cancel₀ _ (two_pow_pos'' P).ne']

/-! ### Exact operations -/

@[simp] theorem val_ofSInt (v : SInt) : (ofSInt v : Fx P).val = ((v.toInt : ℤ) : ℝ) / 2 ^ P := rfl

@[simp] theorem val_add (a b : Fx P) : (add a b).val = a.val + b.val := by
  simp only [val_def, add, toInt_add, Int.cast_add, add_div]

@[simp] theorem val_sub (a b : Fx P) : (sub a b).val = a.val - b.val := by
  simp only [val_def, sub, toInt_sub, Int.cast_sub, sub_div]

/-! ### Rounded operations: one ulp -/

/-- The truncated product is within one ulp. -/
theorem abs_val_mul_sub_lt (a b : Fx P) : |(mul a b).val - a.val * b.val| < 1 / 2 ^ P := by
  have hp := two_pow_pos'' P
  have h := abs_tshift_mul_sub_lt (SInt.mul a.v b.v) P
  rw [toInt_mul] at h
  have h' : |((tshift (SInt.mul a.v b.v) P).toInt : ℝ) * 2 ^ P - a.v.toInt * b.v.toInt| < 2 ^ P := by
    exact_mod_cast h
  have e : (mul a b).val - a.val * b.val =
      (((tshift (SInt.mul a.v b.v) P).toInt : ℝ) * 2 ^ P - a.v.toInt * b.v.toInt) /
        (2 ^ P * 2 ^ P) := by
    simp only [val_def, mul]; field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P * 2 ^ P),
    div_lt_div_iff₀ (by positivity) hp]
  nlinarith

/-- The truncated division by `2^k` is within one ulp. -/
theorem abs_val_divPow2_sub_lt (a : Fx P) (k : ℕ) :
    |(divPow2 a k).val - a.val / 2 ^ k| < 1 / 2 ^ P := by
  have hp := two_pow_pos'' P
  have hk := two_pow_pos'' k
  have h := abs_tshift_mul_sub_lt a.v k
  have h' : |((tshift a.v k).toInt : ℝ) * 2 ^ k - a.v.toInt| < 2 ^ k := by exact_mod_cast h
  have e : (divPow2 a k).val - a.val / 2 ^ k =
      (((tshift a.v k).toInt : ℝ) * 2 ^ k - a.v.toInt) / (2 ^ P * 2 ^ k) := by
    simp only [val_def, divPow2]; field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P * 2 ^ k),
    div_lt_div_iff₀ (by positivity) hp]
  nlinarith

/-- The truncated quotient is within one ulp (for a nonzero divisor). -/
theorem abs_val_div_sub_lt (a b : Fx P) (hb : b.v.mag ≠ 0) :
    |(div a b).val - a.val / b.val| < 1 / 2 ^ P := by
  have hp := two_pow_pos'' P
  have hbm : (0 : ℝ) < b.v.mag := by exact_mod_cast Nat.pos_of_ne_zero hb
  set q := (a.v.mag * 2 ^ P) / b.v.mag with hq
  have q1 : q * b.v.mag ≤ a.v.mag * 2 ^ P := Nat.div_mul_le_self _ _
  have q2 : a.v.mag * 2 ^ P < q * b.v.mag + b.v.mag := Nat.lt_div_mul_add (Nat.pos_of_ne_zero hb)
  have r1 : (q : ℝ) * b.v.mag ≤ a.v.mag * 2 ^ P := by exact_mod_cast q1
  have r2 : (a.v.mag : ℝ) * 2 ^ P < q * b.v.mag + b.v.mag := by exact_mod_cast q2
  -- the magnitudes: `|q / 2^P - (am / bm)| < 1 / 2^P`
  have hmag : |(q : ℝ) / 2 ^ P - (a.v.mag : ℝ) / b.v.mag| < 1 / 2 ^ P := by
    have e : (q : ℝ) / 2 ^ P - (a.v.mag : ℝ) / b.v.mag =
        ((q : ℝ) * b.v.mag - a.v.mag * 2 ^ P) / (2 ^ P * b.v.mag) := by field_simp
    have hD : |(q : ℝ) * b.v.mag - a.v.mag * 2 ^ P| < b.v.mag := by
      rw [abs_lt]; constructor <;> linarith
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P * b.v.mag),
      div_lt_div_iff₀ (by positivity) hp]
    nlinarith
  -- the common sign
  set σ : ℝ := if SInt.xorSign a.v.isNeg b.v.isNeg then -1 else 1 with hσ
  have hσ1 : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have ed : (div a b).val = σ * ((q : ℝ) / 2 ^ P) := by
    simp only [val_def, div, toInt_mk, nat_div_eq, nat_shiftLeft_eq, hσ, ← hq]
    split_ifs <;> push_cast <;> ring
  have eab : a.val / b.val = σ * ((a.v.mag : ℝ) / b.v.mag) := by
    have ea : a.val = (if a.v.isNeg then -(a.v.mag : ℝ) else a.v.mag) / 2 ^ P := by
      rw [val_def, toInt_eq]; split_ifs <;> simp
    have eb : b.val = (if b.v.isNeg then -(b.v.mag : ℝ) else b.v.mag) / 2 ^ P := by
      rw [val_def, toInt_eq]; split_ifs <;> simp
    rw [ea, eb, hσ]
    have hb0 : (b.v.mag : ℝ) ≠ 0 := hbm.ne'
    have hp0 : (2 : ℝ) ^ P ≠ 0 := hp.ne'
    cases a.v.isNeg <;> cases b.v.isNeg <;> simp [SInt.xorSign] <;> field_simp
  rw [ed, eab, ← mul_sub, abs_mul, hσ1, one_mul]
  exact hmag

/-! ### Conversions, comparisons, square roots -/

theorem ble_iff (a b : Fx P) : ble a b = true ↔ a.val ≤ b.val := by
  rw [ble, SInt.ble_iff, val_def, val_def, div_le_div_iff_of_pos_right (two_pow_pos'' P)]
  exact_mod_cast Iff.rfl

/-- A checked square root is within one ulp: `|s/2^P - √a| < 2^-P`. -/
theorem abs_sqrt_sub_lt_of_sqrtCheck {a : Fx P} {s : ℕ} (h : sqrtCheck a s = true) :
    |(ofSInt ⟨false, s⟩ : Fx P).val - Real.sqrt a.val| < 1 / 2 ^ P := by
  simp only [sqrtCheck, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq, Nat.add_eq,
    nat_shiftLeft_eq] at h
  obtain ⟨hn, h1, h2⟩ := h
  have hp := two_pow_pos'' P
  have hnn := (nonneg_iff _).mp hn
  have em : ((a.v.toInt : ℤ) : ℝ) = a.v.mag := by
    have : a.v.toInt = a.v.mag := by
      rw [toInt_eq] at hnn ⊢
      split_ifs at hnn ⊢ <;> omega
    rw [this]; push_cast; rfl
  -- `√a · 2^P = √(m · 2^P)` with `m` the magnitude
  have hsq : Real.sqrt a.val * 2 ^ P = Real.sqrt ((a.v.mag : ℝ) * 2 ^ P) := by
    rw [val_def, em]
    have : (a.v.mag : ℝ) / 2 ^ P = (a.v.mag : ℝ) * 2 ^ P / (2 ^ P * 2 ^ P) := by field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hp.le, div_mul_cancel₀ _ hp.ne']
  have l1 : (s : ℝ) * s ≤ a.v.mag * 2 ^ P := by exact_mod_cast h1
  have l2 : (a.v.mag : ℝ) * 2 ^ P < (s + 1) * (s + 1) := by exact_mod_cast h2
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have r1 : (s : ℝ) ≤ Real.sqrt ((a.v.mag : ℝ) * 2 ^ P) := Real.le_sqrt_of_sq_le (by nlinarith)
  have r2 : Real.sqrt ((a.v.mag : ℝ) * 2 ^ P) < s + 1 := by
    rw [Real.sqrt_lt' (by positivity)]; nlinarith
  have e : (ofSInt ⟨false, s⟩ : Fx P).val - Real.sqrt a.val =
      ((s : ℝ) - Real.sqrt ((a.v.mag : ℝ) * 2 ^ P)) / 2 ^ P := by
    rw [val_ofSInt, toInt_false, ← hsq]; push_cast; field_simp
  rw [e, abs_div, abs_of_pos hp, div_lt_div_iff_of_pos_right hp, abs_lt]
  constructor <;> linarith

end Fx

end SandierSerfaty.Certificate.Arith
