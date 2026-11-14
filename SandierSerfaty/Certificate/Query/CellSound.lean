/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Cell
public import SandierSerfaty.Certificate.Query.Taylor
public import SandierSerfaty.Certificate.Arith.FxLemmas
public import SandierSerfaty.Certificate.Basis.CoreSound

/-!
# Soundness of the cell check

`chanCheck_sound`: if `chanCheck v u c2 n0 n1 lo hi tb fb f1 r = true`, and `F` is a function with
`F' = F₁`, `F₁' = F₂` on a real cell `[a, b]` (`a ∈ v`, `b ∈ u`), `F₂ ∈ c2` on the cell, `F b ∈ n0`, `F₁ b ∈ n1`,
then for every `t ∈ [lo, hi]` (the real numbers denoted by the dyadic `lo`, `hi`): `a ≤ t ≤ b` and

  `|F t - (fb + f1 (t - tb))| ≤ r / 2^128`.

The proof splits the error as in `Query.Taylor`:
`F t - fb - f1 (t - tb) = [F t - F b - F₁ b (t - b)] + [F b - fb] + [(F₁ b - f1)(t - b)] + f1 (tb - b)`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table

theorem two_pow_pos128 : (0 : ℝ) < 2 ^ 128 := by positivity

/-- The real denoted by a dyadic times `2^128` is its integer mantissa. -/
theorem fx_mul (x : Fx 128) : x.val * 2 ^ 128 = ((x.v.toInt : ℤ) : ℝ) := Fx.val_mul_two_pow x

/-- `span b a` is the real difference `b - a` of the integer mantissas when `a ≤ b`. -/
theorem span_cast {a b : SInt} (h : a.toInt ≤ b.toInt) :
    (span b a : ℝ) = ((b.toInt : ℤ) : ℝ) - ((a.toInt : ℤ) : ℝ) := by
  unfold span
  have h1 : |(SInt.sub b a).toInt| = ((SInt.sub b a).mag : ℤ) := SInt.abs_toInt _
  rw [SInt.toInt_sub] at h1
  have h2 : (0 : ℤ) ≤ b.toInt - a.toInt := by omega
  rw [abs_of_nonneg h2] at h1
  have h3 : (((SInt.sub b a).mag : ℤ) : ℝ) = ((b.toInt - a.toInt : ℤ) : ℝ) := by rw [h1]
  push_cast at h3
  exact_mod_cast h3

theorem le_of_ble {a b : SInt} (h : SInt.ble a b = true) : a.toInt ≤ b.toInt := (SInt.ble_iff a b).mp h

theorem cast_le_of_ble {a b : SInt} (h : SInt.ble a b = true) :
    ((a.toInt : ℤ) : ℝ) ≤ ((b.toInt : ℤ) : ℝ) := by exact_mod_cast le_of_ble h

theorem cast_shl (k : ℕ) : ((Nat.shiftLeft 1 k : ℕ) : ℝ) = 2 ^ k := by
  rw [SInt.nat_shiftLeft_eq]; simp

theorem abs_le_div_of {x w N : ℝ} (hN : 0 < N) (h1 : -w ≤ x * N) (h2 : x * N ≤ w) : |x| ≤ w / N := by
  have : |x * N| ≤ w := abs_le.2 ⟨h1, h2⟩
  rw [abs_mul, abs_of_pos hN] at this
  rwa [le_div_iff₀ hN]

theorem span_cast' {a b : SInt} (h : ((a.toInt : ℤ) : ℝ) ≤ ((b.toInt : ℤ) : ℝ)) :
    (span b a : ℝ) = ((b.toInt : ℤ) : ℝ) - ((a.toInt : ℤ) : ℝ) := span_cast (by exact_mod_cast h)

/-- The cell range check puts every `t ∈ [lo, hi]` inside the real cell `[a, b]`. -/
theorem chanCheck_range {v u c2 n0 n1 : IV 128} {lo hi tb fb f1 : Fx 128} {r : ℕ} {a b t : ℝ}
    (hc : chanCheck v u c2 n0 n1 lo hi tb fb f1 r = true) (hv : IV.Mem a v) (hu : IV.Mem b u)
    (hlo : lo.val ≤ t) (hhi : t ≤ hi.val) : a ≤ t ∧ t ≤ b := by
  have hN := two_pow_pos128
  simp only [chanCheck, Bool.and_eq_true] at hc
  obtain ⟨c1, c2', -⟩ := hc
  have k1 := cast_le_of_ble c1
  have k2 := cast_le_of_ble c2'
  have hlo' := fx_mul lo
  have hhi' := fx_mul hi
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  constructor
  · have h1 : lo.val * 2 ^ 128 ≤ t * 2 ^ 128 := mul_le_mul_of_nonneg_right hlo hN.le
    exact le_of_mul_le_mul_right (by linarith) hN
  · have h1 : t * 2 ^ 128 ≤ hi.val * 2 ^ 128 := mul_le_mul_of_nonneg_right hhi hN.le
    exact le_of_mul_le_mul_right (by linarith) hN

/-- **Soundness of one channel check.** -/
theorem chanCheck_sound {F F₁ F₂ : ℝ → ℝ} {a b : ℝ} {v u c2 n0 n1 : IV 128} {lo hi tb fb f1 : Fx 128}
    {r : ℕ} (hc : chanCheck v u c2 n0 n1 lo hi tb fb f1 r = true)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F₁ x) x) (hF₁ : ∀ x ∈ Icc a b, HasDerivAt F₁ (F₂ x) x)
    (hc2 : ∀ x ∈ Icc a b, IV.Mem (F₂ x) c2) (hn0 : IV.Mem (F b) n0) (hn1 : IV.Mem (F₁ b) n1)
    (hv : IV.Mem a v) (hu : IV.Mem b u) {t : ℝ} (hlo : lo.val ≤ t) (hhi : t ≤ hi.val) :
    a ≤ t ∧ t ≤ b ∧ |F t - (fb.val + f1.val * (t - tb.val))| ≤ r / 2 ^ 128 := by
  have hN := two_pow_pos128
  simp only [chanCheck, Bool.and_eq_true] at hc
  obtain ⟨c1, c2', ⟨c3, c4⟩, ⟨c5, c6⟩, ⟨c7, c8⟩, c9⟩ := hc
  have k1 := cast_le_of_ble c1
  have k2 := cast_le_of_ble c2'
  have k3 := cast_le_of_ble c3
  have k4 := cast_le_of_ble c4
  have k5 := cast_le_of_ble c5
  have k6 := cast_le_of_ble c6
  have k7 := cast_le_of_ble c7
  have k8 := cast_le_of_ble c8
  have hlo' := fx_mul lo
  have hhi' := fx_mul hi
  have htb' := fx_mul tb
  have hfb' := fx_mul fb
  have hf1' := fx_mul f1
  obtain ⟨hv1, hv2⟩ := hv
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hm1, hm2⟩ := hn0
  obtain ⟨hq1, hq2⟩ := hn1
  have hsq : ((2 : ℝ) ^ 256) = (2 ^ 128) ^ 2 := by rw [← pow_mul]
  have hMs : ∀ x ∈ Icc a b, |F₂ x| ≤ (magHi c2 : ℝ) / 2 ^ 128 := fun x hx => abs_le_magHi (hc2 x hx)
  have hmag : |f1.val| = (f1.v.mag : ℝ) / 2 ^ 128 := by
    rw [Fx.val_def, abs_div, abs_of_pos hN, ← Int.cast_abs, SInt.abs_toInt]
    simp
  have h9 := Nat.ble_eq.mp c9
  simp only [Nat.mul_eq, SInt.nat_shiftLeft_eq, one_mul] at h9
  have h9' : (chanErr v u c2 n0 n1 f1 : ℝ) ≤ 2 * ((r : ℝ) * 2 ^ 256) := by exact_mod_cast h9
  rw [hsq] at h9'
  -- the point `t` lies in the cell
  have hta : a ≤ t := by
    have h1 : lo.val * 2 ^ 128 ≤ t * 2 ^ 128 := mul_le_mul_of_nonneg_right hlo hN.le
    exact le_of_mul_le_mul_right (by linarith) hN
  have htb : t ≤ b := by
    have h1 : t * 2 ^ 128 ≤ hi.val * 2 ^ 128 := mul_le_mul_of_nonneg_right hhi hN.le
    exact le_of_mul_le_mul_right (by linarith) hN
  refine ⟨hta, htb, ?_⟩
  have hab : a * 2 ^ 128 ≤ b * 2 ^ 128 := mul_le_mul_of_nonneg_right (hta.trans htb) hN.le
  have hat : a * 2 ^ 128 ≤ t * 2 ^ 128 := mul_le_mul_of_nonneg_right hta hN.le
  have htI : t ∈ Icc a b := ⟨hta, htb⟩
  -- Taylor remainder
  have hT := abs_taylor_le hF hF₁ hMs htI
  -- the spans
  have hH := span_cast' (a := v.lo) (b := u.hi) (by linarith)
  have hWu := span_cast' (a := u.lo) (b := u.hi) (by linarith)
  have hW0 := span_cast' (a := n0.lo) (b := n0.hi) (by linarith)
  have hW1 := span_cast' (a := n1.lo) (b := n1.hi) (by linarith)
  have hE : (chanErr v u c2 n0 n1 f1 : ℝ) = (magHi c2 : ℝ) * (((u.hi.toInt : ℤ) : ℝ) - v.lo.toInt) ^ 2 +
      2 * (((n0.hi.toInt : ℤ) : ℝ) - n0.lo.toInt) * (2 ^ 128) ^ 2 +
      2 * (((n1.hi.toInt : ℤ) : ℝ) - n1.lo.toInt) * (((u.hi.toInt : ℤ) : ℝ) - v.lo.toInt) * 2 ^ 128 +
      2 * (f1.v.mag : ℝ) * (((u.hi.toInt : ℤ) : ℝ) - u.lo.toInt) * 2 ^ 128 := by
    unfold chanErr
    simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, cast_shl, Nat.cast_ofNat]
    rw [hH, hWu, hW0, hW1]
    ring
  generalize hNg : (2 : ℝ) ^ 128 = N at *
  generalize hHw : ((u.hi.toInt : ℤ) : ℝ) - v.lo.toInt = hw at *
  generalize hWuu : ((u.hi.toInt : ℤ) : ℝ) - u.lo.toInt = wu at *
  generalize hW00 : ((n0.hi.toInt : ℤ) : ℝ) - n0.lo.toInt = w0 at *
  generalize hW11 : ((n1.hi.toInt : ℤ) : ℝ) - n1.lo.toInt = w1 at *
  have e1' : 0 ≤ b - t := by linarith
  have e1 : b - t ≤ hw / N := by
    rw [le_div_iff₀ hN]; linarith
  have e2 : |b - tb.val| ≤ wu / N :=
    abs_le_div_of hN (by linarith) (by linarith)
  have e3 : |F b - fb.val| ≤ w0 / N :=
    abs_le_div_of hN (by linarith) (by linarith)
  have e4 : |F₁ b - f1.val| ≤ w1 / N :=
    abs_le_div_of hN (by linarith) (by linarith)
  have hdec : F t - (fb.val + f1.val * (t - tb.val)) =
      (F t - F b - F₁ b * (t - b)) + (F b - fb.val) + (F₁ b - f1.val) * (t - b) + f1.val * (tb.val - b) := by
    ring
  have hMn : 0 ≤ (magHi c2 : ℝ) / N := by positivity
  have s1 : |F t - F b - F₁ b * (t - b)| ≤ (magHi c2 : ℝ) / N * (hw / N) ^ 2 / 2 := by
    refine hT.trans ?_
    have h2 : (b - t) ^ 2 ≤ (hw / N) ^ 2 := pow_le_pow_left₀ e1' e1 2
    have h3 := mul_le_mul_of_nonneg_left h2 hMn
    linarith only [h3]
  have s2 : |(F₁ b - f1.val) * (t - b)| ≤ w1 / N * (hw / N) := by
    rw [abs_mul, show |t - b| = b - t by rw [abs_sub_comm, abs_of_nonneg e1']]
    exact mul_le_mul e4 e1 e1' ((abs_nonneg _).trans e4)
  have s3 : |f1.val * (tb.val - b)| ≤ (f1.v.mag : ℝ) / N * (wu / N) := by
    rw [abs_mul, hmag, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left e2 (by positivity)
  rw [hdec]
  have habs : |(F t - F b - F₁ b * (t - b)) + (F b - fb.val) + (F₁ b - f1.val) * (t - b) +
      f1.val * (tb.val - b)| ≤ |F t - F b - F₁ b * (t - b)| + |F b - fb.val| +
        |(F₁ b - f1.val) * (t - b)| + |f1.val * (tb.val - b)| :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hsum : (magHi c2 : ℝ) / N * (hw / N) ^ 2 / 2 + w0 / N +
      w1 / N * (hw / N) + (f1.v.mag : ℝ) / N * (wu / N) =
      (chanErr v u c2 n0 n1 f1 : ℝ) / (2 * N ^ 3) := by
    rw [hE]; field_simp
  have hfin : (chanErr v u c2 n0 n1 f1 : ℝ) / (2 * N ^ 3) ≤ r / N := by
    rw [div_le_div_iff₀ (by positivity) hN]
    have h4 : 0 ≤ N := hN.le
    calc (chanErr v u c2 n0 n1 f1 : ℝ) * N ≤ 2 * ((r : ℝ) * N ^ 2) * N := mul_le_mul_of_nonneg_right h9' h4
      _ = r * (2 * N ^ 3) := by ring
  linarith only [s1, e3, s2, s3, habs, hsum, hfin]

end SandierSerfaty.Certificate.Query
