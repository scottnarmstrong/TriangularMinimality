/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.Log
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Soundness of the logarithm enclosures

* `atanhSeries_partial_le`, `atanhSeries_le_partial_add_tail`: for `0 ≤ w < 1`, the partial sums of
  `Σ 2 w^(2k+1)/(2k+1)` bound `log (1 + w) - log (1 - w)` from below, and from above after adding the tail
  bound `2 w^(2N+1) / ((2N+1)(1 - w²))` (Mathlib `Real.hasSum_log_sub_log_of_abs_lt_one` and a geometric
  comparison);
* `atanhLo_le`, `le_atanhHi`: the rounded `Nat` chains of `SandierSerfaty.Certificate.Arith.Log` respect these
  bounds;
* `mem_logPoint`: `log (m / 2^P) ∈ logPoint P G N l2lo l2hi m` for `0 < m`, given an enclosure of `log 2`;
* `log2Lo144_le`, `le_log2Hi144`: the literal enclosure of `log 2` (kernel-checked against the series);
* `IV.mem_logPos`: `log x ∈ IV.logPos a` for `x ∈ a` and `0 < a.lo`.
-/

public section

namespace SandierSerfaty.Certificate.Arith

open Real Finset

/-- The `k`-th term `2 w^(2k+1)/(2k+1)` of the series of `log (1 + w) - log (1 - w)`. -/
noncomputable def atanhTerm (w : ℝ) (k : ℕ) : ℝ := 2 * (1 / (2 * k + 1)) * w ^ (2 * k + 1)

theorem atanhTerm_nonneg {w : ℝ} (hw : 0 ≤ w) (k : ℕ) : 0 ≤ atanhTerm w k := by
  unfold atanhTerm; positivity

theorem hasSum_atanhTerm {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) :
    HasSum (atanhTerm w) (log (1 + w) - log (1 - w)) := by
  have := Real.hasSum_log_sub_log_of_abs_lt_one (x := w) (by rw [abs_of_nonneg h0]; exact h1)
  exact this

theorem atanhSeries_partial_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (N : ℕ) :
    ∑ i ∈ range N, atanhTerm w i ≤ log (1 + w) - log (1 - w) :=
  sum_le_hasSum (range N) (fun i _ => atanhTerm_nonneg h0 i) (hasSum_atanhTerm h0 h1)

theorem atanhSeries_le_partial_add_tail {w : ℝ} (h0 : 0 ≤ w) (h1 : w < 1) (N : ℕ) :
    log (1 + w) - log (1 - w) ≤
      ∑ i ∈ range N, atanhTerm w i + 2 * w ^ (2 * N + 1) / ((2 * N + 1) * (1 - w ^ 2)) := by
  have hs := hasSum_atanhTerm h0 h1
  have htail := (hasSum_nat_add_iff' N).mpr hs
  have hw2 : w ^ 2 < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg w) hw2).mul_left
    (2 * (1 / (2 * N + 1)) * w ^ (2 * N + 1))
  have hle : ∀ i, atanhTerm w (i + N) ≤
      2 * (1 / (2 * N + 1)) * w ^ (2 * N + 1) * (w ^ 2) ^ i := by
    intro i
    unfold atanhTerm
    have e : w ^ (2 * (i + N : ℕ) + 1) = w ^ (2 * N + 1) * (w ^ 2) ^ i := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e]
    have hd : (1 : ℝ) / (2 * ((i + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * N + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hp : 0 ≤ w ^ (2 * N + 1) * (w ^ 2) ^ i := by positivity
    nlinarith
  have := hasSum_le hle htail hg
  have e2 : 2 * (1 / (2 * (N : ℝ) + 1)) * w ^ (2 * N + 1) * (1 - w ^ 2)⁻¹ =
      2 * w ^ (2 * N + 1) / ((2 * N + 1) * (1 - w ^ 2)) := by
    field_simp
  rw [e2] at this
  linarith

/-! ### The rounded chains -/

private theorem cast_div_le' (x d : ℕ) : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le

private theorem div_le_cdivNat (x d : ℕ) (hd : 0 < d) : (x : ℝ) / d ≤ (SInt.cdivNat x d : ℝ) := by
  have h := SInt.le_cdivNat_mul x d hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  exact_mod_cast h

theorem atanhLoAux_le {a b : ℕ} (hb : 0 < b) (Q : ℝ) :
    ∀ (n k p acc : ℕ), (p : ℝ) ≤ ((a : ℝ) / b) ^ (2 * k + 1) * Q →
      (acc : ℝ) ≤ (∑ i ∈ range k, atanhTerm ((a : ℝ) / b) i) * Q →
      (atanhLoAux (a * a) (b * b) n k p acc : ℝ) ≤
        (∑ i ∈ range (k + n), atanhTerm ((a : ℝ) / b) i) * Q := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  intro n
  induction n with
  | zero => intro k p acc _ hacc; simpa [atanhLoAux] using hacc
  | succ n ih =>
    intro k p acc hp hacc
    simp only [atanhLoAux, Nat.add_eq, Nat.mul_eq, SInt.nat_div_eq]
    rw [show k + (n + 1) = (k + 1) + n by ring]
    apply ih
    · calc ((p * (a * a) / (b * b) : ℕ) : ℝ) ≤ ((p * (a * a) : ℕ) : ℝ) / ((b * b : ℕ) : ℝ) :=
            cast_div_le' _ _
        _ = (p : ℝ) * (((a : ℝ) / b) ^ 2) := by push_cast; field_simp
        _ ≤ ((a : ℝ) / b) ^ (2 * k + 1) * Q * (((a : ℝ) / b) ^ 2) :=
            mul_le_mul_of_nonneg_right hp (by positivity)
        _ = ((a : ℝ) / b) ^ (2 * (k + 1) + 1) * Q := by ring
    · rw [sum_range_succ]
      calc ((acc + 2 * p / (2 * k + 1) : ℕ) : ℝ) ≤ (acc : ℝ) + (2 * p : ℕ) / ((2 * k + 1 : ℕ) : ℝ) := by
            have := cast_div_le' (2 * p) (2 * k + 1)
            rw [Nat.cast_add]; linarith
        _ ≤ (∑ i ∈ range k, atanhTerm ((a : ℝ) / b) i) * Q +
              2 * (((a : ℝ) / b) ^ (2 * k + 1) * Q) / (2 * k + 1) := by
            push_cast
            gcongr
        _ = _ := by unfold atanhTerm; ring

theorem le_atanhHiAux {a b : ℕ} (hab : a < b) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∀ (n k p acc : ℕ), ((a : ℝ) / b) ^ (2 * k + 1) * Q ≤ p →
      (∑ i ∈ range k, atanhTerm ((a : ℝ) / b) i) * Q ≤ acc →
      (log (1 + (a : ℝ) / b) - log (1 - (a : ℝ) / b)) * Q ≤
        (atanhHiAux (a * a) (b * b) n k p acc : ℝ) := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hw0 : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hw1 : (a : ℝ) / b < 1 := by rw [div_lt_one hb']; exact_mod_cast hab
  set w := (a : ℝ) / b with hw
  intro n
  induction n with
  | zero =>
    intro k p acc hp hacc
    simp only [atanhHiAux, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    have hba : 0 < b * b - a * a := by
      have : a * a < b * b := Nat.mul_self_lt_mul_self hab
      omega
    have hden : 0 < (2 * k + 1) * (b * b - a * a) := Nat.mul_pos (by omega) hba
    have hc := div_le_cdivNat (2 * p * (b * b)) _ hden
    have hS := atanhSeries_le_partial_add_tail hw0 hw1 k
    have hcast : (((b * b - a * a : ℕ)) : ℝ) = (b : ℝ) * b - a * a := by
      rw [Nat.cast_sub (Nat.mul_le_mul hab.le hab.le)]; push_cast; ring
    have h1w : (0 : ℝ) < 1 - w ^ 2 := by nlinarith
    -- the tail term dominates
    have htail : 2 * w ^ (2 * k + 1) / ((2 * k + 1) * (1 - w ^ 2)) * Q ≤
        ((2 * p * (b * b) : ℕ) : ℝ) / (((2 * k + 1) * (b * b - a * a) : ℕ) : ℝ) := by
      have hD : (0 : ℝ) < (b : ℝ) * b - a * a := by
        rw [← hcast]; exact_mod_cast hba
      have e1 : 1 - w ^ 2 = ((b : ℝ) * b - a * a) / (b * b) := by rw [hw]; field_simp
      have e : ((2 * p * (b * b) : ℕ) : ℝ) / (((2 * k + 1) * (b * b - a * a) : ℕ) : ℝ) =
          2 * (p : ℝ) / ((2 * k + 1) * (1 - w ^ 2)) := by
        rw [show (((2 * k + 1) * (b * b - a * a) : ℕ) : ℝ) = (2 * (k : ℝ) + 1) * ((b : ℝ) * b - a * a) by
          rw [Nat.cast_mul, hcast]; push_cast; ring, e1]
        push_cast
        field_simp
      rw [e, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    push_cast
    nlinarith
  | succ n ih =>
    intro k p acc hp hacc
    simp only [atanhHiAux, Nat.add_eq, Nat.mul_eq]
    apply ih
    · have hbb : 0 < b * b := Nat.mul_pos hb hb
      calc w ^ (2 * (k + 1) + 1) * Q = w ^ (2 * k + 1) * Q * w ^ 2 := by ring
        _ ≤ (p : ℝ) * w ^ 2 := mul_le_mul_of_nonneg_right hp (by positivity)
        _ = ((p * (a * a) : ℕ) : ℝ) / ((b * b : ℕ) : ℝ) := by rw [hw]; push_cast; field_simp
        _ ≤ _ := div_le_cdivNat _ _ hbb
    · rw [sum_range_succ]
      have hk : 0 < 2 * k + 1 := by omega
      have hc := div_le_cdivNat (2 * p) (2 * k + 1) hk
      push_cast at hc ⊢
      have : atanhTerm w k * Q ≤ 2 * (p : ℝ) / (2 * k + 1) := by
        unfold atanhTerm
        rw [show 2 * (1 / (2 * (k : ℝ) + 1)) * w ^ (2 * k + 1) * Q =
          2 * (w ^ (2 * k + 1) * Q) / (2 * k + 1) by ring]
        gcongr
      nlinarith

theorem atanhLo_le {a b : ℕ} (hab : a < b) (W N : ℕ) :
    (atanhLo a b W N : ℝ) ≤ (log (1 + (a : ℝ) / b) - log (1 - (a : ℝ) / b)) * 2 ^ W := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hw0 : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  have hw1 : (a : ℝ) / b < 1 := by rw [div_lt_one hb']; exact_mod_cast hab
  have h := atanhLoAux_le (a := a) hb (2 ^ W) N 0 ((a <<< W) / b) 0 (by
      calc (((a <<< W) / b : ℕ) : ℝ) ≤ ((a <<< W : ℕ) : ℝ) / b := cast_div_le' _ _
        _ = ((a : ℝ) / b) ^ (2 * 0 + 1) * 2 ^ W := by
            rw [Nat.shiftLeft_eq]; push_cast; ring) (by simp)
  have hS := atanhSeries_partial_le hw0 hw1 N
  simp only [zero_add] at h
  unfold atanhLo
  simp only [Nat.mul_eq, SInt.nat_div_eq, Nat.shiftLeft_eq'] at h ⊢
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right hS (by positivity)

theorem le_atanhHi {a b : ℕ} (hab : a < b) (W N : ℕ) :
    (log (1 + (a : ℝ) / b) - log (1 - (a : ℝ) / b)) * 2 ^ W ≤ (atanhHi a b W N : ℝ) := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
  unfold atanhHi
  simp only [Nat.mul_eq]
  apply le_atanhHiAux hab (2 ^ W) (by positivity) N 0
  · calc ((a : ℝ) / b) ^ (2 * 0 + 1) * 2 ^ W = ((Nat.shiftLeft a W : ℕ) : ℝ) / b := by
          rw [SInt.nat_shiftLeft_eq]; push_cast; ring
      _ ≤ _ := div_le_cdivNat _ _ hb
  · simp

/-! ### The logarithm at a point -/

/-- `log (1 + w) - log (1 - w) = log ((m) / t)` for `w = (m - t)/(m + t)`, `0 < t ≤ m`. -/
private theorem atanh_eq_log_div {m t : ℝ} (ht : 0 < t) (hm : 0 < m) :
    log (1 + (m - t) / (m + t)) - log (1 - (m - t) / (m + t)) = log m - log t := by
  have hmt : 0 < m + t := by linarith
  have e1 : 1 + (m - t) / (m + t) = 2 * m / (m + t) := by field_simp; ring
  have e2 : 1 - (m - t) / (m + t) = 2 * t / (m + t) := by field_simp; ring
  rw [e1, e2, log_div (by positivity) hmt.ne', log_div (by positivity) hmt.ne',
    log_mul (by norm_num) hm.ne', log_mul (by norm_num) ht.ne']
  ring

/-- Bounds of `log (m / t)·2^W` from `logYLo`/`logYHi`, `t = 2^s`. -/
theorem logY_bounds {W N m t : ℕ} (hm : 0 < m) (ht : 0 < t) :
    (((logYLo W N m t).toInt : ℤ) : ℝ) ≤ (log m - log t) * 2 ^ W ∧
      (log m - log t) * 2 ^ W ≤ (((logYHi W N m t).toInt : ℤ) : ℝ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  unfold logYLo logYHi
  by_cases h : t ≤ m
  · have hb : m - t < m + t := by omega
    have hc : ((m - t : ℕ) : ℝ) / ((m + t : ℕ) : ℝ) = ((m : ℝ) - t) / (m + t) := by
      rw [Nat.cast_sub h]; push_cast; ring
    have l := atanhLo_le hb (W) N
    have u := le_atanhHi hb (W) N
    rw [hc, atanh_eq_log_div ht' hm'] at l u
    simp only [Nat.ble_eq_true_of_le h, Bool.cond_true, SInt.toInt_false, Int.cast_natCast,
      Nat.sub_eq, Nat.add_eq]
    exact ⟨l, u⟩
  · push Not at h
    have hb : t - m < m + t := by omega
    have hc : ((t - m : ℕ) : ℝ) / ((m + t : ℕ) : ℝ) = ((t : ℝ) - m) / (t + m) := by
      rw [Nat.cast_sub h.le]; push_cast; ring
    have l := atanhLo_le hb (W) N
    have u := le_atanhHi hb (W) N
    rw [hc, atanh_eq_log_div hm' ht'] at l u
    have hn : Nat.ble t m = false := by
      rw [Bool.eq_false_iff]; intro hc; exact absurd (Nat.le_of_ble_eq_true hc) (not_le.mpr h)
    simp only [hn, Bool.cond_false, SInt.toInt_true, Int.cast_neg, Int.cast_natCast, Nat.sub_eq,
      Nat.add_eq]
    constructor <;> nlinarith

theorem toInt_shiftDiff (s P : ℕ) : (shiftDiff s P).toInt = (s : ℤ) - P := by
  unfold shiftDiff
  by_cases h : P ≤ s
  · simp [Nat.ble_eq_true_of_le h, Nat.sub_eq]; omega
  · have hn : Nat.ble P s = false := by
      rw [Bool.eq_false_iff]; intro hc; exact h (Nat.le_of_ble_eq_true hc)
    simp [hn, Nat.sub_eq]; omega

theorem mulLog2_bounds (c : SInt) {l2lo l2hi : ℕ} {W : ℕ} (hl : (l2lo : ℝ) ≤ log 2 * 2 ^ W)
    (hh : log 2 * 2 ^ W ≤ l2hi) :
    (((mulLog2Lo c l2lo l2hi).toInt : ℤ) : ℝ) ≤ ((c.toInt : ℤ) : ℝ) * log 2 * 2 ^ W ∧
      ((c.toInt : ℤ) : ℝ) * log 2 * 2 ^ W ≤ (((mulLog2Hi c l2lo l2hi).toInt : ℤ) : ℝ) := by
  have hc0 : (0 : ℝ) ≤ c.mag := Nat.cast_nonneg _
  rcases c with ⟨_ | _, n⟩
  · simp only [mulLog2Lo, mulLog2Hi, Bool.cond_false, SInt.toInt_false, Nat.mul_eq] at hc0 ⊢
    push_cast
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hc0, mul_le_mul_of_nonneg_left hh hc0]
  · simp only [mulLog2Lo, mulLog2Hi, Bool.cond_true, SInt.toInt_true, Nat.mul_eq] at hc0 ⊢
    push_cast
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hc0, mul_le_mul_of_nonneg_left hh hc0]

/-- `log (m / 2^P)` lies in `logPoint P G N l2lo l2hi m` for `0 < m`, given `l2lo ≤ log 2·2^(P+G) ≤ l2hi`. -/
theorem mem_logPoint (P G N l2lo l2hi : ℕ) {m : ℕ} (hm : 0 < m)
    (hl : (l2lo : ℝ) ≤ log 2 * 2 ^ (P + G)) (hh : log 2 * 2 ^ (P + G) ≤ l2hi) :
    IV.Mem (log ((m : ℝ) / 2 ^ P)) (logPoint P G N l2lo l2hi m) := by
  set s := logShift m
  have ht : 0 < Nat.shiftLeft 1 s := by rw [SInt.nat_shiftLeft_eq]; positivity
  have htv : ((Nat.shiftLeft 1 s : ℕ) : ℝ) = 2 ^ s := by rw [SInt.nat_shiftLeft_eq]; push_cast; ring
  obtain ⟨yl, yh⟩ := logY_bounds (W := P + G) (N := N) hm ht
  obtain ⟨cl, ch⟩ := mulLog2_bounds (shiftDiff s P) hl hh
  rw [htv, toInt_shiftDiff] at *
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : log ((m : ℝ) / 2 ^ P) =
      (log m - log ((2 : ℝ) ^ s)) + (((s : ℤ) - P : ℤ) : ℝ) * log 2 := by
    rw [log_div hm'.ne' (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
  have hW : (2 : ℝ) ^ (P + G) = 2 ^ P * 2 ^ G := pow_add _ _ _
  have hG : (0 : ℝ) < 2 ^ G := by positivity
  set L := SInt.add (logYLo (Nat.add P G) N m (Nat.shiftLeft 1 s))
    (mulLog2Lo (shiftDiff s P) l2lo l2hi)
  set H := SInt.add (logYHi (Nat.add P G) N m (Nat.shiftLeft 1 s))
    (mulLog2Hi (shiftDiff s P) l2lo l2hi)
  have hL : ((L.toInt : ℤ) : ℝ) ≤ log ((m : ℝ) / 2 ^ P) * 2 ^ P * 2 ^ G := by
    simp only [L, SInt.toInt_add, Int.cast_add, Nat.add_eq]
    rw [key, mul_assoc _ (2 ^ P : ℝ), ← hW]
    linarith
  have hH : log ((m : ℝ) / 2 ^ P) * 2 ^ P * 2 ^ G ≤ ((H.toInt : ℤ) : ℝ) := by
    simp only [H, SInt.toInt_add, Int.cast_add, Nat.add_eq]
    rw [key, mul_assoc _ (2 ^ P : ℝ), ← hW]
    linarith
  have f1 : ((SInt.fshift L G).toInt : ℝ) * 2 ^ G ≤ L.toInt := by
    exact_mod_cast SInt.fshift_mul_le L G
  have f2 : ((H.toInt : ℤ) : ℝ) ≤ ((SInt.cshift H G).toInt : ℝ) * 2 ^ G := by
    exact_mod_cast SInt.le_cshift_mul H G
  refine ⟨?_, ?_⟩
  · exact le_of_mul_le_mul_right (f1.trans hL) hG
  · exact le_of_mul_le_mul_right (hH.trans f2) hG

/-! ### The literal enclosure of `log 2` and the interval logarithm -/

theorem log2Lo144_eq : log2Lo144 = atanhLo 1 3 144 50 := by decide +kernel

theorem log2Hi144_eq : log2Hi144 = atanhHi 1 3 144 50 := by decide +kernel

private theorem log_two_eq_atanh : log (1 + ((1 : ℕ) : ℝ) / (3 : ℕ)) - log (1 - ((1 : ℕ) : ℝ) / (3 : ℕ)) =
    log 2 := by
  rw [← log_div (by norm_num) (by norm_num)]; norm_num

theorem log2Lo144_le : (log2Lo144 : ℝ) ≤ log 2 * 2 ^ (128 + 16) := by
  rw [log2Lo144_eq, ← log_two_eq_atanh]
  exact atanhLo_le (by norm_num) 144 50

theorem le_log2Hi144 : log 2 * 2 ^ (128 + 16) ≤ (log2Hi144 : ℝ) := by
  rw [log2Hi144_eq, ← log_two_eq_atanh]
  exact le_atanhHi (by norm_num) 144 50

namespace IV

theorem mem_logPos {x : ℝ} {a : IV 128} (hpos : posB a = true) (ha : Mem x a) :
    Mem (log x) (logPos a) := by
  obtain ⟨hlm, hln⟩ := SInt.pos_mag hpos
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have eL : ((a.lo.toInt : ℤ) : ℝ) = a.lo.mag := by rw [SInt.toInt_eq, hln]; simp
  have hlo : (0 : ℝ) < a.lo.mag := by exact_mod_cast hlm
  have hx : (a.lo.mag : ℝ) / 2 ^ 128 ≤ x := by
    rw [div_le_iff₀ hp, ← eL]; exact ha.1
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hhi0 : (0 : ℝ) < ((a.hi.toInt : ℤ) : ℝ) := lt_of_lt_of_le (by positivity) ha.2
  have hhn : a.hi.isNeg = false := by
    cases hc : a.hi.isNeg
    · rfl
    · have := SInt.toInt_nonpos_of_isNeg_true hc
      have : ((a.hi.toInt : ℤ) : ℝ) ≤ 0 := by exact_mod_cast this
      linarith
  have eH : ((a.hi.toInt : ℤ) : ℝ) = a.hi.mag := by rw [SInt.toInt_eq, hhn]; simp
  have hhm : 0 < a.hi.mag := by
    have : (0 : ℝ) < a.hi.mag := eH ▸ hhi0
    exact_mod_cast this
  have hxh : x ≤ (a.hi.mag : ℝ) / 2 ^ 128 := by
    rw [le_div_iff₀ hp, ← eH]; exact ha.2
  obtain ⟨l1, -⟩ := mem_logPoint 128 16 32 log2Lo144 log2Hi144 hlm log2Lo144_le le_log2Hi144
  obtain ⟨-, u1⟩ := mem_logPoint 128 16 32 log2Lo144 log2Hi144 hhm log2Lo144_le le_log2Hi144
  refine ⟨?_, ?_⟩
  · exact l1.trans (mul_le_mul_of_nonneg_right (log_le_log (by positivity) hx) hp.le)
  · exact (mul_le_mul_of_nonneg_right (log_le_log hx0 hxh) hp.le).trans u1

end IV

end SandierSerfaty.Certificate.Arith
