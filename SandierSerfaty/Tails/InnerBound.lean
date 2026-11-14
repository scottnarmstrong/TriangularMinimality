/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.UBound

/-!
# The inner continuation: `|b_m^{(j)}| ≤ 3·10⁶ k³ 2^{-k}` on `[p - c, p]` (paper §6.2)

On `seg 1 = [p - c, p]` the spline `b_m` is `bPoly m r = S((r - p + c)/c) q_m(r)` with the quadratic
`q_m(r) = T_{0m} + T_{1m}(r - p) + T_{2m}(r - p)²` (`Calibration.bPoly`). Using `|c_m| ≤ 7/(k a^k)` and
`p/a = 1/2`, `p > 1/2`:

* `abs_T0_le`, `abs_T1_le`, `abs_T2_le`: `|T_0| ≤ (7/k) 2^{-k}`, `|T_1| ≤ 14 k 2^{-k}`,
  `|T_2| ≤ (14/3) k³ 2^{-k}` (paper §6.2);
* `BJ_bPoly`: all jet bounds of `b_m` on `seg 1` are `3·10⁶ k³ 2^{-k}` (paper §6.2); the paper's constant is
  `8500`, the cruder value follows from `|q^{(i)}| ≤ 10 k³ 2^{-k}` and the Leibniz constant `282879`.
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- `2^{-k}`. -/
@[expose] noncomputable def twoPowInv (m : ℕ) : ℝ := ((2 : ℝ) ^ (k m))⁻¹

theorem twoPowInv_pos (m : ℕ) : 0 < twoPowInv m := by unfold twoPowInv; positivity

theorem abs_T0_le {m : ℕ} (hm : 2 ≤ m) : |T0 m| ≤ 7 / (k m : ℝ) * twoPowInv m := by
  have h := abs_coeff_mul_pow_le hm (x := p) p_pos.le
  rw [p_div_a] at h
  unfold T0 twoPowInv
  rw [abs_mul, abs_of_nonneg (pow_nonneg p_pos.le _)]
  refine h.trans (le_of_eq ?_)
  rw [one_div, inv_pow]

theorem k_ge_twelve {m : ℕ} (hm : 2 ≤ m) : (12 : ℝ) ≤ (k m : ℝ) := by
  rw [k_of_pos (by omega)]; exact_mod_cast (by omega : 12 ≤ 6 * m)

theorem abs_T1_le {m : ℕ} (hm : 2 ≤ m) : |T1 m| ≤ 14 * (k m : ℝ) * twoPowInv m := by
  have hk := k_ge_twelve hm
  have hp := half_lt_p
  have hQ := twoPowInv_pos m
  have h0 := abs_T0_le hm
  have hκ0 : (0 : ℝ) < (k m : ℝ) := by linarith
  set κ : ℝ := (k m : ℝ) with hκ
  have e : |T1 m| = κ * (κ - 1) / p * |T0 m| := by
    unfold T1
    rw [abs_mul, abs_div, abs_neg, abs_of_nonneg (by nlinarith : 0 ≤ κ * (κ - 1)),
      abs_of_pos p_pos]
  rw [e]
  have h1 : κ * (κ - 1) / p ≤ 2 * κ ^ 2 := by
    rw [div_le_iff₀ p_pos]; nlinarith
  calc κ * (κ - 1) / p * |T0 m| ≤ 2 * κ ^ 2 * (7 / κ * twoPowInv m) := by
        gcongr
    _ = 14 * κ * twoPowInv m := by field_simp; ring

theorem abs_T2_le {m : ℕ} (hm : 2 ≤ m) : |T2 m| ≤ 14 / 3 * (k m : ℝ) ^ 3 * twoPowInv m := by
  have hk := k_ge_twelve hm
  have hp := half_lt_p
  have hQ := twoPowInv_pos m
  have h0 := abs_T0_le hm
  have hκ0 : (0 : ℝ) < (k m : ℝ) := by linarith
  set κ : ℝ := (k m : ℝ) with hκ
  have hX0 : 0 ≤ (κ - 2) * (κ - 3) / 6 - 1 / 2 := by nlinarith
  have hX1 : (κ - 2) * (κ - 3) / 6 - 1 / 2 ≤ κ ^ 2 / 6 := by nlinarith
  have e : |T2 m| = κ * (κ - 1) / p ^ 2 * ((κ - 2) * (κ - 3) / 6 - 1 / 2) * |T0 m| := by
    unfold T2
    rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (by nlinarith : 0 ≤ κ * (κ - 1)),
      abs_of_pos (pow_pos p_pos 2), abs_of_nonneg hX0]
  rw [e]
  have hp2 : 1 / 4 < p ^ 2 := by nlinarith
  have h1 : κ * (κ - 1) / p ^ 2 ≤ 4 * κ ^ 2 := by
    rw [div_le_iff₀ (pow_pos p_pos 2)]; nlinarith
  have hA : 0 ≤ κ * (κ - 1) / p ^ 2 := by
    apply div_nonneg (by nlinarith) (by positivity)
  calc κ * (κ - 1) / p ^ 2 * ((κ - 2) * (κ - 3) / 6 - 1 / 2) * |T0 m|
      ≤ 4 * κ ^ 2 * (κ ^ 2 / 6) * (7 / κ * twoPowInv m) := by
        gcongr
    _ = 14 / 3 * κ ^ 3 * twoPowInv m := by field_simp; ring

/-- `F = k³ 2^{-k}`, the size of the inner continuation (paper §6.2). -/
@[expose] noncomputable def innerF (m : ℕ) : ℝ := (k m : ℝ) ^ 3 * twoPowInv m

theorem innerF_nonneg (m : ℕ) : 0 ≤ innerF m := by
  unfold innerF; have := twoPowInv_pos m; positivity

theorem abs_T_le_five {m : ℕ} (hm : 2 ≤ m) :
    |T0 m| ≤ 5 * innerF m ∧ |T1 m| ≤ 5 * innerF m ∧ |T2 m| ≤ 5 * innerF m := by
  have hk := k_ge_twelve hm
  have hQ := twoPowInv_pos m
  unfold innerF
  set κ : ℝ := (k m : ℝ) with hκ
  have hκ0 : 0 < κ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · refine (abs_T0_le hm).trans ?_
    have : 7 / κ ≤ 5 * κ ^ 3 := by
      rw [div_le_iff₀ hκ0]; nlinarith [pow_pos hκ0 3, pow_pos hκ0 2]
    nlinarith [mul_le_mul_of_nonneg_right this hQ.le]
  · refine (abs_T1_le hm).trans ?_
    rw [← hκ]
    have : 14 * κ ≤ 5 * κ ^ 3 := by nlinarith [pow_pos hκ0 2]
    nlinarith [mul_le_mul_of_nonneg_right this hQ.le]
  · refine (abs_T2_le hm).trans ?_
    nlinarith [mul_pos (pow_pos hκ0 3) hQ]

/-- The quadratic `q_m(r) = T_{0m} + T_{1m}(r - p) + T_{2m}(r - p)²` has all jet bounds `10 F` on `seg 1`
(paper §6.2). -/
theorem BJ_q {m : ℕ} (hm : 2 ≤ m) :
    BJ univ (seg 1) (fun r : ℝ => T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2)
      (10 * innerF m) (10 * innerF m) (10 * innerF m) (10 * innerF m) := by
  obtain ⟨t0, t1, t2⟩ := abs_T_le_five hm
  have hF := innerF_nonneg m
  refine ⟨fun r => T1 m + 2 * T2 m * (r - p), fun _ => 2 * T2 m, fun _ => 0,
    ⟨fun x _ => hasDerivAt_Tq m x, fun x _ => ?_, fun x _ => hasDerivAt_const x _⟩, fun r hr => ?_⟩
  · have := (((hasDerivAt_id x).sub_const p).const_mul (2 * T2 m)).const_add (T1 m)
    simpa using this
  · have hd0 : r - p ≤ 0 := by linarith [hr.2]
    have hd1 : -c ≤ r - p := by linarith [hr.1]
    have hc : c = 3 / 50 := rfl
    have hd : |r - p| ≤ 3 / 50 := by rw [abs_le]; constructor <;> linarith
    have hdd : |(r - p) ^ 2| ≤ (3 / 50) ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have b1 : |T1 m * (r - p)| ≤ 5 * innerF m * (3 / 50) := by
      rw [abs_mul]; exact mul_le_mul t1 hd (abs_nonneg _) (by positivity)
    have b2 : |T2 m * (r - p) ^ 2| ≤ 5 * innerF m * (3 / 50) ^ 2 := by
      rw [abs_mul]; exact mul_le_mul t2 hdd (abs_nonneg _) (by positivity)
    have b3 : |2 * T2 m * (r - p)| ≤ 2 * (5 * innerF m) * (3 / 50) := by
      rw [abs_mul, abs_mul]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      exact mul_le_mul (mul_le_mul_of_nonneg_left t2 (by norm_num)) hd (abs_nonneg _) (by positivity)
    refine ⟨?_, ?_, ?_, by simp; positivity⟩
    · calc |T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2|
          ≤ |T0 m| + |T1 m * (r - p)| + |T2 m * (r - p) ^ 2| := abs_add_three _ _ _
        _ ≤ 5 * innerF m + 5 * innerF m * (3 / 50) + 5 * innerF m * (3 / 50) ^ 2 := by
            gcongr
        _ ≤ _ := by nlinarith
    · calc |T1 m + 2 * T2 m * (r - p)| ≤ |T1 m| + |2 * T2 m * (r - p)| := abs_add_le _ _
        _ ≤ 5 * innerF m + 2 * (5 * innerF m) * (3 / 50) := by gcongr
        _ ≤ _ := by nlinarith
    · calc |2 * T2 m| = 2 * |T2 m| := by rw [abs_mul]; norm_num
        _ ≤ _ := by nlinarith

/-- **The inner continuation** (paper §6.2): on `seg 1 = [p - c, p]` all jets of `b_m = bPoly m` up to order
`3` are bounded by `3·10⁶ k³ 2^{-k}`. -/
theorem BJ_bPoly {m : ℕ} (hm : 2 ≤ m) :
    BJ univ (seg 1) (bPoly m) (3000000 * innerF m) (3000000 * innerF m) (3000000 * innerF m)
      (3000000 * innerF m) := by
  have hF := innerF_nonneg m
  have hc : c = 3 / 50 := rfl
  have hS := BJ_squintic_aff (α := 1 / c) (β := (c - p) / c) (by have := c_pos; positivity) univ (seg 1)
    (fun r hr => by
      have e : (1 / c) * r + (c - p) / c = (r - p + c) / c := by ring
      rw [e]
      have := c_pos
      constructor
      · exact div_nonneg (by linarith [hr.1]) this.le
      · rw [div_le_one this]; linarith [hr.2])
  have hS' : BJ univ (seg 1) (fun r : ℝ => Squintic ((1 / c) * r + (c - p) / c)) 1 34 1667 277778 := by
    refine hS.mono le_rfl ?_ ?_ ?_ <;> rw [hc] <;> norm_num
  have hprod := BJ.mul hS' (BJ_q hm) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e : bPoly m = fun r => Squintic ((1 / c) * r + (c - p) / c) *
      (T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2) := by
    funext r; unfold bPoly
    congr 2; ring
  rw [e]
  refine hprod.mono ?_ ?_ ?_ ?_ <;> nlinarith

end Tails

end SandierSerfaty

end
