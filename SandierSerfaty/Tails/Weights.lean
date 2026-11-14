/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Coefficient

/-!
# The majorant `w_k` and the numerical side facts of paper `tail:radial-derivatives`, `tail:w-definition`, `tail:mode-derivative-bound`

* `wk k` (`tail:w-definition`): for `k = 6m ≥ 234`,
  `w_k = 10⁶ (30 k² (13/20)^k + 3·10⁶ k³ 2^{-k} + 5600 k⁵ (3/5)^k + 7·10¹¹ k² (289/500)^k)`;
* the rational bounds `a > 1.07`, `l/a < 13/20`, `R₀/a < 289/500`, `p/a = 1/2` (paper §6.2; the paper's decimals are
  rationals), all from `a⁴ = 4/3`, `R₀ = a/√3`;
* `abs_coeff_mul_pow_le`: `|c_m| x^{k} ≤ (7/k) (x/a)^{k}` for `m ≥ 2` and `x ≥ 0` (from `tail:coefficient-uniform`).
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- **`tail:w-definition`**: the rational majorant `w_k` of the omitted-mode derivatives. -/
@[expose] noncomputable def wk (k : ℕ) : ℝ :=
  10 ^ 6 * (30 * (k : ℝ) ^ 2 * (13 / 20 : ℝ) ^ k + 3 * 10 ^ 6 * (k : ℝ) ^ 3 * ((2 : ℝ) ^ k)⁻¹ +
    5600 * (k : ℝ) ^ 5 * (3 / 5 : ℝ) ^ k + 7 * 10 ^ 11 * (k : ℝ) ^ 2 * (289 / 500 : ℝ) ^ k)

theorem a_gt : 107 / 100 < a := lt_of_pow_four a_pos.le a_pow_four (by norm_num)

theorem p_div_a : p / a = 1 / 2 := by
  have := a_pos
  unfold p; field_simp

/-- `R₀ = a/√3` (`R₀ = 2p/√3`, `p = a/2`). -/
theorem R₀_eq : R₀ = a / √3 := by
  have := sqrt_three_pos
  unfold R₀ p; ring

theorem R₀_lt_mul_a : R₀ < (289 / 500) * a := by
  have h3 := sqrt_three_pos
  have hs : (500 / 289 : ℝ) < √3 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have ha := a_pos
  rw [R₀_eq, div_lt_iff₀ h3]
  nlinarith

theorem l_lt_mul_a : l < (13 / 20) * a := by
  have h1 := R₀_lt_mul_a
  have h2 := a_gt
  unfold l
  linarith

theorem R₀_div_a_lt : R₀ / a < 289 / 500 := by
  rw [div_lt_iff₀ a_pos]; linarith [R₀_lt_mul_a]

theorem l_div_a_lt : l / a < 13 / 20 := by
  rw [div_lt_iff₀ a_pos]; linarith [l_lt_mul_a]

/-- `|c_m| x^k ≤ (7/k)(x/a)^k` for `m ≥ 2`, `x ≥ 0` (paper `tail:coefficient-uniform`). -/
theorem abs_coeff_mul_pow_le {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    |coeff m| * x ^ (k m) ≤ (7 / (k m : ℝ)) * (x / a) ^ (k m) := by
  have hk : k m = 6 * m := k_of_pos (by omega)
  have h := coefficient_uniform hm
  have ha := a_pos
  have hxk : 0 ≤ x ^ (k m) := pow_nonneg hx _
  have hkpos : (0 : ℝ) < (6 * m : ℕ) := by positivity
  calc |coeff m| * x ^ (k m) ≤ (7 / ((6 * m : ℕ) * a ^ (6 * m))) * x ^ (k m) :=
        mul_le_mul_of_nonneg_right h hxk
    _ = (7 / (k m : ℝ)) * (x / a) ^ (k m) := by
        rw [hk, div_pow]
        field_simp

end Tails

end SandierSerfaty

end
