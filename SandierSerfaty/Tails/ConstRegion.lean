/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.OmittedModes
public import SandierSerfaty.Tails.Weights
public import SandierSerfaty.Calibration.EdgeForm

/-!
# The constant region: `ΔB(l)` (paper `tail:constant-region`)

`B(l) - B̃(l) = ∑_{m ≥ 39} u_m(l)` and `u_m(l) = V_m(R₀)` (the cutoff is `1` and the continuation of the edge
polynomial is constant beyond `R₀ + h_s`), with `|V_m(R₀)| ≤ |c_m| R₀^k ≤ (7/k)(R₀/a)^k`
(`tail:coefficient-uniform`). Summing over `k = 234, 240, …`:
`|ΔB(l)| ≤ (7/234)(289/500)^{234}/(1 - (289/500)^6) < 6.075·10⁻⁵⁸ < 10⁻¹¹` (`abs_dB_l_lt`).
-/

open Set Filter Complex

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem norm_edge_point : ‖((p : ℂ) + ((√(R₀ ^ 2 - p ^ 2) : ℝ) : ℂ) * I)‖ = R₀ := by
  have hp : p ≤ R₀ := p_lt_R₀.le
  have h0 : 0 ≤ R₀ ^ 2 - p ^ 2 := by nlinarith [p_pos]
  have hsq : ‖((p : ℂ) + ((√(R₀ ^ 2 - p ^ 2) : ℝ) : ℂ) * I)‖ ^ 2 = R₀ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_one, Complex.add_im, Complex.mul_im]
    have := Real.mul_self_sqrt h0
    nlinarith
  exact (sq_eq_sq₀ (norm_nonneg _) R₀_pos.le).1 hsq

/-- `|V_m(R₀)| ≤ (7/k)(R₀/a)^k` for `m ≥ 2` (paper §6.6). -/
theorem abs_V_R₀_le {m : ℕ} (hm : 2 ≤ m) : |V m R₀| ≤ (7 / (k m : ℝ)) * (R₀ / a) ^ (k m) := by
  rw [V_eq_re m p_lt_R₀.le, abs_mul]
  have h1 : |(((p : ℂ) + ((√(R₀ ^ 2 - p ^ 2) : ℝ) : ℂ) * I) ^ k m).re| ≤ R₀ ^ k m := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_pow, norm_edge_point]
  calc |coeff m| * |(((p : ℂ) + ((√(R₀ ^ 2 - p ^ 2) : ℝ) : ℂ) * I) ^ k m).re|
      ≤ |coeff m| * R₀ ^ k m := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ _ := abs_coeff_mul_pow_le hm R₀_pos.le

theorem u_l_eq {j : ℕ} : u (j + 39) l = V (j + 39) R₀ := by
  rw [u_of_ge le_rfl, bRad_of_ge (by have := R₀_add_hs_lt_l; linarith)]
  simp

theorem abs_u_l_le (j : ℕ) :
    |u (j + 39) l| ≤ (7 / 234 : ℝ) * (289 / 500 : ℝ) ^ 234 * ((289 / 500 : ℝ) ^ 6) ^ j := by
  rw [u_l_eq]
  refine (abs_V_R₀_le (by omega)).trans ?_
  have hk : k (j + 39) = 234 + 6 * j := by rw [k_tail]; unfold kk; omega
  rw [hk]
  have hr0 : 0 ≤ R₀ / a := by have := a_pos; have := R₀_pos; positivity
  have hr : R₀ / a ≤ 289 / 500 := R₀_div_a_lt.le
  have hkc : (234 : ℝ) ≤ ((234 + 6 * j : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have e1 : 7 / ((234 + 6 * j : ℕ) : ℝ) ≤ 7 / 234 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkc
  have e2 : (R₀ / a) ^ (234 + 6 * j) ≤ (289 / 500 : ℝ) ^ (234 + 6 * j) := pow_le_pow_left₀ hr0 hr _
  have e3 : (289 / 500 : ℝ) ^ (234 + 6 * j) = (289 / 500 : ℝ) ^ 234 * ((289 / 500 : ℝ) ^ 6) ^ j := by
    rw [pow_add, pow_mul]
  calc 7 / ((234 + 6 * j : ℕ) : ℝ) * (R₀ / a) ^ (234 + 6 * j)
      ≤ 7 / 234 * (289 / 500 : ℝ) ^ (234 + 6 * j) :=
        mul_le_mul e1 e2 (by positivity) (by norm_num)
    _ = _ := by rw [e3]; ring

/-- **`ΔB(l)`** (paper `tail:constant-region`): `B(l) - B̃(l) = ∑_{m ≥ 39} u_m(l)` is bounded by the geometric series. -/
theorem abs_dB_l_le :
    |B l - Trunc.B l| ≤ (7 / 234 : ℝ) * (289 / 500 : ℝ) ^ 234 / (1 - (289 / 500 : ℝ) ^ 6) := by
  have hl : 0 < l := by have := l_gt; linarith
  rw [B_eq_trunc_add hl, add_sub_cancel_left]
  unfold dU0
  have hq : (289 / 500 : ℝ) ^ 6 < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by norm_num)
  have hg : Summable fun j : ℕ => (7 / 234 : ℝ) * (289 / 500 : ℝ) ^ 234 * ((289 / 500 : ℝ) ^ 6) ^ j :=
    (summable_geometric_of_lt_one (by positivity) hq).mul_left _
  have hs : Summable fun j : ℕ => |u (j + 39) l| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_u_l_le hg
  calc |∑' j, u (j + 39) l| ≤ ∑' j, |u (j + 39) l| := by
        simpa using norm_tsum_le_tsum_norm (f := fun j => u (j + 39) l) (by simpa using hs)
    _ ≤ ∑' j : ℕ, (7 / 234 : ℝ) * (289 / 500 : ℝ) ^ 234 * ((289 / 500 : ℝ) ^ 6) ^ j :=
        Summable.tsum_le_tsum abs_u_l_le hs hg
    _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq]
        field_simp

/-- **`ΔB(l)` numerics** (paper §6.6): `(7/234)(289/500)^{234}/(1 - (289/500)^6) < 6.075·10⁻⁵⁸`. -/
theorem dB_l_const_lt :
    (7 / 234 : ℝ) * (289 / 500 : ℝ) ^ 234 / (1 - (289 / 500 : ℝ) ^ 6) < 6075 / 10 ^ 61 := by
  norm_num

/-- **`ΔB(l)`** (`tail:constant-region`): `|B(l) - B̃(l)| < 6.075·10⁻⁵⁸ < 10⁻¹¹`. -/
theorem abs_dB_l_lt : |B l - Trunc.B l| < 6075 / 10 ^ 61 :=
  abs_dB_l_le.trans_lt dB_l_const_lt

theorem abs_dB_l_lt_eps : |B l - Trunc.B l| < 1 / 10 ^ 11 :=
  abs_dB_l_lt.trans (by norm_num)

end Tails

end SandierSerfaty

end
