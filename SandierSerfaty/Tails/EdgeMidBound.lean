/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.EdgeMid

/-!
# `|V_m^{(j)}| ≤ 3·10⁶ k² (289/500)^k` on `[p + .01, R₀]` (paper §6.2)

`BJ_V_mid`: for `m ≥ 39` and `j ≤ 3` the `j`-th derivative of `V_m = c_m Re z^k` on `[p + .01, R₀]` is bounded by
`3·10⁶ k² (289/500)^k`. The proof: `BJ.pow3` for `z^k` (`|z| ≤ R₀`, `|z'| ≤ 7`, `|z''| ≤ 300`,
`|z'''| ≤ 60000`), `R₀^{k-j} ≤ 2^j R₀^k` (`R₀ > 1/2`), `|c_m| R₀^k ≤ (7/k)(R₀/a)^k` and `R₀/a < 289/500`;
the paper's displayed constant for the third derivative is `20000`, the weaker `3·10⁶` covers all orders
(paper §6.2).
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The arithmetic of paper §6.2, for all four orders. -/
theorem mid_arith {c T G κ u v R₀' R₁' R₂' : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T) (hG : 0 ≤ G) (hκ : 1 ≤ κ)
    (hu : u ≤ κ) (hv : v ≤ κ) (hv0 : 0 ≤ v) (hR₀ : 0 ≤ R₀') (hR₁ : 0 ≤ R₁')
    (hA : R₀' ≤ 8 * T) (hB : R₁' ≤ 4 * T) (hC : R₂' ≤ 2 * T)
    (hY : c * T * κ ≤ 7 * G) :
    c * T ≤ 3000000 * κ ^ 2 * G ∧
    c * (κ * R₂' * 7) ≤ 3000000 * κ ^ 2 * G ∧
    c * (κ * (u * R₁' * 7 * 7 + R₂' * 300)) ≤ 3000000 * κ ^ 2 * G ∧
    c * (κ * (u * v * R₀' * 7 * 7 * 7 + 3 * u * R₁' * 7 * 300 + R₂' * 60000)) ≤
      3000000 * κ ^ 2 * G := by
  have hcT : 0 ≤ c * T := mul_nonneg hc hT
  have hk0 : 0 ≤ κ := by linarith
  have hk2 : κ ≤ κ ^ 2 := by nlinarith
  have hG1 : G ≤ κ ^ 2 * G := by nlinarith
  have hcTG : c * T ≤ 7 * G := by nlinarith
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · calc c * (κ * R₂' * 7) ≤ c * (κ * (2 * T) * 7) := by gcongr
      _ = 14 * (c * T * κ) := by ring
      _ ≤ 14 * (7 * G) := by gcongr
      _ ≤ _ := by nlinarith
  · have h1 : u * R₁' * 7 * 7 + R₂' * 300 ≤ κ * (4 * T) * 49 + 2 * T * 300 := by
      have : u * R₁' ≤ κ * (4 * T) := by gcongr
      nlinarith
    calc c * (κ * (u * R₁' * 7 * 7 + R₂' * 300)) ≤ c * (κ * (κ * (4 * T) * 49 + 2 * T * 300)) := by gcongr
      _ = (c * T * κ) * (196 * κ + 600) := by ring
      _ ≤ (7 * G) * (196 * κ + 600) := by gcongr
      _ ≤ _ := by nlinarith
  · have h1 : u * v * R₀' ≤ κ * κ * (8 * T) := by gcongr
    have h2 : u * R₁' ≤ κ * (4 * T) := by gcongr
    have h3 : u * v * R₀' * 7 * 7 * 7 + 3 * u * R₁' * 7 * 300 + R₂' * 60000 ≤
        κ * κ * (8 * T) * 343 + 3 * (κ * (4 * T)) * 2100 + 2 * T * 60000 := by nlinarith
    calc c * (κ * (u * v * R₀' * 7 * 7 * 7 + 3 * u * R₁' * 7 * 300 + R₂' * 60000))
        ≤ c * (κ * (κ * κ * (8 * T) * 343 + 3 * (κ * (4 * T)) * 2100 + 2 * T * 60000)) := by gcongr
      _ = (c * T * κ) * (2744 * κ ^ 2 + 25200 * κ + 120000) := by ring
      _ ≤ (7 * G) * (2744 * κ ^ 2 + 25200 * κ + 120000) := by gcongr
      _ ≤ _ := by nlinarith

/-- **Mid-edge bound** (paper §6.2): for `m ≥ 39` and `p + 1/100 ≤ r ≤ R₀`, `0 ≤ j ≤ 3`,
`|V_m^{(j)}(r)| ≤ 3·10⁶ k² (289/500)^k`. -/
theorem BJ_V_mid {m : ℕ} (hm : 39 ≤ m) :
    BJ (Ioi p) (Icc (p + 1 / 100) R₀) (V m) (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)) := by
  have hk : k m = 6 * m := k_of_pos (by omega)
  obtain ⟨e, he⟩ : ∃ e, k m = e + 3 := ⟨k m - 3, by omega⟩
  have hF := BJ.pow3 (𝔸 := ℂ) e BJ_zc R₀_pos.le (by norm_num)
  have hFc := hF.const_mul ((coeff m : ℝ) : ℂ)
  have hRe := hFc.re
  simp only [Complex.norm_real, Real.norm_eq_abs] at hRe
  have hcongr : EqOn (fun r => (((coeff m : ℝ) : ℂ) * zc r ^ (e + 3)).re) (V m) (Ioi p) := by
    intro r hr
    have hr' : p ≤ r := le_of_lt hr
    show (((coeff m : ℝ) : ℂ) * zc r ^ (e + 3)).re = V m r
    rw [V_eq_re m hr', Complex.re_ofReal_mul, ← he]
    rfl
  have hB := BJ.congr isOpen_Ioi (fun r hr => (lt_of_lt_of_le (by linarith [p_pos]) hr.1 : p < r))
    hRe hcongr
  have hm2 : 2 ≤ m := by omega
  have hY0 := abs_coeff_mul_pow_le hm2 (x := R₀) R₀_pos.le
  rw [he] at hY0
  rw [he]
  have hG0 : (R₀ / a) ^ (e + 3) ≤ (289 / 500 : ℝ) ^ (e + 3) :=
    pow_le_pow_left₀ (div_nonneg R₀_pos.le a_pos.le) R₀_div_a_lt.le _
  set κ : ℝ := ((e + 3 : ℕ) : ℝ) with hκdef
  set G : ℝ := (289 / 500 : ℝ) ^ (e + 3) with hGdef
  set T : ℝ := R₀ ^ (e + 3) with hTdef
  have hκ1 : (1 : ℝ) ≤ κ := by rw [hκdef]; exact_mod_cast (by omega : 1 ≤ e + 3)
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hY : |coeff m| * T * κ ≤ 7 * G := by
    have h1 : |coeff m| * T * κ ≤ 7 / κ * (R₀ / a) ^ (e + 3) * κ := by gcongr
    have h2 : 7 / κ * (R₀ / a) ^ (e + 3) * κ = 7 * (R₀ / a) ^ (e + 3) := by field_simp
    rw [h2] at h1
    linarith
  have hR := R₀_gt
  have hRh : (1 / 2 : ℝ) ≤ R₀ := by linarith
  have hT0 : 0 ≤ T := by positivity
  have hP2 : R₀ ^ (e + 2) ≤ 2 * T := by
    have : T = R₀ ^ (e + 2) * R₀ := pow_succ R₀ (e + 2)
    have h0 : 0 ≤ R₀ ^ (e + 2) := by positivity
    nlinarith
  have hP1 : R₀ ^ (e + 1) ≤ 4 * T := by
    have : T = R₀ ^ (e + 1) * R₀ ^ 2 := by rw [hTdef, ← pow_add]
    have h0 : 0 ≤ R₀ ^ (e + 1) := by positivity
    have h2 : (1 / 4 : ℝ) ≤ R₀ ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  have hP0 : R₀ ^ e ≤ 8 * T := by
    have : T = R₀ ^ e * R₀ ^ 3 := by rw [hTdef, ← pow_add]
    have h0 : 0 ≤ R₀ ^ e := by positivity
    have h3 : (1 / 8 : ℝ) ≤ R₀ ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hRh 3
      norm_num at this ⊢; linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 h0]
  have hu : ((e + 2 : ℕ) : ℝ) ≤ κ := by rw [hκdef]; exact_mod_cast (by omega : e + 2 ≤ e + 3)
  have hv : ((e + 1 : ℕ) : ℝ) ≤ κ := by rw [hκdef]; exact_mod_cast (by omega : e + 1 ≤ e + 3)
  obtain ⟨a0, a1, a2, a3⟩ := mid_arith (c := |coeff m|) (T := T) (G := G) (κ := κ)
    (u := ((e + 2 : ℕ) : ℝ)) (v := ((e + 1 : ℕ) : ℝ)) (R₀' := R₀ ^ e) (R₁' := R₀ ^ (e + 1))
    (R₂' := R₀ ^ (e + 2)) (abs_nonneg _) hT0 (by positivity) hκ1 hu hv (Nat.cast_nonneg _)
    (by positivity) (by positivity) hP0 hP1 hP2 hY
  exact hB.mono a0 a1 a2 a3

end Tails

end SandierSerfaty

end
