/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Weights
public import SandierSerfaty.Tails.CutoffBounds

/-!
# The baseline `U_m`: `|U_m^{(j)}| ≤ 30 k² (13/20)^k` on `(0, l]` (paper §6.2)

The baseline piece `Piece.w m j` of `u_m = (1 - τ) U_m + τ b_m` is `(-1)^m c_m r^k` times the cutoff
`1 - S((r - R₀)/(1/10))` on the segments `3, 4, 5` (`U_m`, paper §6.2); `BJ_w` bounds all derivatives of
order `≤ 3` on every segment `seg j`, `j ≤ 5` (so on `(0, l]`) by `30 k² (13/20)^k`.

The paper's chain: Leibniz (`BJ.mul`) with the cutoff `1 - S(10 (r - R₀))` (`|·^{(i)}| ≤ 1, 20, 600, 60000`),
`|c_m| ≤ 7/(k a^k)` (`tail:coefficient-uniform`), `l/a < 13/20`, and (the paper uses `l > .69`) `1/l ≤ 3/2`.
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem seg_pos_le {j : ℕ} (hj : j ≤ 5) {r : ℝ} (hr : r ∈ seg j) : 0 < r ∧ r ≤ l := by
  refine ⟨seg_subset_Ioi hr, ?_⟩
  have h1 := p_lt_R₀
  have h2 := c_pos
  have h3 := R₀_add_hs_lt_l
  have h4 := R₀_lt_l
  have h5 := l_eq
  have h6 := hs_pos
  interval_cases j <;> simp only [seg, mem_Icc, mem_Ioc] at hr <;> linarith [hr.2]

theorem l_pos : 0 < l := by linarith [R₀_pos, R₀_lt_l]

theorem two_thirds_le_l : 2 / 3 ≤ l := by linarith [l_gt]

/-- The arithmetic of the Leibniz step for `U` (paper §6.2), for the bounds of the product with the cutoff. -/
theorem U_prod_arith {A₀ A₁ A₂ A₃ E κ : ℝ} (hE : 0 ≤ E) (hκ : 234 ≤ κ)
    (h0 : A₀ ≤ 7 / 234 * E) (h1 : A₁ ≤ 21 / 2 * E) (h2 : A₂ ≤ 63 / 4 * κ * E)
    (h3 : A₃ ≤ 189 / 8 * κ ^ 2 * E) (n2 : 0 ≤ A₂) (n3 : 0 ≤ A₃) :
    A₀ * 1 ≤ 30 * κ ^ 2 * E ∧ A₁ * 1 + A₀ * 20 ≤ 30 * κ ^ 2 * E ∧
    (A₂ * 1 + A₁ * 20) + (A₁ * 20 + A₀ * 600) ≤ 30 * κ ^ 2 * E ∧
    ((A₃ * 1 + A₂ * 20) + (A₂ * 20 + A₁ * 600)) + ((A₂ * 20 + A₁ * 600) + (A₁ * 600 + A₀ * 60000)) ≤
      30 * κ ^ 2 * E := by
  have ha : 234 * (κ * E) ≤ κ ^ 2 * E := by nlinarith [mul_nonneg hE (sub_nonneg.2 hκ)]
  have hb : 54756 * E ≤ κ ^ 2 * E := by nlinarith [mul_nonneg hE (sub_nonneg.2 hκ)]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **`BJ_w`**: the baseline `w` of `u_m` has all jet bounds `30 k² (13/20)^k` on each segment `seg j`,
`j ≤ 5` (paper §6.2). -/
theorem BJ_w {m : ℕ} (hm : 39 ≤ m) {j : ℕ} (hj : j ≤ 5) :
    BJ univ (seg j) (Piece.w m j) (30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m))
      (30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m))
      (30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m))
      (30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m)) := by
  have hm0 : m ≠ 0 := by omega
  have hm2 : 2 ≤ m := by omega
  have hk234 : 234 ≤ k m := by rw [k_of_pos (by omega)]; omega
  obtain ⟨e, he⟩ : ∃ e, k m = e + 3 := ⟨k m - 3, by omega⟩
  have hmem : ∀ x ∈ seg j, |x| ≤ l := fun x hx => by
    obtain ⟨a1, a2⟩ := seg_pos_le hj hx
    rw [abs_of_pos a1]; exact a2
  have hid : BJ univ (seg j) (fun r : ℝ => r) l 1 0 0 := BJ.id univ (seg j) hmem
  have hpow := BJ.pow3 (𝔸 := ℝ) e hid l_pos.le (by norm_num : (0 : ℝ) ≤ 1)
  have hf := hpow.const_mul ((-1 : ℝ) ^ m * coeff m)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs] at hf
  -- arithmetic
  have hY0 := abs_coeff_mul_pow_le hm2 (x := l) l_pos.le
  rw [he]
  rw [he] at hY0
  have hG0 : (l / a) ^ (e + 3) ≤ (13 / 20 : ℝ) ^ (e + 3) :=
    pow_le_pow_left₀ (div_nonneg l_pos.le a_pos.le) l_div_a_lt.le _
  set κ : ℝ := ((e + 3 : ℕ) : ℝ) with hκdef
  set E : ℝ := (13 / 20 : ℝ) ^ (e + 3) with hEdef
  set L : ℝ := l ^ (e + 3) with hLdef
  have hκ : (234 : ℝ) ≤ κ := by
    rw [hκdef]; rw [he] at hk234; exact_mod_cast hk234
  have hκ0 : 0 < κ := by linarith
  have hE0 : 0 ≤ E := by positivity
  have hcLκ : |coeff m| * L * κ ≤ 7 * E := by
    have h1 : |coeff m| * L * κ ≤ 7 / κ * (l / a) ^ (e + 3) * κ := by gcongr
    have h2 : 7 / κ * (l / a) ^ (e + 3) * κ = 7 * (l / a) ^ (e + 3) := by field_simp
    rw [h2] at h1
    linarith
  have hl0 : 0 < l := l_pos
  have hL0 : 0 ≤ L := by positivity
  have hl23 := two_thirds_le_l
  have hP1 : l ^ (e + 2) ≤ 3 / 2 * L := by
    have : L = l ^ (e + 2) * l := pow_succ l (e + 2)
    have h0 : 0 ≤ l ^ (e + 2) := by positivity
    nlinarith
  have hP2 : l ^ (e + 1) ≤ 9 / 4 * L := by
    have : L = l ^ (e + 1) * l ^ 2 := by rw [hLdef, ← pow_add]
    have h0 : 0 ≤ l ^ (e + 1) := by positivity
    have h2 : (4 / 9 : ℝ) ≤ l ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  have hP3 : l ^ e ≤ 27 / 8 * L := by
    have : L = l ^ e * l ^ 3 := by rw [hLdef, ← pow_add]
    have h0 : 0 ≤ l ^ e := by positivity
    have h3 : (8 / 27 : ℝ) ≤ l ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hl23 3
      norm_num at this ⊢; linarith
    nlinarith [mul_le_mul_of_nonneg_left h3 h0]
  have hu : ((e + 2 : ℕ) : ℝ) ≤ κ := by rw [hκdef]; exact_mod_cast (by omega : e + 2 ≤ e + 3)
  have hv : ((e + 1 : ℕ) : ℝ) ≤ κ := by rw [hκdef]; exact_mod_cast (by omega : e + 1 ≤ e + 3)
  have hu0 : (0 : ℝ) ≤ ((e + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc0 := abs_nonneg (coeff m)
  -- clean bounds for the monomial part
  have hn : ‖(-1 : ℝ) ^ m * coeff m‖ = |coeff m| := by simp [norm_mul]
  have hf' : BJ univ (seg j) (fun x => (-1 : ℝ) ^ m * coeff m * x ^ (e + 3)) (7 / 234 * E) (21 / 2 * E)
      (63 / 4 * κ * E) (189 / 8 * κ ^ 2 * E) := by
    refine hpow.const_mul ((-1 : ℝ) ^ m * coeff m) |>.mono ?_ ?_ ?_ ?_ <;> rw [hn]
    · have h1 : 234 * (|coeff m| * L) ≤ κ * (|coeff m| * L) := by
        have := mul_nonneg hc0 hL0; nlinarith
      nlinarith
    · calc |coeff m| * (κ * l ^ (e + 2) * 1) ≤ |coeff m| * (κ * (3 / 2 * L) * 1) := by gcongr
        _ = 3 / 2 * (|coeff m| * L * κ) := by ring
        _ ≤ 3 / 2 * (7 * E) := by gcongr
        _ = _ := by ring
    · calc |coeff m| * (κ * (((e + 2 : ℕ) : ℝ) * l ^ (e + 1) * 1 * 1 + l ^ (e + 2) * 0))
          ≤ |coeff m| * (κ * (κ * (9 / 4 * L) * 1 * 1 + l ^ (e + 2) * 0)) := by gcongr
        _ = 9 / 4 * κ * (|coeff m| * L * κ) := by ring
        _ ≤ 9 / 4 * κ * (7 * E) := by gcongr
        _ = _ := by ring
    · calc |coeff m| * (κ * (((e + 2 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ) * l ^ e * 1 * 1 * 1 +
            3 * ((e + 2 : ℕ) : ℝ) * l ^ (e + 1) * 1 * 0 + l ^ (e + 2) * 0))
          ≤ |coeff m| * (κ * (κ * κ * (27 / 8 * L) * 1 * 1 * 1 +
            3 * ((e + 2 : ℕ) : ℝ) * l ^ (e + 1) * 1 * 0 + l ^ (e + 2) * 0)) := by gcongr
        _ = 27 / 8 * κ ^ 2 * (|coeff m| * L * κ) := by ring
        _ ≤ 27 / 8 * κ ^ 2 * (7 * E) := by gcongr
        _ = _ := by ring
  have ha : 234 * (κ * E) ≤ κ ^ 2 * E := by nlinarith [mul_nonneg hE0 (sub_nonneg.2 hκ)]
  have hb : 54756 * E ≤ κ ^ 2 * E := by nlinarith [mul_nonneg hE0 (sub_nonneg.2 hκ)]
  by_cases h3 : 3 ≤ j
  · -- the cutoff `1 - S(10 (r - R₀))` is active
    have hg : BJ univ (seg j) (fun r : ℝ => 1 - Squintic (10 * r + (-(10 * R₀)))) 1 20 600 60000 := by
      have h := BJ_one_sub_squintic_aff (α := 10) (β := -(10 * R₀)) (by norm_num) univ (seg j)
        (fun r hr => by
          obtain ⟨a1, a2⟩ := seg_pos_le hj hr
          have hr3 : R₀ ≤ r := by
            interval_cases j <;> simp only [seg, mem_Icc] at hr <;> linarith [hr.1, R₀_add_hs_lt_l, hs_pos]
          have := l_eq
          have := hs_pos
          unfold hs at *
          constructor <;> linarith)
      refine h.mono le_rfl (le_of_eq (by norm_num)) (le_of_eq (by norm_num)) (le_of_eq (by norm_num))
    have hprod := BJ.mul hf' hg (by positivity) (by positivity) (by positivity) (by positivity)
    have hw : Piece.w m j = fun x => (-1 : ℝ) ^ m * coeff m * x ^ (e + 3) *
        (1 - Squintic (10 * x + (-(10 * R₀)))) := by
      funext r
      interval_cases j <;> simp only [Piece.w, hm0, he, ite_false] <;> congr 3 <;> ring
    rw [hw]
    obtain ⟨b0, b1, b2, b3⟩ := U_prod_arith hE0 hκ (le_refl _) (le_refl _) (le_refl _) (le_refl _)
      (by positivity) (by positivity)
    exact hprod.mono b0 b1 b2 b3
  · have hw : Piece.w m j = fun x => (-1 : ℝ) ^ m * coeff m * x ^ (e + 3) := by
      funext r
      interval_cases j <;> simp [Piece.w, hm0, he]
    rw [hw]
    refine hf'.mono ?_ ?_ ?_ ?_ <;> nlinarith

end Tails

end SandierSerfaty

end
