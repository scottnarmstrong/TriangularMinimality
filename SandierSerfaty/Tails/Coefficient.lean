/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.ShellCount
public import SandierSerfaty.Calibration.Coeff
public import SandierSerfaty.ClosedForm.Eisenstein

/-!
# The uniform bound `|c_m| ≤ 7/(d a^d)` (paper `tail:coefficient-square`, `tail:coefficient-uniform`)

With `c_m = Re G_{6m}(Λ_△)/(6m)` (`Cal.coeff`, through Mathlib's `PeriodPair.G`) and
`G_n(Λ_△) = a^{-n} ∑_{(n,q) ∈ ℤ²} (n ρ + q)^{-n}` (`Cal.triPair_G`, `ClosedForm.hexG_eq_tsum_prod`):

* `norm_hexTerm`: `|(v₁ ρ + v₂)^{-6m}| = (v₁² + v₁ v₂ + v₂²)^{-3m}` (`hexTerm`);
* `tsum_hexTerm_le` (shell count and integral comparison, paper §6.1): for `m ≥ 2`,
  `∑_{(n,q) ≠ 0} (n² + n q + q²)^{-3m} ≤ 6 + 2·3^{-3m} + 24 (4/3)^{3m} 2^{1-6m}`;
* `coefficient_uniform` (`tail:coefficient-uniform`): for `d = 6 m ≥ 12`,
  `|c_m| ≤ (6 + 2·3^{-d/2} + 24 (4/3)^{d/2} 2^{1-d})/(d a^d) ≤ 7/(d a^d)`;
* `abs_coeff_sub_boxSum_le`: the form used by the finite enclosures of paper `comp:coefficient-summand`
  (`tail:coefficient-square` with the factor `1/(k_m a^{k_m})`).
-/

open Finset

public section

namespace SandierSerfaty

namespace Tails

open ClosedForm Calibration

/-- `|n ρ + q|² = n² + n q + q²` (paper §6.1). -/
theorem normSq_hex (v : ℤ × ℤ) : ‖((v.1 : ℂ) * rho + v.2)‖ ^ 2 = ((hexNorm v : ℤ) : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, rho_re, rho_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero, hexNorm]
  push_cast
  nlinarith [sqrt_three_sq]

theorem norm_hexTerm (m : ℕ) (v : ℤ × ℤ) :
    ‖(((v.1 : ℂ) * rho + v.2) ^ (6 * m))⁻¹‖ = hexTerm m v := by
  rw [norm_inv, norm_pow, show 6 * m = 2 * (3 * m) by ring, pow_mul, normSq_hex]
  rfl

/-- The terms inside the square `|n|, |q| ≤ D`. -/
noncomputable def innerTerm (m D : ℕ) (x : ℤ × ℤ) : ℝ := if supIdx x ≤ D then hexTerm m x else 0

theorem hexTerm_eq_add (m D : ℕ) (x : ℤ × ℤ) : hexTerm m x = tailTerm m D x + innerTerm m D x := by
  unfold tailTerm innerTerm
  by_cases h : D < supIdx x
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

theorem tsum_innerTerm (m D : ℕ) : ∑' x, innerTerm m D x = ∑ x ∈ box D, hexTerm m x := by
  rw [tsum_eq_sum (s := box D)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_box] at hx
    simp [innerTerm, hx]
  · intro x hx
    rw [mem_box] at hx
    simp [innerTerm, hx]

theorem summable_innerTerm (m D : ℕ) : Summable (innerTerm m D) := by
  refine summable_of_ne_finset_zero (s := box D) fun x hx => ?_
  rw [mem_box] at hx
  simp [innerTerm, hx]

theorem summable_hexTerm {m : ℕ} (hm : 1 ≤ m) : Summable (hexTerm m) := by
  have h := (coefficient_square (D := 1) hm le_rfl).1.add (summable_innerTerm m 1)
  exact h.congr fun x => (hexTerm_eq_add m 1 x).symm

theorem tsum_hexTerm_eq {m : ℕ} (hm : 1 ≤ m) (D : ℕ) (hD : 1 ≤ D) :
    ∑' x, hexTerm m x = ∑ x ∈ box D, hexTerm m x + ∑' x, tailTerm m D x := by
  have h := (coefficient_square (D := D) hm hD).1
  have : ∑' x, hexTerm m x = ∑' x, tailTerm m D x + ∑' x, innerTerm m D x := by
    rw [← h.tsum_add (summable_innerTerm m D)]
    exact tsum_congr (hexTerm_eq_add m D)
  rw [this, tsum_innerTerm]; ring

/-- The first shell: six points of norm `1` and two of norm `3` (paper §6.1). -/
theorem sum_box_one {m : ℕ} (hm : 1 ≤ m) :
    ∑ x ∈ box 1, hexTerm m x = 6 + 2 * (((3 : ℝ) ^ (3 * m))⁻¹) := by
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  have h0 : ((0 : ℝ) ^ (3 * m))⁻¹ = 0 := by simp [show 3 * m ≠ 0 by omega]
  simp only [box, hI, Finset.sum_product]
  simp [hexTerm, hexNorm, h0]
  norm_num
  ring

theorem box_two_sdiff_box_one : box 2 \ box 1 = shell 2 := rfl

theorem sum_box_two {m : ℕ} (hm : 1 ≤ m) :
    ∑ x ∈ box 2, hexTerm m x = 6 + 2 * (((3 : ℝ) ^ (3 * m))⁻¹) + ∑ x ∈ shell 2, hexTerm m x := by
  rw [← Finset.sum_sdiff (box_mono (by norm_num : 1 ≤ 2)) (f := hexTerm m), sum_box_one hm,
    box_two_sdiff_box_one]
  ring

/-- `(4/3)^{3m} (2^{6m-1})⁻¹ = 2 · 3^{-3m}`. -/
theorem shellK_mul_two_pow {m : ℕ} (hm : 1 ≤ m) :
    shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ = 2 * (((3 : ℝ) ^ (3 * m))⁻¹) := by
  have e : (2 : ℝ) ^ (6 * m) = (2 : ℝ) ^ (6 * m - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have e4 : (2 : ℝ) ^ (6 * m) = (4 : ℝ) ^ (3 * m) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; ring
  have h2 : (2 : ℝ) ^ (6 * m - 1) = (4 : ℝ) ^ (3 * m) / 2 := by
    rw [← e4, e]; ring
  have h4 : (4 : ℝ) ^ (3 * m) ≠ 0 := by positivity
  have h3 : (3 : ℝ) ^ (3 * m) ≠ 0 := by positivity
  rw [h2, shellK, div_pow]
  field_simp

/-- The shell count and the integral comparison of paper §6.1:
`∑_{(n,q) ≠ 0} (n² + n q + q²)^{-3m} ≤ 6 + 2·3^{-3m} + 24 (4/3)^{3m} 2^{1-6m}` for `m ≥ 2`. -/
theorem tsum_hexTerm_le {m : ℕ} (hm : 2 ≤ m) :
    ∑' x, hexTerm m x ≤
      6 + 2 * (((3 : ℝ) ^ (3 * m))⁻¹) + 24 * shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := by
  have hm1 : 1 ≤ m := by omega
  rw [tsum_hexTerm_eq hm1 2 (by norm_num), sum_box_two hm1]
  have h2 := sum_shell_le (m := m) (V := 2) hm1 (by norm_num)
  have h3 := (coefficient_square (D := 2) hm1 (by norm_num)).2
  have hK : 0 ≤ shellK m := by unfold shellK; positivity
  have e1 : (((2 : ℕ) : ℝ) ^ (6 * m - 1))⁻¹ = (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := by norm_num
  have e2 : (((2 : ℕ) : ℝ) ^ (6 * m - 2))⁻¹ = 2 * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := by
    have : (2 : ℝ) ^ (6 * m - 1) = (2 : ℝ) ^ (6 * m - 2) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]; push_cast; field_simp
  rw [e2] at h3
  rw [e1] at h2
  have hd : (2 : ℝ) ≤ ((6 * m - 2 : ℕ) : ℝ) := by
    have : 2 ≤ 6 * m - 2 := by omega
    exact_mod_cast this
  have hP : 0 ≤ (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := by positivity
  have h4 : 8 * shellK m * (2 * (((2 : ℝ) ^ (6 * m - 1)))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) ≤
      8 * shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ 8 * shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := by positivity
    nlinarith
  have hKP : 0 ≤ shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ := mul_nonneg hK hP
  linarith

/-- `‖G_{6m}(Λ_△)‖ ≤ a^{-6m} ∑ (n² + n q + q²)^{-3m}`. -/
theorem norm_triPair_G_le {m : ℕ} (hm : 1 ≤ m) :
    ‖triPair.G (6 * m)‖ ≤ (a ^ (6 * m))⁻¹ * ∑' x, hexTerm m x := by
  rw [triPair_G, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg a_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ (by have := a_pos; positivity)
  rw [hexG_eq_tsum_prod]
  have hs : Summable fun v : ℤ × ℤ => ‖(((v.1 : ℂ) * rho + v.2) ^ (6 * m))⁻¹‖ := by
    simpa only [norm_hexTerm] using summable_hexTerm hm
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  exact tsum_congr (norm_hexTerm m)

/-- `|c_m| ≤ a^{-d} d⁻¹ ∑ (n² + n q + q²)^{-d/2}` for `d = 6 m`. -/
theorem abs_coeff_le_tsum {m : ℕ} (hm : 1 ≤ m) :
    |coeff m| ≤ (1 / ((6 * m : ℕ) * a ^ (6 * m))) * ∑' x, hexTerm m x := by
  have hpos : (0 : ℝ) < ((6 * m : ℕ) : ℝ) := by positivity
  have h1 : |(triPair.G (6 * m)).re| ≤ ‖triPair.G (6 * m)‖ := Complex.abs_re_le_norm _
  unfold coeff
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine h1.trans ((norm_triPair_G_le hm).trans (le_of_eq ?_))
  have := a_pos
  field_simp

/-- **`tail:coefficient-uniform`**. For `d = k_m = 6 m ≥ 12`,
`|c_m| ≤ (6 + 2·3^{-d/2} + 24 (4/3)^{d/2} 2^{1-d})/(d a^d)`. -/
theorem coefficient_bracket {m : ℕ} (hm : 2 ≤ m) :
    |coeff m| ≤ (1 / ((6 * m : ℕ) * a ^ (6 * m))) *
      (6 + 2 * (((3 : ℝ) ^ (3 * m))⁻¹) + 24 * shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹) := by
  refine (abs_coeff_le_tsum (by omega)).trans ?_
  have := a_pos
  have hp : (0 : ℝ) ≤ 1 / ((6 * m : ℕ) * a ^ (6 * m)) := by positivity
  exact mul_le_mul_of_nonneg_left (tsum_hexTerm_le hm) hp

/-- The bracket is at most `7`: it equals `6 + 50·3^{-3m} ≤ 6 + 50/729` for `m ≥ 2` (paper §6.1). -/
theorem bracket_le_seven {m : ℕ} (hm : 2 ≤ m) :
    6 + 2 * (((3 : ℝ) ^ (3 * m))⁻¹) + 24 * shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ ≤ 7 := by
  have e : 24 * shellK m * (((2 : ℝ) ^ (6 * m - 1)))⁻¹ = 24 * (2 * (((3 : ℝ) ^ (3 * m))⁻¹)) := by
    rw [mul_assoc, shellK_mul_two_pow (by omega)]
  rw [e]
  have h3 : (((3 : ℝ) ^ (3 * m))⁻¹) ≤ ((3 : ℝ) ^ 6)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h3 ⊢
  linarith

/-- **`tail:coefficient-uniform`**: `|c_m| ≤ 7/(d a^d)` for `d = 6 m ≥ 12`. -/
theorem coefficient_uniform {m : ℕ} (hm : 2 ≤ m) :
    |coeff m| ≤ 7 / ((6 * m : ℕ) * a ^ (6 * m)) := by
  refine (coefficient_bracket hm).trans ?_
  have := a_pos
  have hp : (0 : ℝ) ≤ 1 / ((6 * m : ℕ) * a ^ (6 * m)) := by positivity
  calc _ ≤ (1 / ((6 * m : ℕ) * a ^ (6 * m))) * 7 :=
        mul_le_mul_of_nonneg_left (bracket_le_seven hm) hp
    _ = _ := by ring

/-! ### The finite coefficient enclosures (paper `comp:coefficient-summand`) -/

/-- The truncated lattice sum over the square `|n|, |q| ≤ D` (real part of `(n ρ + q)^{-6m}`). -/
noncomputable def boxSum (m D : ℕ) : ℝ :=
  ∑ x ∈ box D, ((((x.1 : ℂ) * rho + x.2) ^ (6 * m))⁻¹).re

/-- The remainder of `c_m` after the square `|n|, |q| ≤ D` is at most
`(1/(d a^d)) · 8 (4/3)^{d/2} D^{2-d}/(d-2)`: the use of `tail:coefficient-square` in the finite coefficient
enclosures of paper `comp:coefficient-summand`, `c_m = a^{-d} d⁻¹ Re ∑_{(n,q)} (n ρ + q)^{-d}`. -/
theorem abs_coeff_sub_boxSum_le {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    |coeff m - (a ^ (6 * m))⁻¹ * boxSum m D / ((6 * m : ℕ) : ℝ)| ≤
      (1 / ((6 * m : ℕ) * a ^ (6 * m))) *
        (8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ)) := by
  set f : ℤ × ℤ → ℂ := fun v => (((v.1 : ℂ) * rho + v.2) ^ (6 * m))⁻¹ with hf
  have hnorm : ∀ v, ‖f v‖ = hexTerm m v := norm_hexTerm m
  have hsumm : Summable f := Summable.of_norm (by simpa only [hnorm] using summable_hexTerm hm)
  set g : ℤ × ℤ → ℂ := fun v => if D < supIdx v then f v else 0 with hg
  set h : ℤ × ℤ → ℂ := fun v => if supIdx v ≤ D then f v else 0 with hh
  have hfgh : ∀ v, f v = g v + h v := fun v => by
    by_cases hv : D < supIdx v
    · simp [hg, hh, hv, not_le.2 hv]
    · simp [hg, hh, hv, not_lt.1 hv]
  have hnormg : ∀ v, ‖g v‖ = tailTerm m D v := fun v => by
    by_cases hv : D < supIdx v
    · simp [hg, tailTerm, hv, hnorm]
    · simp [hg, tailTerm, hv]
  have hsg : Summable g := Summable.of_norm
    (by simpa only [hnormg] using (coefficient_square (D := D) hm hD).1)
  have hsh : Summable h := summable_of_ne_finset_zero (s := box D) fun x hx => by
    rw [mem_box] at hx; simp [hh, hx]
  have hth : ∑' v, h v = ∑ x ∈ box D, f x := by
    rw [tsum_eq_sum (s := box D)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_box] at hx; simp [hh, hx]
    · intro x hx; rw [mem_box] at hx; simp [hh, hx]
  have hG : ClosedForm.hexPair.G (6 * m) = ∑ x ∈ box D, f x + ∑' v, g v := by
    rw [hexG_eq_tsum_prod]
    have : ∑' v, f v = ∑' v, g v + ∑' v, h v := by
      rw [← hsg.tsum_add hsh]; exact tsum_congr hfgh
    rw [this, hth]; ring
  have hre : (triPair.G (6 * m)).re = (a ^ (6 * m))⁻¹ * (boxSum m D + (∑' v, g v).re) := by
    rw [triPair_G, hG]
    have : ((a : ℂ) ^ (6 * m))⁻¹ = (((a ^ (6 * m))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul, Complex.add_re, Complex.re_sum]
    rfl
  have hT : ‖∑' v, g v‖ ≤ 8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) := by
    refine (norm_tsum_le_tsum_norm (by simpa only [hnormg] using (coefficient_square (D := D) hm hD).1)).trans ?_
    simp only [hnormg]
    exact (coefficient_square hm hD).2
  have hpos : (0 : ℝ) < ((6 * m : ℕ) : ℝ) := by positivity
  have := a_pos
  have hpa : (0 : ℝ) < (a ^ (6 * m))⁻¹ := by positivity
  have e : coeff m - (a ^ (6 * m))⁻¹ * boxSum m D / ((6 * m : ℕ) : ℝ) =
      (a ^ (6 * m))⁻¹ * (∑' v, g v).re / ((6 * m : ℕ) : ℝ) := by
    unfold coeff
    rw [hre]; ring
  rw [e, abs_div, abs_of_pos hpos, abs_mul, abs_of_pos hpa, div_le_iff₀ hpos]
  have h1 : |(∑' v, g v).re| ≤ ‖∑' v, g v‖ := Complex.abs_re_le_norm _
  calc (a ^ (6 * m))⁻¹ * |(∑' v, g v).re|
      ≤ (a ^ (6 * m))⁻¹ * (8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans hT) hpa.le
    _ = _ := by field_simp

end Tails

end SandierSerfaty

end
