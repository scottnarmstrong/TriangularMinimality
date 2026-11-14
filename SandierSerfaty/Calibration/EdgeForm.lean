/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.EdgePoly
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The binomial form of the edge polynomial `V_m`

paper `cal:edge-polynomial`. For `m ≥ 0` (any `m`) and `y : ℝ`,
`Vsum m (y²) = Re (p + i y)^{k_m}` (`Vsum_sq_eq_re`; `k_m` is even), hence
* `V_eq_re`: `V_m(r) = c_m Re (p + i √(r² - p²))^{k_m}` for `r ≥ p`;
* `V_edge_cos`: at an edge point of radius `t = p / cos φ`, `V_m(t) = c_m t^{k_m} cos(k_m φ)`
  (the boundary value of the `m`-th Green-function mode, paper §5.2);
* `V_vertex_ray`: on a vertex ray `φ = π/6` the same mode equals `(-1)^m c_m r^{k_m}` (paper §5.2),
  i.e. `cos(k_m π/6) = (-1)^m` for `k_m = 6m`.
-/

open Complex Finset

public section

namespace SandierSerfaty

namespace Calibration

/-- Summing over the even indices of `range (2N + 1)` is summing `g (2 j)` over `range (N + 1)`. -/
theorem sum_range_even (g : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ range (2 * N + 1), (if Even m then g m else 0) = ∑ j ∈ range (N + 1), g (2 * j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j => g (2 * j)) (N + 1)]
    have h1 : ¬ Even (2 * N + 1) := Nat.not_even_two_mul_add_one N
    have h2 : Even (2 * N + 1 + 1) := by
      rw [show 2 * N + 1 + 1 = 2 * (N + 1) by ring]; exact even_two_mul _
    simp only [h1, h2, ↓reduceIte]
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    ring

/-- The real part of `(y i)^n`. -/
theorem re_I_mul_pow (y : ℝ) (n : ℕ) :
    (((y : ℂ) * I) ^ n).re = if Even n then (-1 : ℝ) ^ (n / 2) * y ^ n else 0 := by
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · have : ((y : ℂ) * I) ^ (2 * j) = (((-y ^ 2) ^ j : ℝ) : ℂ) := by
      rw [pow_mul]; push_cast
      congr 1
      rw [mul_pow, I_sq]; ring
    rw [this, Complex.ofReal_re]
    have he : Even (2 * j) := even_two_mul j
    simp only [he, ↓reduceIte]
    rw [show 2 * j / 2 = j by omega, pow_mul, neg_pow]
  · have : ((y : ℂ) * I) ^ (2 * j + 1) = (((-y ^ 2) ^ j * y : ℝ) : ℂ) * I := by
      rw [pow_succ, pow_mul]; push_cast
      have : ((y : ℂ) * I) ^ 2 = -(y : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
      rw [this]; ring
    have ho : ¬ Even (2 * j + 1) := Nat.not_even_two_mul_add_one j
    rw [this, Complex.re_ofReal_mul, Complex.I_re, mul_zero]
    simp only [ho, ↓reduceIte]

/-- `Re (p + i y)^{k_m} = Vsum m (y²)`: the binomial form of the edge polynomial. -/
theorem Vsum_sq_eq_re (m : ℕ) (y : ℝ) :
    Vsum m (y ^ 2) = (((p : ℂ) + (y : ℂ) * I) ^ k m).re := by
  obtain ⟨N, hN⟩ := (k_even m)
  have hk : k m = 2 * N := by omega
  have hk2 : k m / 2 = N := by omega
  rw [hk, add_comm, add_pow]
  have e : ∀ n : ℕ, (((y : ℂ) * I) ^ n * (p : ℂ) ^ (2 * N - n) * (Nat.choose (2 * N) n : ℂ)).re =
      if Even n then (-1 : ℝ) ^ (n / 2) * y ^ n * p ^ (2 * N - n) * (Nat.choose (2 * N) n : ℝ)
      else 0 := by
    intro n
    have : (((y : ℂ) * I) ^ n * (p : ℂ) ^ (2 * N - n) * (Nat.choose (2 * N) n : ℂ)) =
        (((p : ℝ) ^ (2 * N - n) * (Nat.choose (2 * N) n : ℝ) : ℝ) : ℂ) * (((y : ℂ) * I) ^ n) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, re_I_mul_pow]
    by_cases hn : Even n
    · simp only [hn, ↓reduceIte]; ring
    · simp only [hn, ↓reduceIte]; ring
  rw [Complex.re_sum]
  simp only [e]
  rw [sum_range_even (fun n => (-1 : ℝ) ^ (n / 2) * y ^ n * p ^ (2 * N - n) *
    (Nat.choose (2 * N) n : ℝ)) N]
  unfold Vsum
  rw [hk2, hk]
  refine sum_congr rfl fun j _ => ?_
  rw [show 2 * j / 2 = j by omega, pow_mul]
  ring

/-- `V_m(r) = c_m Re (p + i √(r² - p²))^{k_m}` for `r ≥ p` (paper `cal:edge-polynomial` versus paper §5.2). -/
theorem V_eq_re (m : ℕ) {r : ℝ} (hr : p ≤ r) :
    V m r = coeff m * (((p : ℂ) + (√(r ^ 2 - p ^ 2) : ℝ) * I) ^ k m).re := by
  have : 0 ≤ r ^ 2 - p ^ 2 := by nlinarith [p_pos]
  rw [← Vsum_sq_eq_re, Real.sq_sqrt this]
  rfl

/-- At an edge point of radius `t = p / cos φ` the `m`-th mode's boundary value is
`V_m(t) = c_m t^{k_m} cos(k_m φ)` (paper §5.2). -/
theorem V_edge_cos (m : ℕ) {φ : ℝ} (hφ : Real.cos φ ≠ 0) :
    V m (p / Real.cos φ) = coeff m * (p / Real.cos φ) ^ k m * Real.cos ((k m : ℝ) * φ) := by
  set y : ℝ := p * Real.tan φ with hy
  have hsq : (p / Real.cos φ) ^ 2 - p ^ 2 = y ^ 2 := by
    rw [hy, Real.tan_eq_sin_div_cos]
    have := Real.sin_sq_add_cos_sq φ
    field_simp
    nlinarith [this]
  unfold V
  rw [hsq, Vsum_sq_eq_re, mul_assoc]
  congr 1
  have h1 : ((p : ℂ) + (y : ℂ) * I) = ((p / Real.cos φ : ℝ) : ℂ) * Complex.exp ((φ : ℂ) * I) := by
    rw [Complex.exp_mul_I, hy, Real.tan_eq_sin_div_cos]
    have hc : Complex.cos (φ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_cos]; exact_mod_cast hφ
    push_cast
    field_simp
  rw [h1, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have : (k m : ℂ) * ((φ : ℂ) * I) = (((k m : ℝ) * φ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

end Calibration

end SandierSerfaty
