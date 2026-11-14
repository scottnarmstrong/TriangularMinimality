/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.OmittedModes
public import SandierSerfaty.Tails.Coefficient
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The retained modes on `(0, b]` (paper §6.3)

On `(0, R₀)` the data are the hexagon data: `u_0 = γ = -log r + π r²/2` and `u_m = (-1)^m c_m r^{k_m}`
(`Radial.lean`). Hence `B̃₁(t) = π t + ∑_{m=1}^{38} (-1)^m k_m c_m t^{k_m - 1}` for `0 < t < R₀`
(`Trunc_B₁_small`), and, using `t ≤ b < 2/7`, `|c_1| < 1` (the finite premise) and `|c_m| ≤ 7/(k_m a^{k_m})` for
`m ≥ 2` (`tail:coefficient-uniform`), `|B̃₁(t)| + |B̃₁'(t)| < 10` (`B₁_small`; the paper's bound is for the
norm `|B̃₁|_{2,t}`, which adds the nonnegative term `|B̃₁''(t)|/2`, but only the first-order norm enters
the propagation).

`Bt1d t = ∑_{i ≤ 38} u_i''(t) - 1/t²` is the derivative `B̃₁'(t)` (`Bt1d_eq`, `jet_Bt1`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- `B̃₁'(t) = ∑_{i ≤ 38} u_i''(t) - 1/t²`. -/
@[expose] noncomputable def Bt1d (t : ℝ) : ℝ := ∑ i ∈ Finset.range 39, deriv (deriv (u i)) t - 1 / t ^ 2

theorem Trunc_B₁_eq {r : ℝ} (hr : 0 < r) : Trunc.B₁ r = ∑ i ∈ Finset.range 39, deriv (u i) r + 1 / r := by
  unfold Trunc.B₁; rw [deriv_trunc_B hr]

/-- `B̃₁` has the first-order jet `(B̃₁, B̃₁')` on `(0, ∞)`. -/
theorem jet_Bt1 : Jet2 (Ioi 0) ∅ Trunc.B₁ Bt1d (fun _ => 0) := by
  refine ⟨fun x hx => ?_, fun x hx => absurd hx (notMem_empty x), empty_subset _⟩
  have h1 : HasDerivAt (fun r => ∑ i ∈ Finset.range 39, deriv (u i) r)
      (∑ i ∈ Finset.range 39, deriv (deriv (u i)) x) x :=
    HasDerivAt.fun_sum fun i _ => (jet_u i).d1 x hx
  have h2 : HasDerivAt (fun r : ℝ => 1 / r) (-(1 / x ^ 2)) x := by
    have := (hasDerivAt_inv (ne_of_gt hx))
    simpa [one_div] using this
  have h3 := h1.add h2
  refine (h3.congr_deriv (by unfold Bt1d; ring)).congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => Trunc_B₁_eq hy

/-! ### Explicit form on `(0, R₀)` -/

theorem hasDerivAt_gamma {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt gamma (-1 / r + Real.pi * r) r := by
  unfold gamma
  have h1 := (Real.hasDerivAt_log hr).neg
  have h2 := (((hasDerivAt_pow 2 r).const_mul Real.pi).div_const 2)
  refine (h1.add h2).congr_deriv ?_
  simp
  ring

theorem hasDerivAt_gamma1 {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => -1 / r + Real.pi * r) (1 / r ^ 2 + Real.pi) r := by
  have h1 := (hasDerivAt_inv hr).const_mul (-1 : ℝ)
  have h2 := (hasDerivAt_id' r).const_mul Real.pi
  refine (h1.add h2).congr_deriv ?_
  field_simp

theorem deriv_u_zero {r : ℝ} (hr : 0 < r) (hR : r < R₀) :
    deriv (u 0) r = -1 / r + Real.pi * r ∧ deriv (deriv (u 0)) r = 1 / r ^ 2 + Real.pi := by
  have hev : u 0 =ᶠ[nhds r] gamma :=
    Filter.eventually_of_mem (Iio_mem_nhds hR) fun s hs => u_zero_of_le_R₀ (le_of_lt hs)
  have h1 : deriv (u 0) r = -1 / r + Real.pi * r := by
    rw [hev.deriv_eq]; exact (hasDerivAt_gamma (ne_of_gt hr)).deriv
  refine ⟨h1, ?_⟩
  have h2 : deriv (u 0) =ᶠ[nhds r] fun s => -1 / s + Real.pi * s := by
    filter_upwards [hev.deriv, Ioi_mem_nhds hr] with s hs hs0
    rw [hs]; exact (hasDerivAt_gamma (ne_of_gt hs0)).deriv
  rw [h2.deriv_eq]; exact (hasDerivAt_gamma1 (ne_of_gt hr)).deriv

/-- The coefficient function `(-1)^i c_i k_i r^{k_i - 1}` of `u_i'`. -/
@[expose] noncomputable def uc1 (i : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ i * coeff i * ((k i : ℝ) * r ^ (k i - 1))

/-- The coefficient function `(-1)^i c_i k_i (k_i - 1) r^{k_i - 2}` of `u_i''`. -/
@[expose] noncomputable def uc2 (i : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ i * coeff i * ((k i : ℝ) * (((k i - 1 : ℕ) : ℝ) * r ^ (k i - 1 - 1)))

theorem deriv_u_pos {i : ℕ} (hi : 1 ≤ i) {r : ℝ} (hR : r < R₀) :
    deriv (u i) r = uc1 i r ∧ deriv (deriv (u i)) r = uc2 i r := by
  have hev : u i =ᶠ[nhds r] fun s => (-1 : ℝ) ^ i * coeff i * s ^ k i :=
    Filter.eventually_of_mem (Iio_mem_nhds hR) fun s hs => u_of_le_R₀ (by omega) (le_of_lt hs)
  have hd : ∀ s : ℝ, HasDerivAt (fun s => (-1 : ℝ) ^ i * coeff i * s ^ k i) (uc1 i s) s := fun s => by
    have := (hasDerivAt_pow (k i) s).const_mul ((-1 : ℝ) ^ i * coeff i)
    refine this.congr_deriv ?_
    unfold uc1; ring
  have hd2 : ∀ s : ℝ, HasDerivAt (uc1 i) (uc2 i s) s := fun s => by
    have := ((hasDerivAt_pow (k i - 1) s).const_mul (k i : ℝ)).const_mul ((-1 : ℝ) ^ i * coeff i)
    refine this.congr_deriv ?_
    unfold uc2; ring
  refine ⟨by rw [hev.deriv_eq]; exact (hd r).deriv, ?_⟩
  have h2 : deriv (u i) =ᶠ[nhds r] uc1 i := by
    filter_upwards [hev.deriv] with s hs
    rw [hs]; exact (hd s).deriv
  rw [h2.deriv_eq]; exact (hd2 r).deriv

theorem Trunc_B₁_small {r : ℝ} (hr : 0 < r) (hR : r < R₀) :
    Trunc.B₁ r = Real.pi * r + ∑ m ∈ Finset.range 38, uc1 (m + 1) r := by
  rw [Trunc_B₁_eq hr]
  rw [Finset.sum_range_succ', (deriv_u_zero hr hR).1]
  have : ∑ m ∈ Finset.range 38, deriv (u (m + 1)) r = ∑ m ∈ Finset.range 38, uc1 (m + 1) r :=
    Finset.sum_congr rfl fun m _ => (deriv_u_pos (by omega) hR).1
  rw [this]
  field_simp
  ring

theorem Bt1d_small {r : ℝ} (hr : 0 < r) (hR : r < R₀) :
    Bt1d r = Real.pi + ∑ m ∈ Finset.range 38, uc2 (m + 1) r := by
  unfold Bt1d
  rw [Finset.sum_range_succ', (deriv_u_zero hr hR).2]
  have : ∑ m ∈ Finset.range 38, deriv (deriv (u (m + 1))) r = ∑ m ∈ Finset.range 38, uc2 (m + 1) r :=
    Finset.sum_congr rfl fun m _ => (deriv_u_pos (by omega) hR).2
  rw [this]
  ring

/-! ### The numerical bound `< 10` -/

theorem b_lt_two_sevenths : b < 2 / 7 := by unfold b; norm_num

theorem b_lt_R₀ : b < R₀ := b_lt_p.trans p_lt_R₀

/-- For `i ≥ 2` and `0 < r ≤ 2/7`: `|u_i'| + |u_i''|` coefficient terms are `≤ 378 (2/729)^i`. -/
theorem uc_small {i : ℕ} (hi : 2 ≤ i) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 2 / 7) :
    |uc1 i r| + |uc2 i r| ≤ 378 * (2 / 729 : ℝ) ^ i := by
  have hk : k i = 6 * i := k_of_pos (by omega)
  have hc : |coeff i| * (k i : ℝ) ≤ 7 := by
    have h := coefficient_uniform hi
    have ha : 1 ≤ a ^ (6 * i) := one_le_pow₀ (by have := a_gt; linarith)
    have hkpos : (0 : ℝ) < ((6 * i : ℕ) : ℝ) := by positivity
    rw [hk]
    have h2 : |coeff i| * ((6 * i : ℕ) : ℝ) ≤ 7 / ((6 * i : ℕ) * a ^ (6 * i)) * ((6 * i : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right h hkpos.le
    refine h2.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨n, hn⟩ : ∃ n, k i = n + 2 := ⟨k i - 2, by omega⟩
  have hn1 : k i - 1 = n + 1 := by omega
  have hn2 : k i - 1 - 1 = n := by omega
  have hrn : r ^ n ≤ (1 / 3 : ℝ) ^ n := pow_le_pow_left₀ hr.le (by linarith) n
  have hr1 : r ≤ 1 := by linarith
  have hrn1 : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr.le hr1 (by omega)
  have hkr : (k i : ℝ) = n + 2 := by exact_mod_cast hn
  have e1 : |uc1 i r| = |coeff i| * ((k i : ℝ) * r ^ (n + 1)) := by
    unfold uc1
    rw [hn1, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k i : ℝ)),
      abs_pow, abs_of_pos hr]
  have e2 : |uc2 i r| = |coeff i| * ((k i : ℝ) * (((n + 1 : ℕ) : ℝ) * r ^ n)) := by
    unfold uc2
    rw [hn1, Nat.add_sub_cancel, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k i : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)), abs_pow, abs_of_pos hr]
  rw [e1, e2]
  have hpow : (1 / 3 : ℝ) ^ n = 9 * (1 / 729 : ℝ) ^ i := by
    have : (1 / 3 : ℝ) ^ (n + 2) = (1 / 729 : ℝ) ^ i := by
      rw [← hn, hk, pow_mul]; norm_num
    rw [pow_add] at this
    linarith
  have hnn : (0 : ℝ) ≤ n := by positivity
  have hi2 : (i : ℝ) ≤ 2 ^ i := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hkc : (k i : ℝ) = 6 * i := by rw [hk]; push_cast; ring
  calc |coeff i| * ((k i : ℝ) * r ^ (n + 1)) + |coeff i| * ((k i : ℝ) * (((n + 1 : ℕ) : ℝ) * r ^ n))
      = (|coeff i| * (k i : ℝ)) * (r ^ (n + 1) + ((n + 1 : ℕ) : ℝ) * r ^ n) := by ring
    _ ≤ 7 * (r ^ n + ((n + 1 : ℕ) : ℝ) * r ^ n) := by
        refine mul_le_mul hc ?_ (by positivity) (by norm_num)
        linarith
    _ = 7 * ((n + 2 : ℝ) * r ^ n) := by push_cast; ring
    _ ≤ 7 * ((n + 2 : ℝ) * (1 / 3 : ℝ) ^ n) := by gcongr
    _ = 7 * (6 * i) * (9 * (1 / 729 : ℝ) ^ i) := by rw [hpow, ← hkr, hkc]; ring
    _ ≤ 378 * (2 / 729 : ℝ) ^ i := by
        have h3 : (1 / 729 : ℝ) ^ i * (i : ℝ) ≤ (1 / 729 : ℝ) ^ i * 2 ^ i :=
          mul_le_mul_of_nonneg_left hi2 (by positivity)
        have h4 : (2 / 729 : ℝ) ^ i = (1 / 729 : ℝ) ^ i * 2 ^ i := by
          rw [← mul_pow]; norm_num
        rw [h4]
        nlinarith

/-- **`B̃₁` on `(0, b]`** (paper §6.3): `|B̃₁(t)| + |B̃₁'(t)| ≤ 10` for `0 < t ≤ b`, given the finite premise
`|c_1| < 1`. -/
theorem B₁_small (hc1 : |coeff 1| < 1) {r : ℝ} (hr : 0 < r) (hrb : r ≤ b) :
    |Trunc.B₁ r| + |Bt1d r| ≤ 10 := by
  have hR : r < R₀ := lt_of_le_of_lt hrb b_lt_R₀
  have hr2 : r ≤ 2 / 7 := hrb.trans b_lt_two_sevenths.le
  rw [Trunc_B₁_small hr hR, Bt1d_small hr hR]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have s1 : |∑ m ∈ Finset.range 38, uc1 (m + 1) r| + |∑ m ∈ Finset.range 38, uc2 (m + 1) r| ≤
      ∑ m ∈ Finset.range 38, (|uc1 (m + 1) r| + |uc2 (m + 1) r|) := by
    rw [Finset.sum_add_distrib]
    exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
  -- the first mode
  have m1 : |uc1 1 r| + |uc2 1 r| ≤ 1 / 2 := by
    have hk1 : k 1 = 6 := by rw [k_of_pos (by omega)]
    have hr4 : r ^ 4 ≤ (2 / 7 : ℝ) ^ 4 := pow_le_pow_left₀ hr.le hr2 4
    have hr5 : r ^ 5 ≤ r ^ 4 := pow_le_pow_of_le_one hr.le (by linarith) (by norm_num)
    have hc0 := abs_nonneg (coeff 1)
    have e : |uc1 1 r| + |uc2 1 r| = |coeff 1| * (6 * r ^ 5 + 30 * r ^ 4) := by
      unfold uc1 uc2
      rw [hk1]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hr, Nat.cast_ofNat]
      norm_num
      ring
    rw [e]
    calc |coeff 1| * (6 * r ^ 5 + 30 * r ^ 4) ≤ 1 * (6 * r ^ 4 + 30 * r ^ 4) := by
          refine mul_le_mul hc1.le (by linarith) (by positivity) (by norm_num)
      _ ≤ 1 / 2 := by norm_num at hr4 ⊢; linarith
  have rest : ∑ m ∈ Finset.range 37, (|uc1 (m + 2) r| + |uc2 (m + 2) r|) ≤ 1 := by
    have h1 : ∑ m ∈ Finset.range 37, (|uc1 (m + 2) r| + |uc2 (m + 2) r|) ≤
        ∑ m ∈ Finset.range 37, 378 * (2 / 729 : ℝ) ^ (m + 2) :=
      Finset.sum_le_sum fun m _ => uc_small (by omega) hr hr2
    refine h1.trans ?_
    have e : ∑ m ∈ Finset.range 37, 378 * (2 / 729 : ℝ) ^ (m + 2) =
        378 * (2 / 729 : ℝ) ^ 2 * ∑ m ∈ Finset.range 37, (2 / 729 : ℝ) ^ m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hg : ∑ m ∈ Finset.range 37, (2 / 729 : ℝ) ^ m ≤ (1 - 2 / 729 : ℝ)⁻¹ := by
      have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 729) (by norm_num)).sum_le_tsum
        (Finset.range 37) (fun _ _ => by positivity)
      rwa [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at this
    rw [e]
    calc 378 * (2 / 729 : ℝ) ^ 2 * ∑ m ∈ Finset.range 37, (2 / 729 : ℝ) ^ m
        ≤ 378 * (2 / 729 : ℝ) ^ 2 * (1 - 2 / 729 : ℝ)⁻¹ := by gcongr
      _ ≤ 1 := by norm_num
  have sum_eq : ∑ m ∈ Finset.range 38, (|uc1 (m + 1) r| + |uc2 (m + 1) r|) =
      ∑ m ∈ Finset.range 37, (|uc1 (m + 2) r| + |uc2 (m + 2) r|) + (|uc1 1 r| + |uc2 1 r|) := by
    rw [Finset.sum_range_succ']
  have t1 : |Real.pi * r + ∑ m ∈ Finset.range 38, uc1 (m + 1) r| ≤
      Real.pi * r + |∑ m ∈ Finset.range 38, uc1 (m + 1) r| :=
    (abs_add_le _ _).trans (by rw [abs_of_pos (by positivity : 0 < Real.pi * r)])
  have t2 : |Real.pi + ∑ m ∈ Finset.range 38, uc2 (m + 1) r| ≤
      Real.pi + |∑ m ∈ Finset.range 38, uc2 (m + 1) r| :=
    (abs_add_le _ _).trans (by rw [abs_of_pos hpi0])
  have hpr : Real.pi * r ≤ 3.15 * (2 / 7) := by nlinarith
  linarith

end Tails

end SandierSerfaty

end
