/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Exterior
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# `comp:inner-exact`: `f₀` and `e` on the first radial interval

on `0 < t ≤ p - .06 = p - c` all `b_m` (`m ≥ 1`) vanish, `D_m(t) = -a_m t^{k_m}`
(`a_m = (-1)^m c_m`), `D_0 = 0`, and the full infinite-mode functions are
`f₀(t) = (π t² - 1/2) log t - 3 π² t⁴/8`, `e(t) = 0`.

* `D_succ_of_le`, `deriv_D_succ_of_le`: the data `D_{m+1} = -ptm m` and `Q_{m+1} = 0` on `(0, p - c]`;
* `hasSum_integral_of_bound`: termwise integration of a series with a summable constant majorant;
* the moments `∫₀ᵗ P(r) r`, `∫₀ᵗ P'(r) r^j`, `∫₀ᵗ r P'(r)²` of the coefficient series
  `P = Pser` as series;
* `inner_exact`: the cancellation of the non-constant modes, with the closed forms
  `∫₀ᵗ γ r dr = -t²/2 log t + t²/4 + π t⁴/8`.
-/

open Set Filter Topology MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

theorem p_sub_c_lt_half : p - c < 1 / 2 := by
  have := p_lt; unfold c; linarith

/-- Termwise integration over `[0, t]` of a series of continuous functions with a summable
constant majorant. -/
theorem hasSum_integral_of_bound {t : ℝ} (ht : 0 ≤ t) {F : ℕ → ℝ → ℝ}
    (hF : ∀ n, ContinuousOn (F n) (Icc 0 t)) {M : ℕ → ℝ} (hM : Summable M)
    (hb : ∀ n, ∀ r ∈ Ioc 0 t, |F n r| ≤ M n) :
    HasSum (fun n => ∫ r in (0 : ℝ)..t, F n r) (∫ r in (0 : ℝ)..t, ∑' n, F n r) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => M n) ?_ ?_ ?_ ?_ ?_
  · intro n
    rw [Set.uIoc_of_le ht]
    exact ((hF n).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · intro n
    refine Filter.Eventually.of_forall fun r hr => ?_
    rw [Set.uIoc_of_le ht] at hr
    simpa [Real.norm_eq_abs] using hb n r hr
  · exact Filter.Eventually.of_forall fun r _ => hM
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun r hr => ?_
    rw [Set.uIoc_of_le ht] at hr
    exact (Summable.of_norm_bounded hM fun n => by
      rw [Real.norm_eq_abs]; exact hb n r hr).hasSum

/-! ### The data on `(0, p - c]` -/

theorem D_zero_inner {r : ℝ} (hr : r ≤ p - c) : D 0 r = 0 :=
  D_zero_of_le_R₀ (by have := p_lt_R₀; have := c_pos; linarith)

theorem D_succ_of_le {m : ℕ} {r : ℝ} (hr : r ≤ p - c) : D (m + 1) r = -ptm m r := by
  rw [D, bRad_of_le_inner (Nat.succ_pos m) hr,
    u_succ_eq_ptm (by have := p_lt_R₀; have := c_pos; linarith)]
  ring

theorem eqOn_D_succ (m : ℕ) : EqOn (D (m + 1)) (fun r => -ptm m r) (Ioc 0 (p - c)) :=
  fun _ hr => D_succ_of_le hr.2

theorem contDiff_ptm (m : ℕ) : ContDiff ℝ 2 (ptm m) := by unfold ptm; fun_prop

theorem deriv_D_succ_of_le {m : ℕ} {r : ℝ} (hr : r ∈ Ioc 0 (p - c)) :
    deriv (D (m + 1)) r = -dptm m r := by
  have h := deriv_deriv_eq_of_eqOn (f := D (m + 1)) (g := fun r => -ptm m r) (s := Ioc 0 (p - c))
    (U := Ioi 0) (uniqueDiffOn_Ioc 0 (p - c)) isOpen_Ioi
    (fun x hx => hx.1) (eqOn_D_succ m) (contDiffOn_D _) (contDiff_ptm m).neg.contDiffOn
  rw [h.1 hr]
  exact ((hasDerivAt_ptm m r).neg).deriv

theorem Q_succ_of_le {m : ℕ} {r : ℝ} (hr : r ∈ Ioc 0 (p - c)) : Q (m + 1) r = 0 := by
  rw [Q, deriv_D_succ_of_le hr, D_succ_of_le hr.2, k_of_pos (Nat.succ_pos m)]
  unfold ptm dptm
  have hn : 1 ≤ 6 * (m + 1) := by omega
  have : r * r ^ (6 * (m + 1) - 1) = r ^ (6 * (m + 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  generalize 6 * (m + 1) = n at *
  linear_combination (-((-1 : ℝ) ^ (m + 1) * coeff (m + 1) * (n : ℝ))) * this

theorem Q_zero_of_le {r : ℝ} (hr : r ∈ Ioc 0 (p - c)) : Q 0 r = 0 := by
  have h := deriv_deriv_eq_of_eqOn (f := D 0) (g := fun _ => (0 : ℝ)) (s := Ioc 0 (p - c))
    (U := Ioi 0) (uniqueDiffOn_Ioc 0 (p - c)) isOpen_Ioi (fun x hx => hx.1)
    (fun x hx => D_zero_inner hx.2) (contDiffOn_D _) contDiffOn_const
  have e : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by funext x; simp
  have := h.1 hr
  rw [e] at this
  rw [Q, this, D_zero_inner hr.2]; simp

/-- `e = 0` on `(0, p - c]` (`comp:inner-exact`, second part). -/
theorem e_inner {t : ℝ} (ht : t ∈ Ioc 0 (p - c)) : e t = 0 := by
  have : ∀ i, Q i t = 0 := fun i => by
    cases i with
    | zero => exact Q_zero_of_le ht
    | succ m => exact Q_succ_of_le ht
  simp [e, this]

/-! ### Moments of the coefficient series -/

/-- The coefficient `(-1)^{m+1} c_{m+1}` of the `m`-th term of `P = Pser`. -/
@[expose] noncomputable def pa (m : ℕ) : ℝ := (-1 : ℝ) ^ (m + 1) * coeff (m + 1)

/-- The exponent `6 (m + 1)` of the `m`-th term of `P = Pser`. -/
@[expose] def pk (m : ℕ) : ℕ := 6 * (m + 1)

/-- `P' = ∑ dptm`. -/
@[expose] noncomputable def Pd (r : ℝ) : ℝ := ∑' m, dptm m r

theorem ptm_eq (m : ℕ) (r : ℝ) : ptm m r = pa m * r ^ pk m := rfl

theorem pk_pos (m : ℕ) : 0 < pk m := by unfold pk; omega

theorem dptm_eq (m : ℕ) (r : ℝ) : dptm m r = pa m * ((pk m : ℝ) * r ^ (pk m - 1)) := rfl

theorem mul_dptm (m : ℕ) (r : ℝ) : r * dptm m r = pa m * (pk m : ℝ) * r ^ pk m := by
  rw [dptm_eq]
  have : r * r ^ (pk m - 1) = r ^ pk m := by
    rw [← pow_succ', Nat.sub_add_cancel (pk_pos m)]
  linear_combination (pa m * (pk m : ℝ)) * this

theorem abs_dptm_le_Icc {m : ℕ} {r : ℝ} (hr : r ∈ Icc 0 (1 / 2)) : |dptm m r| ≤ r ^ 5 * N₁ m := by
  rcases hr.1.eq_or_lt with h | h
  · subst h
    rw [dptm_eq]
    have : (0 : ℝ) ^ (pk m - 1) = 0 := zero_pow (by have := pk_pos m; unfold pk at *; omega)
    simp [this]
  · exact abs_dptm_le ⟨h, hr.2⟩

theorem abs_ptm_le_Icc {m : ℕ} {r : ℝ} (hr : r ∈ Icc 0 (1 / 2)) : |ptm m r| ≤ r ^ 6 * N₀ m := by
  rcases hr.1.eq_or_lt with h | h
  · subst h
    rw [ptm_eq]
    have : (0 : ℝ) ^ pk m = 0 := zero_pow (pk_pos m).ne'
    simp [this]
  · exact abs_ptm_le ⟨h, hr.2⟩

theorem N₀_nonneg (m : ℕ) : 0 ≤ N₀ m := by
  have h := (abs_nonneg _).trans (abs_ptm_le (m := m) (r := 1 / 2) ⟨by norm_num, le_rfl⟩)
  by_contra hn
  replace hn := lt_of_not_ge hn
  have : (1 / 2 : ℝ) ^ 6 * N₀ m < 0 := mul_neg_of_pos_of_neg (by norm_num) hn
  linarith

theorem N₁_nonneg (m : ℕ) : 0 ≤ N₁ m := by
  have h := (abs_nonneg _).trans (abs_dptm_le (m := m) (r := 1 / 2) ⟨by norm_num, le_rfl⟩)
  by_contra hn
  replace hn := lt_of_not_ge hn
  have : (1 / 2 : ℝ) ^ 5 * N₁ m < 0 := mul_neg_of_pos_of_neg (by norm_num) hn
  linarith

theorem continuousOn_Pd {t : ℝ} (ht : t ≤ 1 / 2) : ContinuousOn Pd (Icc 0 t) := by
  unfold Pd
  refine continuousOn_tsum (u := fun m => (1 / 2 : ℝ) ^ 5 * N₁ m) (fun m => ?_)
    (summable_N₁.mul_left _) (fun m r hr => ?_)
  · unfold dptm; fun_prop
  · rw [Real.norm_eq_abs]
    refine (abs_dptm_le_Icc ⟨hr.1, hr.2.trans ht⟩).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1 (hr.2.trans ht) 5) (N₁_nonneg m)

theorem abs_Pd_le {r : ℝ} (hr : r ∈ Icc 0 (1 / 2)) : |Pd r| ≤ (1 / 2 : ℝ) ^ 5 * ∑' m, N₁ m := by
  have h := tsum_of_norm_bounded (summable_N₁.mul_left ((1 / 2 : ℝ) ^ 5)).hasSum
    (f := fun m => dptm m r) fun m => by
      rw [Real.norm_eq_abs]
      refine (abs_dptm_le_Icc hr).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1 hr.2 5) (N₁_nonneg m)
  rwa [tsum_mul_left, Real.norm_eq_abs] at h

theorem deriv_Pser_eq {r : ℝ} (hr : r ∈ Ioo 0 (1 / 2)) : deriv Pser r = Pd r :=
  (hasDerivAt_Pser hr).deriv

theorem B₁_eq {r : ℝ} (hr : r ∈ Ioo 0 (1 / 2)) : B₁ r = Real.pi * r + Pd r := by
  unfold B₁
  rw [deriv_B_eq hr, deriv_Pser_eq hr]
  have := hr.1.ne'
  field_simp
  ring

theorem int_dptm_pow (m : ℕ) (t : ℝ) (j : ℕ) :
    ∫ r in (0 : ℝ)..t, dptm m r * r ^ j
      = pa m * (pk m : ℝ) * t ^ (pk m + j) / ((pk m : ℝ) + j) := by
  have hn : pk m - 1 + 1 = pk m := Nat.sub_add_cancel (pk_pos m)
  have h1 : ∀ r : ℝ, dptm m r * r ^ j = (pa m * (pk m : ℝ)) * r ^ (pk m - 1 + j) := fun r => by
    rw [dptm_eq, pow_add]; ring
  simp only [h1]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have h2 : pk m - 1 + j + 1 = pk m + j := by omega
  have hpos : (0 : ℝ) < (pk m : ℝ) + j := by have := pk_pos m; positivity
  rw [h2]
  have : ((pk m - 1 + j : ℕ) : ℝ) + 1 = (pk m : ℝ) + j := by
    have : ((pk m - 1 : ℕ) : ℝ) + 1 = pk m := by exact_mod_cast hn
    push_cast at this ⊢; linarith
  rw [this, zero_pow (by omega)]
  ring

/-- `∫₀ᵗ P'(r) r^j dr = ∑_m a_m k_m t^{k_m + j}/(k_m + j)`. -/
theorem hasSum_int_Pd_mul_pow {t : ℝ} (ht : 0 ≤ t) (hth : t ≤ 1 / 2) (j : ℕ) :
    HasSum (fun m => pa m * (pk m : ℝ) * t ^ (pk m + j) / ((pk m : ℝ) + j))
      (∫ r in (0 : ℝ)..t, Pd r * r ^ j) := by
  have h := hasSum_integral_of_bound ht (F := fun m r => dptm m r * r ^ j)
    (fun m => by unfold dptm; fun_prop)
    (M := fun m => (1 / 2 : ℝ) ^ 5 * N₁ m * (1 / 2 : ℝ) ^ j)
    ((summable_N₁.mul_left _).mul_right _) (fun m r hr => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hr.1.le j)]
      have hr' : r ∈ Icc 0 (1 / 2) := ⟨hr.1.le, hr.2.trans hth⟩
      refine mul_le_mul ((abs_dptm_le_Icc hr').trans ?_) (pow_le_pow_left₀ hr.1.le hr'.2 j)
        (pow_nonneg hr.1.le j) (mul_nonneg (by norm_num) (N₁_nonneg m))
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hr'.2 5) (N₁_nonneg m))
  have e1 : ∀ r, ∑' m, dptm m r * r ^ j = Pd r * r ^ j := fun r => by
    unfold Pd; rw [tsum_mul_right]
  simp only [e1] at h
  convert h using 1
  funext m
  exact (int_dptm_pow m t j).symm

theorem continuousOn_Pser {t : ℝ} (ht : t ≤ 1 / 2) : ContinuousOn Pser (Icc 0 t) := by
  unfold Pser
  refine continuousOn_tsum (u := fun m => (1 / 2 : ℝ) ^ 6 * N₀ m) (fun m => ?_)
    (summable_N₀.mul_left _) (fun m r hr => ?_)
  · unfold ptm; fun_prop
  · rw [Real.norm_eq_abs]
    refine (abs_ptm_le_Icc ⟨hr.1, hr.2.trans ht⟩).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1 (hr.2.trans ht) 6) (N₀_nonneg m)

theorem int_ptm_mul (m : ℕ) (t : ℝ) :
    ∫ r in (0 : ℝ)..t, ptm m r * r = pa m * t ^ (pk m + 2) / ((pk m : ℝ) + 2) := by
  have h1 : ∀ r : ℝ, ptm m r * r = pa m * r ^ (pk m + 1) := fun r => by
    rw [ptm_eq]; ring
  simp only [h1]
  rw [intervalIntegral.integral_const_mul, integral_pow, zero_pow (by omega)]
  push_cast
  ring

/-- `∫₀ᵗ P(r) r dr = ∑_m a_m t^{k_m + 2}/(k_m + 2)`. -/
theorem hasSum_int_Pser_mul {t : ℝ} (ht : 0 ≤ t) (hth : t ≤ 1 / 2) :
    HasSum (fun m => pa m * t ^ (pk m + 2) / ((pk m : ℝ) + 2))
      (∫ r in (0 : ℝ)..t, Pser r * r) := by
  have h := hasSum_integral_of_bound ht (F := fun m r => ptm m r * r)
    (fun m => by unfold ptm; fun_prop)
    (M := fun m => (1 / 2 : ℝ) ^ 6 * N₀ m * (1 / 2 : ℝ))
    ((summable_N₀.mul_left _).mul_right _) (fun m r hr => by
      rw [abs_mul, abs_of_nonneg hr.1.le]
      have hr' : r ∈ Icc 0 (1 / 2) := ⟨hr.1.le, hr.2.trans hth⟩
      refine mul_le_mul ((abs_ptm_le_Icc hr').trans ?_) hr'.2 hr.1.le
        (mul_nonneg (by norm_num) (N₀_nonneg m))
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hr'.2 6) (N₀_nonneg m))
  have e1 : ∀ r, ∑' m, ptm m r * r = Pser r * r := fun r => by
    unfold Pser; rw [tsum_mul_right]
  simp only [e1] at h
  convert h using 1
  funext m
  exact (int_ptm_mul m t).symm

/-- `∫₀ᵗ r P'(r)² dr = ∑_m a_m k_m ∫₀ᵗ P'(r) r^{k_m} dr`. -/
theorem hasSum_int_Pd_sq {t : ℝ} (ht : 0 ≤ t) (hth : t ≤ 1 / 2) :
    HasSum (fun m => pa m * (pk m : ℝ) * ∫ r in (0 : ℝ)..t, Pd r * r ^ pk m)
      (∫ r in (0 : ℝ)..t, r * Pd r ^ 2) := by
  have hPd := continuousOn_Pd hth
  have h := hasSum_integral_of_bound ht (F := fun m r => (r * dptm m r) * Pd r)
    (fun m => by
      refine ContinuousOn.mul ?_ (hPd.mono (Icc_subset_Icc_right le_rfl))
      unfold dptm; fun_prop)
    (M := fun m => (1 / 2 : ℝ) ^ 6 * N₁ m * ((1 / 2 : ℝ) ^ 5 * ∑' m, N₁ m))
    ((summable_N₁.mul_left _).mul_right _) (fun m r hr => by
      rw [abs_mul, abs_mul, abs_of_nonneg hr.1.le]
      have hr' : r ∈ Icc 0 (1 / 2) := ⟨hr.1.le, hr.2.trans hth⟩
      have hC : 0 ≤ (1 / 2 : ℝ) ^ 5 * ∑' m, N₁ m :=
        mul_nonneg (by norm_num) (tsum_nonneg N₁_nonneg)
      refine mul_le_mul ?_ (abs_Pd_le hr') (abs_nonneg _)
        (mul_nonneg (by norm_num) (N₁_nonneg m))
      calc r * |dptm m r| ≤ r * (r ^ 5 * N₁ m) :=
            mul_le_mul_of_nonneg_left (abs_dptm_le_Icc hr') hr.1.le
        _ = r ^ 6 * N₁ m := by ring
        _ ≤ (1 / 2 : ℝ) ^ 6 * N₁ m :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hr'.2 6) (N₁_nonneg m))
  have e1 : ∀ r, ∑' m, (r * dptm m r) * Pd r = r * Pd r ^ 2 := fun r => by
    rw [tsum_mul_right]
    have : ∑' m, r * dptm m r = r * Pd r := by unfold Pd; rw [tsum_mul_left]
    rw [this]; ring
  simp only [e1] at h
  convert h using 1
  funext m
  have h2 : ∀ r : ℝ, (r * dptm m r) * Pd r = (pa m * (pk m : ℝ)) * (Pd r * r ^ pk m) := fun r => by
    rw [mul_dptm]; ring
  simp only [h2]
  rw [intervalIntegral.integral_const_mul]

/-- `∫₀ᵗ γ(r) r dr = -t²/2 log t + t²/4 + π t⁴/8` (paper `comp:inner-exact`). -/
theorem integral_gamma_mul {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, gamma r * r
      = -(t ^ 2 / 2) * Real.log t + t ^ 2 / 4 + Real.pi * t ^ 4 / 8 := by
  have hcont : ContinuousOn (fun r : ℝ => -(r ^ 2 / 2) * Real.log r + r ^ 2 / 4 + Real.pi * r ^ 4 / 8)
      (Icc 0 t) := by
    refine Continuous.continuousOn ?_
    have h1 : Continuous fun r : ℝ => r * Real.log r := Real.continuous_mul_log
    have : (fun r : ℝ => -(r ^ 2 / 2) * Real.log r + r ^ 2 / 4 + Real.pi * r ^ 4 / 8)
        = fun r => -(r / 2) * (r * Real.log r) + r ^ 2 / 4 + Real.pi * r ^ 4 / 8 := by
      funext r; ring
    rw [this]; fun_prop
  have hderiv : ∀ x ∈ Ioo 0 t, HasDerivAt
      (fun r : ℝ => -(r ^ 2 / 2) * Real.log r + r ^ 2 / 4 + Real.pi * r ^ 4 / 8) (gamma x * x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 := (((hasDerivAt_pow 2 x).div_const 2).neg).mul (Real.hasDerivAt_log hx0)
    have h2 := ((hasDerivAt_pow 2 x).div_const 4)
    have h3 := ((hasDerivAt_pow 4 x).const_mul Real.pi).div_const 8
    refine ((h1.add h2).add h3).congr_deriv ?_
    unfold gamma
    simp only [Pi.neg_apply]
    field_simp
    ring
  have hint : IntervalIntegrable (fun r => gamma r * r) volume 0 t := by
    have : ContinuousOn (fun r : ℝ => gamma r * r) (Icc 0 t) := by
      have : (fun r : ℝ => gamma r * r) = fun r => -(r * Real.log r) + Real.pi / 2 * r ^ 3 := by
        funext r; unfold gamma; ring
      rw [this]
      refine Continuous.continuousOn ?_
      have h1 : Continuous fun r : ℝ => r * Real.log r := Real.continuous_mul_log
      fun_prop
    exact (this.intervalIntegrable_of_Icc ht)
  rcases ht.eq_or_lt with h0 | h0
  · subst h0; simp
  · have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0.le hcont hderiv hint
    rw [this]; simp

/-! ### Assembly -/

theorem integral_congr_Ioc {t : ℝ} (ht : 0 ≤ t) {f g : ℝ → ℝ} (h : ∀ r ∈ Ioc 0 t, f r = g r) :
    ∫ r in (0 : ℝ)..t, f r = ∫ r in (0 : ℝ)..t, g r :=
  intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => h r (by
    rwa [Set.uIoc_of_le ht] at hr))

theorem tsum_succ_of_zero {g : ℕ → ℝ} (h0 : g 0 = 0) : ∑' i, g i = ∑' m, g (m + 1) := by
  refine (Function.Injective.tsum_eq (Nat.succ_injective) (f := g) ?_).symm
  intro i hi
  have : i ≠ 0 := fun h => hi (h ▸ h0)
  exact ⟨i - 1, by simp; omega⟩

theorem tsum_succ_prod_of_zero {g : ℕ × ℕ → ℝ} (h0 : ∀ ij : ℕ × ℕ, ij.1 = 0 ∨ ij.2 = 0 → g ij = 0) :
    ∑' ij, g ij = ∑' mn : ℕ × ℕ, g (mn.1 + 1, mn.2 + 1) := by
  have hinj : Function.Injective (fun mn : ℕ × ℕ => (mn.1 + 1, mn.2 + 1)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  refine (Function.Injective.tsum_eq hinj (f := g) ?_).symm
  intro ij hij
  have h1 : ij.1 ≠ 0 := fun h => hij (h0 ij (Or.inl h))
  have h2 : ij.2 ≠ 0 := fun h => hij (h0 ij (Or.inr h))
  exact ⟨(ij.1 - 1, ij.2 - 1), Prod.ext (by simp; omega) (by simp; omega)⟩

section Assembly

theorem hth {t : ℝ} (htc : t ≤ p - c) : t ≤ 1 / 2 := htc.trans p_sub_c_lt_half.le

theorem mem_Ioo_half {t : ℝ} (htc : t ≤ p - c) {r : ℝ} (hr : r ∈ Ioc 0 t) : r ∈ Ioo 0 (1 / 2) :=
  ⟨hr.1, lt_of_le_of_lt hr.2 (htc.trans_lt p_sub_c_lt_half)⟩

theorem int_Pd_zero {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) : ∫ r in (0 : ℝ)..t, Pd r = Pser t := by
  have h := hasSum_int_Pd_mul_pow ht.le (hth htc) 0
  simp only [pow_zero, mul_one, add_zero, Nat.cast_zero] at h
  have hP : HasSum (fun m => ptm m t) (Pser t) := by
    refine (Summable.of_norm_bounded ((summable_N₀.mul_left ((1 / 2 : ℝ) ^ 6))) fun m => ?_).hasSum
    rw [Real.norm_eq_abs]
    refine (abs_ptm_le_Icc ⟨ht.le, hth htc⟩).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le (hth htc) 6) (N₀_nonneg m)
  refine h.unique ?_
  convert hP using 1
  funext m
  have := (pk_pos m)
  rw [ptm_eq]
  field_simp

theorem S₁_inner {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) : S₁ t = (-(t ^ 2 / 2) * Real.log t + t ^ 2 / 4 + Real.pi * t ^ 4 / 8)
    + ∫ r in (0 : ℝ)..t, Pser r * r := by
  have hc : ContinuousOn (fun r => gamma r * r) (Icc 0 t) := by
    have : (fun r : ℝ => gamma r * r) = fun r => -(r * Real.log r) + Real.pi / 2 * r ^ 3 := by
      funext r; unfold gamma; ring
    rw [this]
    refine Continuous.continuousOn ?_
    have h1 : Continuous fun r : ℝ => r * Real.log r := Real.continuous_mul_log
    fun_prop
  have hP : ContinuousOn (fun r => Pser r * r) (Icc 0 t) :=
    (continuousOn_Pser (hth htc)).mul continuousOn_id
  unfold S₁
  rw [integral_congr_Ioc ht.le (g := fun r => gamma r * r + Pser r * r) (fun r hr => by
    rw [B_eq_gamma_add_Pser ⟨hr.1, (mem_Ioo_half htc hr).2.le⟩]; ring),
    intervalIntegral.integral_add (hc.intervalIntegrable_of_Icc ht.le)
      (hP.intervalIntegrable_of_Icc ht.le), integral_gamma_mul ht.le]

theorem S₂_inner {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) :
    S₂ t = -(Real.pi * t ^ 2) - 2 * Pser t + Real.pi ^ 2 * t ^ 4 / 4
      + 2 * Real.pi * (∫ r in (0 : ℝ)..t, Pd r * r ^ 2) + ∫ r in (0 : ℝ)..t, r * Pd r ^ 2 := by
  have hPdc : ContinuousOn Pd (Icc 0 t) := continuousOn_Pd (hth htc)
  have i1 : IntervalIntegrable (fun r : ℝ => (-2 * Real.pi) * r) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun r : ℝ => (-2 : ℝ) * Pd r) volume 0 t :=
    (continuousOn_const.mul hPdc).intervalIntegrable_of_Icc ht.le
  have i3 : IntervalIntegrable (fun r : ℝ => Real.pi ^ 2 * r ^ 3) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i4 : IntervalIntegrable (fun r : ℝ => (2 * Real.pi) * (Pd r * r ^ 2)) volume 0 t :=
    (continuousOn_const.mul (hPdc.mul (continuousOn_id.pow 2))).intervalIntegrable_of_Icc ht.le
  have i5 : IntervalIntegrable (fun r : ℝ => r * Pd r ^ 2) volume 0 t :=
    (continuousOn_id.mul (hPdc.pow 2)).intervalIntegrable_of_Icc ht.le
  have i6 : IntervalIntegrable (fun r : ℝ => Pd r * r ^ 2) volume 0 t :=
    (hPdc.mul (continuousOn_id.pow 2)).intervalIntegrable_of_Icc ht.le
  have i7 : IntervalIntegrable Pd volume 0 t := hPdc.intervalIntegrable_of_Icc ht.le
  unfold S₂
  rw [integral_congr_Ioc ht.le (g := fun r => (-2 * Real.pi) * r + (-2) * Pd r
      + Real.pi ^ 2 * r ^ 3 + (2 * Real.pi) * (Pd r * r ^ 2) + r * Pd r ^ 2) (fun r hr => by
    rw [B₁_eq (mem_Ioo_half htc hr)]; ring),
    intervalIntegral.integral_add (((i1.add i2).add i3).add i4) i5,
    intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_id, integral_pow, int_Pd_zero ht htc]
  norm_num
  ring

theorem Ik_eq {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) (m : ℕ) :
    ∫ r in (0 : ℝ)..t, B₁ r * r ^ pk m
      = Real.pi * t ^ (pk m + 2) / ((pk m : ℝ) + 2) + ∫ r in (0 : ℝ)..t, Pd r * r ^ pk m := by
  have hPdc : ContinuousOn Pd (Icc 0 t) := continuousOn_Pd (hth htc)
  have i1 : IntervalIntegrable (fun r : ℝ => Real.pi * r ^ (pk m + 1)) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have i2 : IntervalIntegrable (fun r : ℝ => Pd r * r ^ pk m) volume 0 t :=
    (hPdc.mul (continuousOn_id.pow _)).intervalIntegrable_of_Icc ht.le
  rw [integral_congr_Ioc ht.le (g := fun r => Real.pi * r ^ (pk m + 1) + Pd r * r ^ pk m)
    (fun r hr => by rw [B₁_eq (mem_Ioo_half htc hr)]; ring),
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul, integral_pow,
    zero_pow (by omega)]
  push_cast
  ring

theorem hasSum_ptm {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) : HasSum (fun m => ptm m t) (Pser t) := by
  refine (Summable.of_norm_bounded ((summable_N₀.mul_left ((1 / 2 : ℝ) ^ 6))) fun m => ?_).hasSum
  rw [Real.norm_eq_abs]
  refine (abs_ptm_le_Icc ⟨ht.le, hth htc⟩).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le (hth htc) 6) (N₀_nonneg m)

theorem inner_T1 {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) :
    t ^ 2 * ∑' i : ℕ, D i t / ((k i : ℝ) + 2) = -∫ r in (0 : ℝ)..t, Pser r * r := by
  have hA := hasSum_int_Pser_mul ht.le (hth htc)
  rw [tsum_succ_of_zero (by simp [D_zero_inner htc]), ← tsum_mul_left, ← hA.tsum_eq,
    ← tsum_neg]
  refine tsum_congr fun m => ?_
  rw [D_succ_of_le htc, k_of_pos (Nat.succ_pos m), ptm_eq]
  have : ((6 * (m + 1) : ℕ) : ℝ) = (pk m : ℝ) := rfl
  rw [this]
  have : (0 : ℝ) < (pk m : ℝ) + 2 := by positivity
  field_simp
  ring

theorem inner_T2 {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) :
    ∑' i : ℕ, (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t)
      = 2 * Pser t - 2 * Real.pi * (∫ r in (0 : ℝ)..t, Pd r * r ^ 2)
        - 2 * ∫ r in (0 : ℝ)..t, r * Pd r ^ 2 := by
  have hP := hasSum_ptm ht htc
  have hI2 := hasSum_int_Pd_mul_pow ht.le (hth htc) 2
  have hsq := hasSum_int_Pd_sq ht.le (hth htc)
  have hsum := ((hP.mul_left 2).sub (hI2.mul_left (2 * Real.pi))).sub (hsq.mul_left 2)
  rw [← hsum.tsum_eq]
  rw [tsum_succ_of_zero (by simp [D_zero_inner htc])]
  refine tsum_congr fun m => ?_
  have hk : (k (m + 1) : ℝ) = (pk m : ℝ) := by rw [k_of_pos (Nat.succ_pos m)]; rfl
  have hkn : k (m + 1) = pk m := k_of_pos (Nat.succ_pos m)
  have hpk : (pk m : ℝ) + 2 ≠ 0 := by have := pk_pos m; positivity
  have htp : t ^ pk m ≠ 0 := pow_ne_zero _ ht.ne'
  rw [hk, D_succ_of_le htc, H, hkn, Ik_eq ht htc m, ptm_eq]
  simp only [Nat.cast_ofNat]
  field_simp
  ring

theorem inner_T3 {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) :
    ∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ))
          * D ij.1 t * D ij.2 t = ∫ r in (0 : ℝ)..t, r * Pd r ^ 2 := by
  have hsq := hasSum_int_Pd_sq ht.le (hth htc)
  let W : ℕ × ℕ → ℝ := fun mn => pa mn.1 * (pk mn.1 : ℝ) *
    (pa mn.2 * (pk mn.2 : ℝ) * t ^ (pk mn.2 + pk mn.1) / ((pk mn.2 : ℝ) + (pk mn.1 : ℝ)))
  have hW : ∀ mn : ℕ × ℕ, (k (mn.1 + 1) : ℝ) * (k (mn.2 + 1) : ℝ)
      / ((k (mn.1 + 1) : ℝ) + (k (mn.2 + 1) : ℝ)) * D (mn.1 + 1) t * D (mn.2 + 1) t = W mn := by
    intro mn
    have hk1 : (k (mn.1 + 1) : ℝ) = (pk mn.1 : ℝ) := by rw [k_of_pos (Nat.succ_pos _)]; rfl
    have hk2 : (k (mn.2 + 1) : ℝ) = (pk mn.2 : ℝ) := by rw [k_of_pos (Nat.succ_pos _)]; rfl
    have h1 := pk_pos mn.1
    have h2 := pk_pos mn.2
    have hpos : (0 : ℝ) < (pk mn.2 : ℝ) + (pk mn.1 : ℝ) := by positivity
    have hpos' : (0 : ℝ) < (pk mn.1 : ℝ) + (pk mn.2 : ℝ) := by positivity
    simp only [W]
    rw [hk1, hk2, D_succ_of_le htc, D_succ_of_le htc, ptm_eq, ptm_eq, pow_add]
    field_simp
    ring
  -- summability on `ℕ × ℕ`
  have hG : Summable fun m => |pa m| * (pk m : ℝ) * t ^ pk m := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (summable_N₁.mul_left ((1 / 2 : ℝ) ^ 6))
    have h := abs_dptm_le_Icc (m := m) (r := t) ⟨ht.le, hth htc⟩
    have h2 : |pa m| * (pk m : ℝ) * t ^ pk m = t * |dptm m t| := by
      rw [← abs_of_pos ht, ← abs_mul, abs_of_pos ht, mul_dptm, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (pk m : ℝ)),
        abs_of_nonneg (pow_nonneg ht.le _)]
    rw [h2]
    calc t * |dptm m t| ≤ t * (t ^ 5 * N₁ m) := mul_le_mul_of_nonneg_left h ht.le
      _ = t ^ 6 * N₁ m := by ring
      _ ≤ (1 / 2 : ℝ) ^ 6 * N₁ m :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le (hth htc) 6) (N₁_nonneg m)
  have hsumW : Summable W := by
    have hprod := Summable.mul_of_nonneg hG hG (fun m => by positivity) (fun m => by positivity)
    refine Summable.of_norm_bounded hprod (fun mn => ?_)
    rw [Real.norm_eq_abs]
    have h1 := pk_pos mn.1
    have h2 := pk_pos mn.2
    have hpos : (0 : ℝ) < (pk mn.2 : ℝ) + (pk mn.1 : ℝ) := by positivity
    have hone : (1 : ℝ) ≤ (pk mn.2 : ℝ) + (pk mn.1 : ℝ) := by
      have : 1 ≤ pk mn.2 + pk mn.1 := by omega
      exact_mod_cast this
    simp only [W]
    have e1 : pa mn.1 * (pk mn.1 : ℝ) * (pa mn.2 * (pk mn.2 : ℝ) * t ^ (pk mn.2 + pk mn.1)
        / ((pk mn.2 : ℝ) + (pk mn.1 : ℝ)))
        = (pa mn.1 * (pk mn.1 : ℝ) * t ^ pk mn.1) * (pa mn.2 * (pk mn.2 : ℝ) * t ^ pk mn.2)
          / ((pk mn.2 : ℝ) + (pk mn.1 : ℝ)) := by
      rw [pow_add]; ring
    rw [e1, abs_div, abs_of_pos hpos, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (pk mn.1 : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (pk mn.2 : ℝ)),
      abs_of_nonneg (pow_nonneg ht.le (pk mn.1)), abs_of_nonneg (pow_nonneg ht.le (pk mn.2))]
    rw [div_le_iff₀ hpos]
    have hnn : 0 ≤ |pa mn.1| * (pk mn.1 : ℝ) * t ^ pk mn.1 * (|pa mn.2| * (pk mn.2 : ℝ) * t ^ pk mn.2) :=
      by positivity
    nlinarith [hnn]
  have hfib : ∀ m, HasSum (fun n => W (m, n)) (pa m * (pk m : ℝ) * ∫ r in (0 : ℝ)..t, Pd r * r ^ pk m) :=
    fun m => (hasSum_int_Pd_mul_pow ht.le (hth htc) (pk m)).mul_left (pa m * (pk m : ℝ))
  rw [tsum_succ_prod_of_zero (fun ij hij => by
    rcases hij with h | h
    · simp [h, D_zero_inner htc]
    · simp [h, D_zero_inner htc])]
  rw [tsum_congr hW]
  rw [hsumW.tsum_prod' (fun m => (hfib m).summable)]
  rw [← hsq.tsum_eq]
  exact tsum_congr fun m => (hfib m).tsum_eq

/-- **`comp:inner-exact`**: for `0 < t ≤ p - c` (`c = .06`),
`f₀(t) = (π t² - 1/2) log t - 3 π² t⁴/8` and `e(t) = 0`. -/
theorem inner_exact {t : ℝ} (ht : 0 < t) (htc : t ≤ p - c) :
    f₀ t = (Real.pi * t ^ 2 - 1 / 2) * Real.log t - 3 * Real.pi ^ 2 * t ^ 4 / 8 ∧ e t = 0 := by
  refine ⟨?_, e_inner ⟨ht, htc⟩⟩
  unfold f₀
  rw [S₁_inner ht htc, S₂_inner ht htc, inner_T2 ht htc, inner_T3 ht htc]
  have h1 := inner_T1 ht htc
  have h2 := int_Pd_zero ht htc
  rw [mul_add, h1]
  ring

end Assembly

end Calibration
