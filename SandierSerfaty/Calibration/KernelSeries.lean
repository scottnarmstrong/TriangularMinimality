/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.FirstOrderRegularity
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Radial integration of series, and the positive kernel `e ≥ 0` (`cal:positive-kernel`)

The scale-free radial integrals of the angle-density computation:

* `integral_sq_series`: for `∑ |q_i| < ∞`,
  `∫₀¹ (∑ q_i v^{k_i})² dv/v = ∑_{i,j} q_i q_j/(k_i + k_j)` (all `k_i ≥ 6`), the double family being summable;
* `integral_series_mul`: `∫₀¹ (∑ q_i v^{k_i}) dv/v = ∑ q_i/k_i` and `∫₀¹ (∑ q_i v^{k_i}) v dv = ∑ q_i/(k_i + 2)`
  (the two linear integrals);
* `summable_abs_Q`: `∑ |Q_i(t)| < ∞` for `t > 0`.
-/

open Set MeasureTheory intervalIntegral

public section

namespace SandierSerfaty

namespace Calibration

theorem k_ge_one (i : ℕ) : 1 ≤ k i := (by norm_num : 1 ≤ 6).trans (six_le_k i)

theorem k_real_pos (i : ℕ) : (0 : ℝ) < k i := by exact_mod_cast k_pos i

/-- `∫₀¹ v^n dv/v = 1/n` for `n ≥ 1`, in the integrable form `v^(n-1)`. -/
theorem integral_pow_pred {n : ℕ} (hn : 1 ≤ n) :
    ∫ v in (0 : ℝ)..1, v ^ (n - 1) = 1 / (n : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [integral_pow]

theorem integral_pow_pred_Ioc {n : ℕ} (hn : 1 ≤ n) :
    ∫ v in Ioc (0 : ℝ) 1, v ^ (n - 1) = 1 / (n : ℝ) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]; exact integral_pow_pred hn

theorem summable_norm_mul_pow {q : ℕ → ℝ} (hq : Summable fun i => |q i|) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Summable fun i => ‖q i * v ^ k i‖ := by
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hq
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hv0 hv1)

theorem integral_sq_series {q : ℕ → ℝ} (hq : Summable fun i => |q i|) :
    ∫ v in (0 : ℝ)..1, (∑' i, q i * v ^ k i) ^ 2 / v =
      ∑' ij : ℕ × ℕ, q ij.1 * q ij.2 / ((k ij.1 : ℝ) + k ij.2) := by
  set F : ℕ × ℕ → ℝ → ℝ := fun ij v => q ij.1 * q ij.2 * v ^ (k ij.1 + k ij.2 - 1) with hF
  have hFint : ∀ ij, Integrable (F ij) (volume.restrict (Ioc (0 : ℝ) 1)) := fun ij => by
    refine (Continuous.integrableOn_Ioc ?_)
    exact continuous_const.mul (continuous_pow _)
  have hn1 : ∀ ij : ℕ × ℕ, 1 ≤ k ij.1 + k ij.2 := fun ij => by have := k_ge_one ij.1; omega
  have hFi : ∀ ij : ℕ × ℕ, ∫ v in Ioc (0 : ℝ) 1, F ij v = q ij.1 * q ij.2 / ((k ij.1 : ℝ) + k ij.2) := by
    intro ij
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, integral_pow_pred_Ioc (hn1 ij)]
    push_cast
    ring
  have hFn : ∀ ij : ℕ × ℕ, ∫ v in Ioc (0 : ℝ) 1, ‖F ij v‖ = |q ij.1 * q ij.2| / ((k ij.1 : ℝ) + k ij.2) := by
    intro ij
    have : ∀ v ∈ Ioc (0 : ℝ) 1, ‖F ij v‖ = |q ij.1 * q ij.2| * v ^ (k ij.1 + k ij.2 - 1) := by
      intro v hv
      simp only [hF]
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hv.1]
    rw [setIntegral_congr_fun measurableSet_Ioc this, MeasureTheory.integral_const_mul, integral_pow_pred_Ioc (hn1 ij)]
    push_cast
    ring
  have hsumN : Summable fun ij : ℕ × ℕ => ∫ v in Ioc (0 : ℝ) 1, ‖F ij v‖ := by
    simp_rw [hFn]
    have h := Summable.mul_norm (f := q) (g := q) (by simpa using hq) (by simpa using hq)
    refine Summable.of_nonneg_of_le (fun ij => by have := k_real_pos ij.1; have := k_real_pos ij.2; positivity)
      (fun ij => ?_) h
    have h1 : (1 : ℝ) ≤ (k ij.1 : ℝ) + k ij.2 := by
      have : (1 : ℝ) ≤ k ij.1 := by exact_mod_cast k_ge_one ij.1
      have := k_real_pos ij.2; linarith
    exact div_le_self (abs_nonneg _) h1
  have hS := hasSum_integral_of_summable_integral_norm hFint hsumN
  have hpt : ∀ v ∈ Ioc (0 : ℝ) 1, (∑' i, q i * v ^ k i) ^ 2 / v = ∑' ij, F ij v := by
    intro v hv
    have hs := summable_norm_mul_pow hq hv.1.le hv.2
    rw [sq, tsum_mul_tsum_of_summable_norm hs hs, ← tsum_div_const]
    refine tsum_congr fun ij => ?_
    simp only [hF]
    have hk : k ij.1 + k ij.2 = (k ij.1 + k ij.2 - 1) + 1 := by have := hn1 ij; omega
    have hv0 : v ≠ 0 := hv.1.ne'
    have hpw : v ^ k ij.1 * v ^ k ij.2 = v ^ (k ij.1 + k ij.2 - 1) * v := by
      rw [← pow_add, ← pow_succ, ← hk]
    calc q ij.1 * v ^ k ij.1 * (q ij.2 * v ^ k ij.2) / v
        = q ij.1 * q ij.2 * (v ^ k ij.1 * v ^ k ij.2) / v := by ring
      _ = _ := by rw [hpw]; field_simp
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_fun measurableSet_Ioc hpt]
  rw [← hS.tsum_eq]
  exact tsum_congr hFi

/-- The linear radial integrals of the series: `∫₀¹ (∑ q_i v^{k_i}) dv/v = ∑ q_i / k_i`. -/
theorem integral_series_inv {q : ℕ → ℝ} (hq : Summable fun i => |q i|) :
    ∫ v in (0 : ℝ)..1, (∑' i, q i * v ^ k i) / v = ∑' i, q i / (k i : ℝ) := by
  set F : ℕ → ℝ → ℝ := fun i v => q i * v ^ (k i - 1) with hF
  have hFint : ∀ i, Integrable (F i) (volume.restrict (Ioc (0 : ℝ) 1)) := fun i =>
    (Continuous.integrableOn_Ioc (continuous_const.mul (continuous_pow _)))
  have hFi : ∀ i, ∫ v in Ioc (0 : ℝ) 1, F i v = q i / (k i : ℝ) := fun i => by
    simp only [hF]; rw [MeasureTheory.integral_const_mul, integral_pow_pred_Ioc (k_ge_one i)]; ring
  have hFn : ∀ i, ∫ v in Ioc (0 : ℝ) 1, ‖F i v‖ = |q i| / (k i : ℝ) := fun i => by
    have : ∀ v ∈ Ioc (0 : ℝ) 1, ‖F i v‖ = |q i| * v ^ (k i - 1) := by
      intro v hv
      simp only [hF]
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hv.1]
    rw [setIntegral_congr_fun measurableSet_Ioc this, MeasureTheory.integral_const_mul, integral_pow_pred_Ioc (k_ge_one i)]
    ring
  have hsumN : Summable fun i => ∫ v in Ioc (0 : ℝ) 1, ‖F i v‖ := by
    simp_rw [hFn]
    refine Summable.of_nonneg_of_le (fun i => by have := k_real_pos i; positivity) (fun i => ?_) hq
    have : (1 : ℝ) ≤ k i := by exact_mod_cast k_ge_one i
    exact div_le_self (abs_nonneg _) this
  have hS := hasSum_integral_of_summable_integral_norm hFint hsumN
  have hpt : ∀ v ∈ Ioc (0 : ℝ) 1, (∑' i, q i * v ^ k i) / v = ∑' i, F i v := by
    intro v hv
    rw [← tsum_div_const]
    refine tsum_congr fun i => ?_
    simp only [hF]
    have hk : k i = (k i - 1) + 1 := by have := k_ge_one i; omega
    have hv0 : v ≠ 0 := hv.1.ne'
    have hpw : v ^ k i = v ^ (k i - 1) * v := by rw [← pow_succ, ← hk]
    rw [hpw]; field_simp
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_fun measurableSet_Ioc hpt,
    ← hS.tsum_eq]
  exact tsum_congr hFi

/-- `|Q_i(t)| ≤ (t + k_i) M_i`: the family `Q_i(t)` is absolutely summable for `t > 0`. -/
theorem summable_abs_Q {t : ℝ} (ht : 0 < t) : Summable fun i => |Q i t| := by
  obtain ⟨M, hM0, hMs, hMb⟩ := exists_D_majorant ht
  refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_) (summable_W hMs t)
  obtain ⟨b0, b1, -⟩ := hMb i t le_rfl
  have hk : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
  unfold Q
  calc |t * deriv (D i) t - (k i : ℝ) * D i t| ≤ |t * deriv (D i) t| + |(k i : ℝ) * D i t| := abs_sub _ _
    _ ≤ t * M i + (k i) * M i := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_pos ht]; exact mul_le_mul_of_nonneg_left b1 ht.le
        · rw [abs_mul, abs_of_nonneg hk]; exact mul_le_mul_of_nonneg_left b0 hk
    _ ≤ (1 + t + (k i : ℝ)) * M i := by nlinarith [hM0 i]

end Calibration

end SandierSerfaty

end
