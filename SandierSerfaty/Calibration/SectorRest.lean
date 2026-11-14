/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorSer

/-!
# The radial integral of the non-singular part of the gradient energy

Paper, verification of `cal:angle-density`. Along a ray at angle `φ` (`t = d sec φ`, `τ = tan²φ`), with
`ΣA(r) = ∑ kᵢ cᵢ (r/t)^{kᵢ}` (`cᵢ = Dᵢ(t)`) and `ΣQ(r) = ∑ qᵢ (r/t)^{kᵢ}` (`qᵢ = Qᵢ(t)`), the part of
`r |∇H|²` other than the singular `r B'(r)²` is `2 B'(r) ΣA(r) + ΣA(r)²/r + τ ΣQ(r)²/r`, and

`∫₀ᵗ (2 B' ΣA + ΣA²/r + τ ΣQ²/r) dr
   = ∑ (-2 cᵢ + 2 kᵢ cᵢ H_{kᵢ}(t)) + ∑_{i,j} kᵢkⱼ/(kᵢ+kⱼ) cᵢ cⱼ + τ ∑_{i,j} qᵢ qⱼ/(kᵢ+kⱼ)`
(`integral_rest_inner`), the three series being exactly those of `f₀(t)` and `2 e(t)` (`cal:f0-e`).
-/

open Set MeasureTheory intervalIntegral

public section

namespace SandierSerfaty

namespace Calibration

theorem summable_abs_div_k {a : ℕ → ℝ} (ha : Summable fun i => |a i|) :
    Summable fun i => |a i / (k i : ℝ)| := by
  refine Summable.of_nonneg_of_le (fun i => abs_nonneg _) (fun i => ?_) ha
  rw [abs_div, Nat.abs_cast]
  have : (1 : ℝ) ≤ k i := by exact_mod_cast k_ge_one i
  exact div_le_self (abs_nonneg _) this

theorem integral_rest_inner {t : ℝ} (ht : 0 < t) {c q : ℕ → ℝ}
    (hc : Summable fun i => |(k i : ℝ) * c i|) (hq : Summable fun i => |q i|) (τ : ℝ) :
    ∫ r in (0 : ℝ)..t, (2 * deriv B r * ser (fun i => (k i : ℝ) * c i) t r +
        ser (fun i => (k i : ℝ) * c i) t r ^ 2 / r + τ * (ser q t r ^ 2 / r)) =
      (∑' i, (-2 * c i + 2 * (k i : ℝ) * c i * H (k i) t)) +
        (∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * c ij.1 * c ij.2) +
        τ * ∑' ij : ℕ × ℕ, q ij.1 * q ij.2 / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) := by
  set a : ℕ → ℝ := fun i => (k i : ℝ) * c i with ha
  have I1 := (intervalIntegrable_B₁_ser hc ht).const_mul 2
  have I2 := (intervalIntegrable_ser_div hc ht).const_mul 2
  have I3 := intervalIntegrable_ser_sq_div hc ht
  have I4 := (intervalIntegrable_ser_sq_div hq ht).const_mul τ
  have hpt : ∫ r in (0 : ℝ)..t, (2 * deriv B r * ser a t r + ser a t r ^ 2 / r + τ * (ser q t r ^ 2 / r)) =
      ∫ r in (0 : ℝ)..t, (2 * (B₁ r * ser a t r) - 2 * (ser a t r / r) + ser a t r ^ 2 / r +
        τ * (ser q t r ^ 2 / r)) := by
    rw [intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hr0 : 0 < r := hr.1
    unfold B₁
    field_simp
    ring
  rw [hpt, intervalIntegral.integral_add ((I1.sub I2).add I3) I4,
    intervalIntegral.integral_add (I1.sub I2) I3, intervalIntegral.integral_sub I1 I2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h1 : ∫ r in (0 : ℝ)..t, B₁ r * ser a t r = ∑' i, a i * H (k i) t := integral_B₁_series ht hc
  have h2 : ∫ r in (0 : ℝ)..t, ser a t r / r = ∑' i, a i / (k i : ℝ) := integral_series_div ht hc
  have h3 : ∫ r in (0 : ℝ)..t, ser a t r ^ 2 / r =
      ∑' ij : ℕ × ℕ, a ij.1 * a ij.2 / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) := integral_sq_series_div ht hc
  have h4 : ∫ r in (0 : ℝ)..t, ser q t r ^ 2 / r =
      ∑' ij : ℕ × ℕ, q ij.1 * q ij.2 / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) := integral_sq_series_div ht hq
  rw [h1, h2, h3, h4]
  -- recombine the series
  obtain ⟨C, hC0, hC⟩ := exists_B₁_bound t
  have hHb : ∀ n : ℕ, |H n t| ≤ C * t := fun n => abs_H_le n hC hC0 ⟨ht, le_rfl⟩
  have hs1 : Summable fun i => a i * H (k i) t := by
    refine Summable.of_norm_bounded (hc.mul_right (C * t)) fun i => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hHb _) (abs_nonneg _)
  have hs2 : Summable fun i => a i / (k i : ℝ) := Summable.of_norm_bounded (summable_abs_div_k hc)
    fun i => by rw [Real.norm_eq_abs]
  have e1 : ∑' i, (-2 * c i + 2 * (k i : ℝ) * c i * H (k i) t) =
      2 * ∑' i, a i * H (k i) t - 2 * ∑' i, a i / (k i : ℝ) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← hs1.mul_left 2 |>.tsum_sub (hs2.mul_left 2)]
    refine tsum_congr fun i => ?_
    have hk : (k i : ℝ) ≠ 0 := (k_real_pos i).ne'
    simp only [ha]
    field_simp
    ring
  have e2 : ∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * c ij.1 * c ij.2 =
      ∑' ij : ℕ × ℕ, a ij.1 * a ij.2 / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) :=
    tsum_congr fun ij => by simp only [ha]; ring
  rw [e1, e2]

end Calibration

end SandierSerfaty

end
