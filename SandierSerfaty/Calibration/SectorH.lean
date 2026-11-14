/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorInt

/-!
# Bounds on `H_k` and its derivatives, uniform in `k`

For `0 < d ≤ t ≤ T` and every exponent `n` (paper `cal:radial-integrals`): `|H_n(t)| ≤ A`, `|H_n'(t)| ≤ A (1 + n)`,
`|H_n''(t)| ≤ A (1 + n)²`, with `A` independent of `n` (`exists_H_bound`). These feed the termwise
differentiation of `∑_i D_i (-2 + 2 k_i H_{k_i})` in `f₀` (`SectorSeries.lean`).

Proof: `|I_n(t)| ≤ C t^{n+1}/(n+1)` for `C ≥ sup_{(0,T]} |B₁|`; `H_n' = B₁ - (n/t) H_n`;
`H_n'' = B₁' + (n/t²) H_n - (n/t) H_n'`.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

theorem abs_Ik_le (n : ℕ) {T C : ℝ} (hC : ∀ r ∈ Ioc 0 T, |B₁ r| ≤ C) {t : ℝ} (ht : t ∈ Ioc 0 T) :
    |Ik n t| ≤ C * (t ^ (n + 1) / (n + 1)) := by
  have hint : IntervalIntegrable (fun r : ℝ => C * r ^ n) volume 0 t :=
    (continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := t)
    (f := fun r => B₁ r * r ^ n) (g := fun r => C * r ^ n) ht.1.le
    (Filter.Eventually.of_forall fun r hr => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr.1]
      exact mul_le_mul_of_nonneg_right (hC r ⟨hr.1, hr.2.trans ht.2⟩) (pow_nonneg hr.1.le _)) hint
  rw [intervalIntegral.integral_const_mul, integral_pow] at h
  simpa [Ik, Real.norm_eq_abs] using h

theorem abs_H_le (n : ℕ) {T C : ℝ} (hC : ∀ r ∈ Ioc 0 T, |B₁ r| ≤ C) (hC0 : 0 ≤ C) {t : ℝ}
    (ht : t ∈ Ioc 0 T) : |H n t| ≤ C * T := by
  have h := abs_Ik_le n hC ht
  have htp := ht.1
  have hp : 0 < t ^ n := pow_pos htp n
  unfold H
  rw [abs_mul, abs_inv, abs_of_pos hp]
  have e : (t ^ n)⁻¹ * (C * (t ^ (n + 1) / (n + 1))) = C * t / (n + 1) := by
    rw [pow_succ]; field_simp
  calc (t ^ n)⁻¹ * |Ik n t| ≤ (t ^ n)⁻¹ * (C * (t ^ (n + 1) / (n + 1))) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 hp.le)
    _ = C * t / (n + 1) := e
    _ ≤ C * t := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 ≤ C * t := by positivity
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
    _ ≤ C * T := mul_le_mul_of_nonneg_left ht.2 hC0

/-- The derivative of `H_n` on `(0, ∞)` as a function. -/
theorem deriv_H (n : ℕ) {t : ℝ} (ht : 0 < t) : deriv (H n) t = B₁ t - n / t * H n t :=
  (hasDerivAt_H n ht).deriv

theorem hasDerivAt_deriv_H (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (H n)) (deriv B₁ t - (-(n : ℝ) / t ^ 2 * H n t + n / t * deriv (H n) t)) t := by
  have hB : HasDerivAt B₁ (deriv B₁ t) t :=
    (((contDiffOn_B₁.differentiableOn one_ne_zero) t ht).differentiableAt
      (Ioi_mem_nhds ht)).hasDerivAt
  have hinv : HasDerivAt (fun s : ℝ => (n : ℝ) / s) (-(n : ℝ) / t ^ 2) t := by
    have := (hasDerivAt_inv ht.ne').const_mul (n : ℝ)
    refine this.congr_deriv ?_ |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · field_simp
    · simp [div_eq_mul_inv]
  have h2 := hinv.mul (hasDerivAt_H n ht)
  have h3 := hB.sub (hinv.mul (hasDerivAt_H n ht).differentiableAt.hasDerivAt)
  have e : deriv (H n) =ᶠ[nhds t] fun s => B₁ s - n / s * H n s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using deriv_H n hs
  refine (h3.congr_deriv ?_).congr_of_eventuallyEq e
  rw [deriv_H n ht]

theorem deriv_deriv_H (n : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (H n)) t = deriv B₁ t - (-(n : ℝ) / t ^ 2 * H n t + n / t * deriv (H n) t) :=
  (hasDerivAt_deriv_H n ht).deriv

/-- `|H_n| ≤ A`, `|H_n'| ≤ A(1+n)`, `|H_n''| ≤ A(1+n)²` on `[d, T]`, uniformly in `n`. -/
theorem exists_H_bound {d T : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ∀ t ∈ Icc d T, |H n t| ≤ A ∧ |deriv (H n) t| ≤ A * (1 + n) ∧
      |deriv (deriv (H n)) t| ≤ A * (1 + n) ^ 2 := by
  obtain ⟨Cb, hCb0, hCb⟩ := exists_B₁_bound T
  have hsub : Icc d T ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hd ht.1
  obtain ⟨C₂, h₂⟩ := (isCompact_Icc (a := d) (b := T)).exists_bound_of_continuousOn
    (continuousOn_deriv_B₁.mono hsub)
  set q : ℝ := 1 / d with hq
  have hq0 : 0 ≤ q := by positivity
  set a0 : ℝ := Cb * T with ha0
  set a1 : ℝ := Cb + q * a0 with ha1
  set a2 : ℝ := |C₂| + q * a1 + q ^ 2 * a0 with ha2
  by_cases hT : T ≤ 0
  · refine ⟨0, le_rfl, fun n t ht => absurd (ht.1.trans ht.2) (by linarith)⟩
  push Not at hT
  have ha00 : 0 ≤ a0 := by positivity
  have ha10 : 0 ≤ a1 := by positivity
  have ha20 : 0 ≤ a2 := by positivity
  refine ⟨a0 + a1 + a2, by positivity, fun n t ht => ?_⟩
  have htp : 0 < t := lt_of_lt_of_le hd ht.1
  have htT : t ∈ Ioc 0 T := ⟨htp, ht.2⟩
  have hx : 1 / t ≤ q := by
    rw [hq]; exact one_div_le_one_div_of_le hd ht.1
  have hx0 : 0 ≤ 1 / t := by positivity
  have hK : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hH := abs_H_le n hCb hCb0 htT
  have hB := hCb t htT
  -- first derivative
  have hd1 : |deriv (H n) t| ≤ a1 * (1 + n) := by
    rw [deriv_H n htp]
    have e : (n : ℝ) / t * H n t = n * (1 / t) * H n t := by ring
    calc |B₁ t - n / t * H n t| ≤ |B₁ t| + |n / t * H n t| := abs_sub _ _
      _ ≤ Cb + n * q * a0 := by
          refine add_le_add hB ?_
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / t)]
          have : (n : ℝ) / t = n * (1 / t) := by ring
          rw [this]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hx hK) hH (abs_nonneg _) (by positivity)
      _ ≤ a1 * (1 + n) := by
          rw [ha1]; nlinarith [mul_nonneg hK (mul_nonneg hq0 ha00), mul_nonneg hK hCb0,
            mul_nonneg hq0 ha00]
  -- second derivative
  have hd2 : |deriv (deriv (H n)) t| ≤ a2 * (1 + n) ^ 2 := by
    rw [deriv_deriv_H n htp]
    have hB' : |deriv B₁ t| ≤ |C₂| := by
      have := h₂ t ht; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
    have e1 : |(-(n : ℝ) / t ^ 2) * H n t| ≤ n * q ^ 2 * a0 := by
      rw [abs_mul, abs_div, abs_neg, Nat.abs_cast, abs_of_pos (pow_pos htp 2)]
      have : (n : ℝ) / t ^ 2 = n * (1 / t) ^ 2 := by field_simp
      rw [this]
      have hx2 : (1 / t) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hx0 hx 2
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx2 hK) hH (abs_nonneg _) (by positivity)
    have e2 : |(n : ℝ) / t * deriv (H n) t| ≤ n * q * (a1 * (1 + n)) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / t)]
      have : (n : ℝ) / t = n * (1 / t) := by ring
      rw [this]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hx hK) hd1 (abs_nonneg _) (by positivity)
    calc |deriv B₁ t - (-(n : ℝ) / t ^ 2 * H n t + n / t * deriv (H n) t)|
        ≤ |deriv B₁ t| + (|(-(n : ℝ) / t ^ 2) * H n t| + |(n : ℝ) / t * deriv (H n) t|) :=
          (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _ |>.trans' le_rfl)
      _ ≤ |C₂| + (n * q ^ 2 * a0 + n * q * (a1 * (1 + n))) := by
          gcongr
      _ ≤ a2 * (1 + n) ^ 2 := by
          rw [ha2]
          have h1 : 0 ≤ n * q ^ 2 * a0 := by positivity
          have h2 : 0 ≤ n * q * a1 := by positivity
          nlinarith [mul_nonneg h1 hK, mul_nonneg h2 hK, mul_nonneg (abs_nonneg C₂) hK,
            mul_nonneg (abs_nonneg C₂) (mul_nonneg hK hK), mul_nonneg h1 (mul_nonneg hK hK),
            mul_nonneg h2 (mul_nonneg hK hK), mul_nonneg (mul_nonneg hq0 ha10) hK,
            mul_nonneg (mul_nonneg hq0 ha10) (mul_nonneg hK hK),
            mul_nonneg (pow_nonneg hq0 2) (mul_nonneg ha00 hK),
            mul_nonneg (pow_nonneg hq0 2) (mul_nonneg ha00 (mul_nonneg hK hK))]
  have hn1 : (1 : ℝ) ≤ 1 + n := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc |H n t| ≤ a0 := hH
      _ ≤ a0 + a1 + a2 := by linarith
  · calc |deriv (H n) t| ≤ a1 * (1 + n) := hd1
      _ ≤ (a0 + a1 + a2) * (1 + n) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  · calc |deriv (deriv (H n)) t| ≤ a2 * (1 + n) ^ 2 := hd2
      _ ≤ (a0 + a1 + a2) * (1 + n) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Calibration

end SandierSerfaty

end
