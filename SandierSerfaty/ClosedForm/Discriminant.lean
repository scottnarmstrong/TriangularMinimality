/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.PeriodBeta

/-!
# `|Δ(ρ)|` in closed form

The closed-form note's Theorem C: for `ρ = e^{iπ/3}` and Mathlib's `ModularForm.discriminant`
(`Δ = η²⁴`),

`|Δ(ρ)| = 3³ Γ(1/3)³⁶ / (2²⁴ π²⁴)`,

equivalently `|η(ρ)| = 3^(1/8) Γ(1/3)^(3/2) / (2π)`.

The proof combines `Δ(ρ) = -E₆(ρ)²/1728` and `g₃ = (8π⁶/27) E₆(ρ)` (`Eisenstein.lean`), `4 e³ = g₃`
(`WeierstrassHex.lean`), `B(1/6, 1/2) = 3 √e` (`PeriodBeta.lean`) and
`B(1/6, 1/2) = 3 Γ(1/3)³/(2^(4/3) π)` (`GammaThird.lean`).
-/

open Complex

public section

namespace SandierSerfaty

namespace ClosedForm

/-- `√e = Γ(1/3)³ / (2^(4/3) π)`, from the two evaluations of `B(1/6, 1/2)`. -/
theorem sqrt_hexE_eq :
    √hexE = Real.Gamma (1 / 3) ^ 3 / ((2 : ℝ) ^ (4 / 3 : ℝ) * Real.pi) := by
  have h := betaReal_one_sixth_one_half_eq.symm.trans betaReal_one_sixth_one_half
  have hd : 0 < (2 : ℝ) ^ (4 / 3 : ℝ) * Real.pi := by positivity
  rw [eq_div_iff hd.ne']
  rw [eq_div_iff hd.ne'] at h
  linarith

theorem rpow_four_thirds_pow_twelve : ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 12 = 65536 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show (4 / 3 : ℝ) * ((12 : ℕ) : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- `E₆(ρ)` as a real number: `E₆(ρ) = 27 g₃/(8 π⁶)`. -/
theorem E₆_rhoH_eq_real :
    ModularForm.E₆ rhoH = ((27 * hexG3 / (8 * Real.pi ^ 6) : ℝ) : ℂ) := by
  have h := hexPair_g₃
  rw [hexPair_g₃_eq] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := pi_ne_zero_complex
  push_cast
  field_simp
  linear_combination -27 * h

/-- Theorem C: `|Δ(ρ)| = 3³ Γ(1/3)³⁶ / (2²⁴ π²⁴)`. -/
theorem norm_discriminant_rhoH :
    ‖ModularForm.discriminant rhoH‖ = 3 ^ 3 * Real.Gamma (1 / 3) ^ 36 / (2 ^ 24 * Real.pi ^ 24) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hE := hexE_pos
  have hG : hexG3 = 4 * hexE ^ 3 := four_mul_hexE_cube_real.symm
  have hd : 0 < (2 : ℝ) ^ (4 / 3 : ℝ) := by positivity
  set s := √hexE with hs
  have hes : hexE = s ^ 2 := (Real.sq_sqrt hE.le).symm
  have hpos : 0 < 27 * hexG3 / (8 * Real.pi ^ 6) := by
    have := hexG3_pos; positivity
  rw [discriminant_rhoH, E₆_rhoH_eq_real, norm_div, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hpos.le]
  have h1728 : ‖(1728 : ℂ)‖ = 1728 := by simp
  rw [h1728, hG, hes]
  have hs' : s = Real.Gamma (1 / 3) ^ 3 / ((2 : ℝ) ^ (4 / 3 : ℝ) * Real.pi) := sqrt_hexE_eq
  have hs12 : s ^ 12 = Real.Gamma (1 / 3) ^ 36 / (65536 * Real.pi ^ 12) := by
    rw [hs', div_pow, mul_pow, ← pow_mul, mul_comm 3 12, pow_mul, rpow_four_thirds_pow_twelve]
  have : (27 * (4 * (s ^ 2) ^ 3) / (8 * Real.pi ^ 6)) ^ 2 / 1728 =
      729 * s ^ 12 / (6912 * Real.pi ^ 12) := by
    field_simp
    ring
  rw [this, hs12]
  field_simp
  ring

/-- Theorem C, `η` form: `|η(ρ)| = 3^(1/8) Γ(1/3)^(3/2) / (2π)`. -/
theorem norm_eta_rho :
    ‖ModularForm.eta rho‖ =
      (3 : ℝ) ^ (1 / 8 : ℝ) * Real.Gamma (1 / 3) ^ (3 / 2 : ℝ) / (2 * Real.pi) := by
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h24 : ‖ModularForm.eta rho‖ ^ 24 = ‖ModularForm.discriminant rhoH‖ := by
    rw [← norm_pow]; rfl
  rw [norm_discriminant_rhoH] at h24
  have h3 : ((3 : ℝ) ^ (1 / 8 : ℝ)) ^ 24 = 3 ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (1 / 8 : ℝ) * ((24 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hg : (Real.Gamma (1 / 3) ^ (3 / 2 : ℝ)) ^ 24 = Real.Gamma (1 / 3) ^ 36 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG.le,
      show (3 / 2 : ℝ) * ((24 : ℕ) : ℝ) = ((36 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hr : ((3 : ℝ) ^ (1 / 8 : ℝ) * Real.Gamma (1 / 3) ^ (3 / 2 : ℝ) / (2 * Real.pi)) ^ 24 =
      3 ^ 3 * Real.Gamma (1 / 3) ^ 36 / (2 ^ 24 * Real.pi ^ 24) := by
    rw [div_pow, mul_pow, mul_pow, h3, hg]
  have hnn : 0 ≤ (3 : ℝ) ^ (1 / 8 : ℝ) * Real.Gamma (1 / 3) ^ (3 / 2 : ℝ) / (2 * Real.pi) := by
    positivity
  exact (pow_left_inj₀ (norm_nonneg _) hnn (by norm_num : (24 : ℕ) ≠ 0)).1 (h24.trans hr.symm)

end ClosedForm

end SandierSerfaty
