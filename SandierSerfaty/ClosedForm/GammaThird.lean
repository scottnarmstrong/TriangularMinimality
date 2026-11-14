/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Beta integral `B(1/6, 1/2)` in terms of `Γ(1/3)`

`betaReal a c = ∫_{(0,1)} x^(a-1) (1-x)^(c-1) dx` is the real Beta integral. For `0 < a, c` it satisfies
`Γ(a) Γ(c) = Γ(a + c) B(a, c)` (from Mathlib's complex `Complex.Gamma_mul_Gamma_eq_betaIntegral`). We prove

`betaReal (1/6) (1/2) = 3 Γ(1/3)³ / (2^(4/3) π)`

(`betaReal_one_sixth_one_half`; the closed-form note's Lemma C7), from the Beta–Gamma relation, `Γ(1/2) = √π`,
the duplication formula at `1/6` and Euler's reflection formula at `1/3`.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace ClosedForm

/-- The real Beta integral `∫_{(0,1)} x^(a-1) (1-x)^(c-1) dx`. -/
@[expose] noncomputable def betaReal (a c : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, x ^ (a - 1) * (1 - x) ^ (c - 1)

/-- Mathlib's complex Beta integral at real arguments is the real Beta integral. -/
theorem betaIntegral_ofReal (a c : ℝ) :
    Complex.betaIntegral (a : ℂ) (c : ℂ) = (betaReal a c : ℂ) := by
  unfold Complex.betaIntegral betaReal
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have h1 : (0 : ℝ) ≤ x := hx.1.le
  have h2 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
  have e1 := Complex.ofReal_cpow h1 (a - 1)
  have e2 := Complex.ofReal_cpow h2 (c - 1)
  push_cast at e1 e2
  simp only [Complex.ofReal_mul]
  rw [e1, e2]

/-- The Beta–Gamma relation for real arguments. -/
theorem Gamma_mul_Gamma_eq_betaReal {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.Gamma a * Real.Gamma c = Real.Gamma (a + c) * betaReal a c := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (c : ℂ))
    (by simpa using ha) (by simpa using hc)
  rw [betaIntegral_ofReal] at h
  rw [← Complex.ofReal_add] at h
  simp only [Complex.Gamma_ofReal, ← Complex.ofReal_mul] at h
  exact_mod_cast h

/-- The closed-form note's Lemma C7: `B(1/6, 1/2) = 3 Γ(1/3)³ / (2^(4/3) π)`. -/
theorem betaReal_one_sixth_one_half :
    betaReal (1 / 6) (1 / 2) = 3 * Real.Gamma (1 / 3) ^ 3 / ((2 : ℝ) ^ (4 / 3 : ℝ) * Real.pi) := by
  set G := Real.Gamma (1 / 3) with hG
  set H := Real.Gamma (2 / 3) with hH
  set A := Real.Gamma (1 / 6) with hA
  set B := betaReal (1 / 6) (1 / 2) with hB
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < √Real.pi := Real.sqrt_pos.2 hpi
  have hGpos : 0 < G := Real.Gamma_pos_of_pos (by norm_num)
  have hHpos : 0 < H := Real.Gamma_pos_of_pos (by norm_num)
  have hApos : 0 < A := Real.Gamma_pos_of_pos (by norm_num)
  -- Beta–Gamma
  have h1 : A * √Real.pi = H * B := by
    have := Gamma_mul_Gamma_eq_betaReal (a := 1 / 6) (c := 1 / 2) (by norm_num) (by norm_num)
    rw [Real.Gamma_one_half_eq] at this
    rw [show (1 / 6 + 1 / 2 : ℝ) = 2 / 3 by norm_num] at this
    exact this
  -- duplication
  have h2 : A * H = (2 : ℝ) ^ (2 / 3 : ℝ) * √Real.pi * G := by
    have := Real.Gamma_mul_Gamma_add_half (1 / 6)
    rw [show (1 / 6 + 1 / 2 : ℝ) = 2 / 3 by norm_num, show (2 * (1 / 6) : ℝ) = 1 / 3 by norm_num,
      show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at this
    rw [this]; ring
  -- reflection
  have h3 : G * H = 2 * Real.pi / √3 := by
    have := Real.Gamma_mul_Gamma_one_sub (1 / 3)
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, show Real.pi * (1 / 3) = Real.pi / 3 by ring,
      Real.sin_pi_div_three] at this
    rw [this]
    have h3' : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
    field_simp
  have h3s : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3' : 0 < √3 := Real.sqrt_pos.2 (by norm_num)
  -- `2^(4/3) * 2^(2/3) = 4`
  have h4 : (2 : ℝ) ^ (4 / 3 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    rw [← Real.rpow_add (by norm_num), show (4 / 3 + 2 / 3 : ℝ) = 2 by norm_num, Real.rpow_two]
    norm_num
  have h4pos : 0 < (2 : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h4pos' : 0 < (2 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : √Real.pi * √Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  set c : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) with hc
  set d : ℝ := (2 : ℝ) ^ (4 / 3 : ℝ) with hd
  -- `B H² = c π G`
  have k1 : B * H ^ 2 = c * Real.pi * G := by
    calc B * H ^ 2 = (H * B) * H := by ring
      _ = (A * √Real.pi) * H := by rw [h1]
      _ = (A * H) * √Real.pi := by ring
      _ = c * (√Real.pi * √Real.pi) * G := by rw [h2]; ring
      _ = c * Real.pi * G := by rw [hsq]
  -- `G² H² = 4π²/3`
  have k2 : (G * H) ^ 2 * 3 = 4 * Real.pi ^ 2 := by
    rw [h3, div_pow, Real.sq_sqrt (by norm_num)]
    field_simp
    norm_num
  have k3 : B * (4 * Real.pi ^ 2) = 3 * c * Real.pi * G ^ 3 := by
    calc B * (4 * Real.pi ^ 2) = B * ((G * H) ^ 2 * 3) := by rw [k2]
      _ = 3 * G ^ 2 * (B * H ^ 2) := by ring
      _ = 3 * c * Real.pi * G ^ 3 := by rw [k1]; ring
  rw [eq_div_iff (by positivity)]
  have key : B * (d * Real.pi) * (4 * Real.pi ^ 2) = 3 * G ^ 3 * (4 * Real.pi ^ 2) := by
    calc B * (d * Real.pi) * (4 * Real.pi ^ 2) = d * Real.pi * (B * (4 * Real.pi ^ 2)) := by ring
      _ = d * Real.pi * (3 * c * Real.pi * G ^ 3) := by rw [k3]
      _ = 3 * G ^ 3 * (d * c) * Real.pi ^ 2 := by ring
      _ = 3 * G ^ 3 * (4 * Real.pi ^ 2) := by rw [h4]; ring
  exact mul_right_cancel₀ (by positivity) key

end ClosedForm

end SandierSerfaty
