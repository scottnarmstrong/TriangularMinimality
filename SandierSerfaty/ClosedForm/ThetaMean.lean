/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.RectDomain
public import SandierSerfaty.ClosedForm.ThetaJensen

/-!
# The mean of the single-charge theta Green function

The closed-form note's Lemma B4(b) and Theorem B(a) ("mean zero"), in the form needed to fix the additive constant of the
triangular Green function. For `p > 0` and `Im τ > 0`, with `Γ = p (ℤ + ℤ τ)`, the rectangle
`V = [0, p) × [0, p Im τ)` is a fundamental domain (`RectDomain.lean`) of area `p² Im τ`, and
`SandierSerfaty.ClosedForm.integral_greenOne_rect` computes
`∫_V greenOne p τ = -π (p Im τ)² / 6`
(Fubini over horizontal slices, `integral_thetaGreen0_slice`, and `∫₀ᴸ (π y² / L - π y) dy = -π L² / 6`).
Integrability of `greenOne p τ` on `V` is a hypothesis here and is discharged where the lattice is fixed.
-/

open MeasureTheory Set Complex intervalIntegral Real
open SandierSerfaty.Torus

public section

namespace SandierSerfaty

namespace ClosedForm

/-- The slice integral of the single-charge Green function over `x ∈ [0, p)` at height `y`. -/
theorem integral_greenOne_slice {τ : ℂ} (hτ : 0 < τ.im) {p : ℝ} (hp : 0 < p) {y : ℝ}
    (hy0 : 0 < y) (hy1 : y < p * τ.im) :
    ∫ x in Ico 0 p, greenOne (p : ℂ) τ ⟨x, y⟩ = π * y ^ 2 / (p * τ.im) - π * y := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdiv : ∀ x : ℝ, ((⟨x, y⟩ : ℂ) / (p : ℂ)) = ((x / p : ℝ) : ℂ) + ((y / p : ℝ) : ℂ) * I := by
    intro x
    apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hy1' : y / p < τ.im := by rwa [div_lt_iff₀ hp, mul_comm]
  have hy0' : 0 < y / p := div_pos hy0 hp
  have h1 : ∀ x : ℝ, greenOne (p : ℂ) τ ⟨x, y⟩ =
      thetaGreen0 τ (((x / p : ℝ) : ℂ) + ((y / p : ℝ) : ℂ) * I) := by
    intro x
    unfold greenOne
    rw [hdiv]
  simp_rw [h1]
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hp.le]
  rw [intervalIntegral.integral_comp_div (fun x : ℝ => thetaGreen0 τ (((x : ℝ) : ℂ) +
    ((y / p : ℝ) : ℂ) * I)) hp.ne']
  rw [zero_div, div_self hp.ne', integral_thetaGreen0_slice hτ hy0' hy1']
  simp only [smul_eq_mul]
  field_simp

/-- **The mean of the single-charge theta Green function over the rectangle.** -/
theorem integral_greenOne_rect {τ : ℂ} (hτ : 0 < τ.im) {p : ℝ} (hp : 0 < p)
    (hf : IntegrableOn (greenOne (p : ℂ) τ)
      {z : ℂ | z.re ∈ Ico 0 p ∧ z.im ∈ Ico 0 (p * τ.im)}) :
    ∫ z in {z : ℂ | z.re ∈ Ico 0 p ∧ z.im ∈ Ico 0 (p * τ.im)}, greenOne (p : ℂ) τ z =
      -(π * (p * τ.im) ^ 2 / 6) := by
  have hL : 0 < p * τ.im := mul_pos hp hτ
  rw [setIntegral_re_im hf, integral_Ico_eq_integral_Ioo]
  rw [setIntegral_congr_fun measurableSet_Ioo fun y hy => integral_greenOne_slice hτ hp hy.1 hy.2]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL.le]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul]
  · simp only [integral_pow, integral_id]
    field_simp
    ring
  · exact (by fun_prop : Continuous fun y : ℝ => π * y ^ 2 / (p * τ.im)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun y : ℝ => π * y).intervalIntegrable _ _

end ClosedForm

end SandierSerfaty

end
