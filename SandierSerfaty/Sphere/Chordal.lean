/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The chordal, inversion and Mercator identities (sphere note, Lemma 3.1)

* `Sphere.norm_stereo_sub`: `‖T x - T x'‖ = √(λ x λ x') |x - x'|`;
* `Sphere.norm_invC_sub`, `Sphere.lam_invC`: `|ι x - ι x'| = |x - x'| / (|x||x'|)` and
  `λ (ι x) = |x|² λ x`;
* `Sphere.mercator_eq_stereo`: `ℳ(s, t) = T(e^{t + is})`.
-/

open Complex

public section

namespace SandierSerfaty

namespace Sphere

theorem lam_pos (x : ℂ) : 0 < lam x := by
  unfold lam; positivity

theorem one_add_norm_sq_pos (x : ℂ) : 0 < 1 + ‖x‖ ^ 2 := by positivity

theorem norm_stereo_sq (x : ℂ) : ‖stereo x‖ ^ 2 = 1 := by
  have h : 0 < 1 + ‖x‖ ^ 2 := one_add_norm_sq_pos x
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, stereo_apply_zero, stereo_apply_one, stereo_apply_two,
    Real.norm_eq_abs, sq_abs]
  have e : ‖x‖ ^ 2 = x.re * x.re + x.im * x.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [e] at h ⊢
  field_simp
  ring

theorem norm_stereo (x : ℂ) : ‖stereo x‖ = 1 := by
  have := norm_stereo_sq x
  nlinarith [norm_nonneg (stereo x)]

/-- **Chordal identity**, squared form. -/
theorem norm_stereo_sub_sq (x x' : ℂ) :
    ‖stereo x - stereo x'‖ ^ 2 = lam x * lam x' * ‖x - x'‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, stereo_apply_zero, stereo_apply_one, stereo_apply_two, lam,
    Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  have e : ∀ y : ℂ, ‖y‖ ^ 2 = y.re * y.re + y.im * y.im := fun y => by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h1 := one_add_norm_sq_pos x
  have h2 := one_add_norm_sq_pos x'
  rw [e (x - x'), e x, e x'] at *
  simp only [Complex.sub_re, Complex.sub_im]
  field_simp
  ring

/-- **Chordal identity.** `‖T x - T x'‖ = √(λ x λ x') |x - x'|`. -/
theorem norm_stereo_sub (x x' : ℂ) :
    ‖stereo x - stereo x'‖ = Real.sqrt (lam x * lam x') * ‖x - x'‖ := by
  have h : ‖stereo x - stereo x'‖ ^ 2 = (Real.sqrt (lam x * lam x') * ‖x - x'‖) ^ 2 := by
    rw [norm_stereo_sub_sq, mul_pow, Real.sq_sqrt (mul_nonneg (lam_pos x).le (lam_pos x').le)]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h

theorem norm_invC_sub {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ‖invC x - invC x'‖ = ‖x - x'‖ / (‖x‖ * ‖x'‖) := by
  unfold invC
  have h1 : (starRingEnd ℂ x) ≠ 0 := by simpa using hx
  have h2 : (starRingEnd ℂ x') ≠ 0 := by simpa using hx'
  have : (starRingEnd ℂ x)⁻¹ - (starRingEnd ℂ x')⁻¹ =
      (starRingEnd ℂ x' - starRingEnd ℂ x) / (starRingEnd ℂ x * starRingEnd ℂ x') := by
    field_simp
  rw [this, norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, ← map_sub,
    Complex.norm_conj, norm_sub_rev]

theorem lam_invC {x : ℂ} (hx : x ≠ 0) : lam (invC x) = ‖x‖ ^ 2 * lam x := by
  unfold lam invC
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [norm_inv, Complex.norm_conj]
  have : 0 < 1 + ‖x‖ ^ 2 := one_add_norm_sq_pos x
  field_simp
  ring

/-! ### The Mercator map -/

theorem mercator_eq_stereo (s t : ℝ) :
    mercator s t = stereo (Complex.exp ((t : ℂ) + (s : ℂ) * Complex.I)) := by
  have hn : ‖Complex.exp ((t : ℂ) + (s : ℂ) * Complex.I)‖ = Real.exp t := by
    rw [Complex.norm_exp]; simp
  have hre : (Complex.exp ((t : ℂ) + (s : ℂ) * Complex.I)).re = Real.exp t * Real.cos s := by
    rw [Complex.exp_re]; simp
  have him : (Complex.exp ((t : ℂ) + (s : ℂ) * Complex.I)).im = Real.exp t * Real.sin s := by
    rw [Complex.exp_im]; simp
  have hc : Real.cosh t = (Real.exp t + Real.exp (-t)) / 2 := Real.cosh_eq t
  have hc0 : 0 < Real.cosh t := Real.cosh_pos t
  have hE : 0 < Real.exp t := Real.exp_pos t
  have hE' : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  have hth : Real.tanh t = (Real.exp t ^ 2 - 1) / (1 + Real.exp t ^ 2) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, hc, hE']
    field_simp
    ring
  ext i
  fin_cases i
  · simp only [mercator, stereo, hn, hre]
    simp
    rw [hc, hE']
    field_simp
    ring
  · simp only [mercator, stereo, hn, him]
    simp
    rw [hc, hE']
    field_simp
    ring
  · simp only [mercator, stereo, hn, hth]
    simp

theorem lam_exp (s t : ℝ) :
    lam (Complex.exp ((t : ℂ) + (s : ℂ) * Complex.I)) = Real.exp (-t) / Real.cosh t := by
  have hn : ‖Complex.exp ((t : ℂ) + (s : ℂ) * Complex.I)‖ = Real.exp t := by
    rw [Complex.norm_exp]; simp
  have hc : Real.cosh t = (Real.exp t + Real.exp (-t)) / 2 := Real.cosh_eq t
  have hE : 0 < Real.exp t := Real.exp_pos t
  have hE' : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  unfold lam
  rw [hn, hc, hE']
  field_simp
  ring

end Sphere

end SandierSerfaty

end
