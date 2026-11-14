/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.GreenOne
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Jensen's formula for the theta product on horizontal slices

The closed-form note's Lemma B4(a). For `τ` in the upper half
plane and `0 < y < Im τ`,
`∫₀¹ log ‖θ τ (x + i y)‖ dx = 2 π y`
(`SandierSerfaty.ClosedForm.integral_log_norm_theta`), and consequently the slice mean of the theta
Green function `thetaGreen0 τ` is `π y² / Im τ - π y`
(`SandierSerfaty.ClosedForm.integral_thetaGreen0_slice`).

Proof: `θ(w) = -e(-w)⁻¹ ... ` is split as `e(-w) · A(e(w)) · B(e(-w))`, with `A(u) = (1 - u) R(u)` zero-free
on `‖u‖ < 1` and `B(v) = R(v)` zero-free on `‖v‖ < ‖Q‖⁻¹`; on a horizontal slice `e(w)` and `e(-w)` run
once around circles of radius `e^{-2π y} < 1` and `e^{2π y} < ‖Q‖⁻¹`, and the mean value property of the
harmonic functions `log ‖A‖`, `log ‖B‖` gives `log ‖A 0‖ = log ‖B 0‖ = 0`. No sum–integral interchange is needed.
-/

open Complex MeasureTheory intervalIntegral Real
open SandierSerfaty.Torus

public section

namespace SandierSerfaty

namespace ClosedForm

theorem integral_circle_pos {φ : ℂ → ℝ} {R : ℝ}
    (hφ : InnerProductSpace.HarmonicOnNhd φ (Metric.closedBall 0 |R|)) :
    ∫ x in (0:ℝ)..1, φ ((R:ℂ) * Complex.exp (↑(2 * π * x) * I)) = φ 0 := by
  have h := hφ.circleAverage_eq
  rw [circleAverage_def, smul_eq_mul] at h
  have h2 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun θ => φ (circleMap 0 R θ)) (c := 2*π) (by positivity)
  simp only [mul_zero, mul_one, smul_eq_mul, circleMap, zero_add] at h2 h ⊢
  rw [h2, h]

theorem integral_circle_neg {φ : ℂ → ℝ} {R : ℝ}
    (hφ : InnerProductSpace.HarmonicOnNhd φ (Metric.closedBall 0 |R|)) :
    ∫ x in (0:ℝ)..1, φ ((R:ℂ) * Complex.exp (-(↑(2 * π * x) * I))) = φ 0 := by
  rw [← integral_circle_pos hφ]
  have h := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => φ ((R:ℂ) * Complex.exp (↑(2 * π * x) * I))) (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  congr 2
  have : (↑(2 * π * (1 - x)) * I : ℂ) = 2 * π * I + -(↑(2 * π * x) * I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

variable {τ : ℂ}

/-- Factorisation of the theta product on a horizontal line. -/
theorem norm_theta_eq (w : ℂ) :
    ‖theta τ w‖ = Real.exp (2 * π * w.im) *
      (‖(1 - eF w) * thetaR (eF τ) (eF w)‖ * ‖thetaR (eF τ) (eF (-w))‖) := by
  have hu : eF (-w) = (eF w)⁻¹ := eF_neg w
  have h1 : (1 - eF (-w)) = -(eF (-w)) * (1 - eF w) := by
    rw [hu]
    have := eF_ne_zero w
    field_simp
    ring
  have h2 : ‖eF (-w)‖ = Real.exp (2 * π * w.im) := by
    rw [norm_eF]; simp
  unfold theta
  rw [h1, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, h2]
  ring


theorem thetaR_ne_zero_of_norm_lt {Q v : ℂ} (hQ : ‖Q‖ < 1) (hv : ‖Q‖ * ‖v‖ < 1) :
    thetaR Q v ≠ 0 := by
  rw [thetaR_ne_zero_iff hQ]
  intro n hn
  have h1 : Q ^ (n + 1) * v = 1 := by linear_combination -hn
  have h2 : ‖Q ^ (n + 1) * v‖ ≤ ‖Q‖ * ‖v‖ := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_of_le_one (norm_nonneg Q) hQ.le (Nat.succ_ne_zero n)) (norm_nonneg v)
  rw [h1] at h2
  simp at h2
  linarith

/-- `φA u = log ‖(1 - u) R(u)‖` is harmonic on the closed ball of radius `r < 1`. -/
theorem harmonic_phiA {τ : ℂ} (hτ : 0 < τ.im) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    InnerProductSpace.HarmonicOnNhd
      (fun u : ℂ => Real.log ‖(1 - u) * thetaR (eF τ) u‖) (Metric.closedBall 0 |r|) := by
  intro u hu
  have hQ := norm_eF_lt_one hτ
  have hu' : ‖u‖ ≤ r := by
    simpa [abs_of_nonneg hr0] using hu
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu' hr
  refine AnalyticAt.harmonicAt_log_norm ?_ ?_
  · exact ((analyticAt_const.sub analyticAt_id).mul
      ((differentiable_thetaR hQ).analyticAt u))
  · refine mul_ne_zero ?_ ?_
    · intro h
      have : u = 1 := by linear_combination -h
      rw [this] at hu1; simp at hu1
    · refine thetaR_ne_zero_of_norm_lt hQ ?_
      nlinarith [norm_nonneg u, norm_nonneg (eF τ)]

/-- `φB v = log ‖R(v)‖` is harmonic on the closed ball of radius `s` when `‖Q‖ s < 1`. -/
theorem harmonic_phiB {τ : ℂ} (hτ : 0 < τ.im) {s : ℝ} (hs0 : 0 ≤ s) (hs : ‖eF τ‖ * s < 1) :
    InnerProductSpace.HarmonicOnNhd
      (fun v : ℂ => Real.log ‖thetaR (eF τ) v‖) (Metric.closedBall 0 |s|) := by
  intro v hv
  have hQ := norm_eF_lt_one hτ
  have hv' : ‖v‖ ≤ s := by
    simpa [abs_of_nonneg hs0] using hv
  refine AnalyticAt.harmonicAt_log_norm ((differentiable_thetaR hQ).analyticAt v) ?_
  refine thetaR_ne_zero_of_norm_lt hQ ?_
  calc ‖eF τ‖ * ‖v‖ ≤ ‖eF τ‖ * s := mul_le_mul_of_nonneg_left hv' (norm_nonneg _)
    _ < 1 := hs


theorem eF_pos_line (x y : ℝ) :
    eF ((x : ℂ) + y * I) = ((Real.exp (-(2 * π * y)) : ℝ) : ℂ) * Complex.exp (↑(2 * π * x) * I) := by
  rw [eF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (2 * π * y : ℂ) * Complex.I_sq

theorem eF_neg_line (x y : ℝ) :
    eF (-((x : ℂ) + y * I)) =
      ((Real.exp (2 * π * y) : ℝ) : ℂ) * Complex.exp (-(↑(2 * π * x) * I)) := by
  rw [eF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (-(2 * π * y) : ℂ) * Complex.I_sq

theorem norm_circle_param (R x : ℝ) (hR : 0 ≤ R) :
    ‖(R : ℂ) * Complex.exp (↑(2 * π * x) * I)‖ = R := by
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_of_nonneg hR]

theorem norm_circle_param' (R x : ℝ) (hR : 0 ≤ R) :
    ‖(R : ℂ) * Complex.exp (-(↑(2 * π * x) * I))‖ = R := by
  have : -(↑(2 * π * x) * I : ℂ) = ((-(2 * π * x) : ℝ) : ℂ) * I := by push_cast; ring
  rw [norm_mul, Complex.norm_real, this, Complex.norm_exp_ofReal_mul_I, mul_one,
    Real.norm_of_nonneg hR]


/-- On the open strip `0 < Im w < Im τ` the theta product does not vanish. -/
theorem theta_ne_zero_of_im {τ : ℂ} (hτ : 0 < τ.im) {w : ℂ} (h0 : 0 < w.im) (h1 : w.im < τ.im) :
    theta τ w ≠ 0 := by
  intro h
  obtain ⟨m, n, hmn⟩ := (theta_eq_zero_iff hτ w).1 h
  have him : w.im = n * τ.im := by
    rw [hmn]; simp
  rw [him] at h0 h1
  have h2 : (0 : ℝ) < n := by
    by_contra hn
    replace hn := not_lt.1 hn
    nlinarith
  have h3 : (n : ℝ) < 1 := by
    by_contra hn
    replace hn := not_lt.1 hn
    nlinarith
  have h4 : (0 : ℤ) < n := by exact_mod_cast h2
  have h5 : n < (1 : ℤ) := by exact_mod_cast h3
  omega

/-- The slice integral of `log ‖θ‖` over a horizontal period: Jensen's formula. -/
theorem integral_log_norm_theta {τ : ℂ} (hτ : 0 < τ.im) {y : ℝ} (hy0 : 0 < y) (hy1 : y < τ.im) :
    ∫ x in (0 : ℝ)..1, Real.log ‖theta τ ((x : ℂ) + y * I)‖ = 2 * π * y := by
  have hQ := norm_eF_lt_one hτ
  set r : ℝ := Real.exp (-(2 * π * y)) with hr
  set s : ℝ := Real.exp (2 * π * y) with hs
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hs0 : 0 ≤ s := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
  have hQs : ‖eF τ‖ * s < 1 := by
    rw [norm_eF, hs, ← Real.exp_add, Real.exp_lt_one_iff]
    have := Real.pi_pos; nlinarith
  have hA := harmonic_phiA hτ hr0 hr1
  have hB := harmonic_phiB hτ hs0 hQs
  -- pointwise decomposition
  have hdec : ∀ x : ℝ, Real.log ‖theta τ ((x : ℂ) + y * I)‖ =
      2 * π * y +
        (Real.log ‖(1 - ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))) *
            thetaR (eF τ) ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))‖ +
          Real.log ‖thetaR (eF τ) ((s : ℂ) * Complex.exp (-(↑(2 * π * x) * I)))‖) := by
    intro x
    have hnorm := norm_theta_eq (τ := τ) ((x : ℂ) + y * I)
    have him : ((x : ℂ) + y * I).im = y := by simp
    rw [him] at hnorm
    rw [eF_pos_line, eF_neg_line, ← hr, ← hs] at hnorm
    have hu : ‖(r : ℂ) * Complex.exp (↑(2 * π * x) * I)‖ < 1 := by
      rw [norm_circle_param r x hr0]; exact hr1
    have hv : ‖eF τ‖ * ‖(s : ℂ) * Complex.exp (-(↑(2 * π * x) * I))‖ < 1 := by
      rw [norm_circle_param' s x hs0]; exact hQs
    have hb : thetaR (eF τ) ((s : ℂ) * Complex.exp (-(↑(2 * π * x) * I))) ≠ 0 :=
      thetaR_ne_zero_of_norm_lt hQ hv
    have ha : (1 - ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))) *
        thetaR (eF τ) ((r : ℂ) * Complex.exp (↑(2 * π * x) * I)) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · intro h
        have h1 : ((r : ℂ) * Complex.exp (↑(2 * π * x) * I)) = 1 := by linear_combination -h
        rw [h1] at hu; simp at hu
      · refine thetaR_ne_zero_of_norm_lt hQ ?_
        nlinarith [norm_nonneg ((r : ℂ) * Complex.exp (↑(2 * π * x) * I)), norm_nonneg (eF τ)]
    have hs_ne : s ≠ 0 := (Real.exp_pos _).ne'
    have hna := norm_ne_zero_iff.2 ha
    have hnb := norm_ne_zero_iff.2 hb
    rw [hnorm, Real.log_mul hs_ne (mul_ne_zero hna hnb), Real.log_mul hna hnb, hs, Real.log_exp]
  have cA : Continuous fun x : ℝ => Real.log ‖(1 - ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))) *
      thetaR (eF τ) ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))‖ := by
    refine hA.continuousOn.comp_continuous (by fun_prop) fun x => ?_
    simp only [Metric.mem_closedBall, dist_zero_right, norm_circle_param r x hr0,
      abs_of_nonneg hr0, le_refl]
  have cB : Continuous fun x : ℝ => Real.log ‖thetaR (eF τ)
      ((s : ℂ) * Complex.exp (-(↑(2 * π * x) * I)))‖ := by
    refine hB.continuousOn.comp_continuous (by fun_prop) fun x => ?_
    simp only [Metric.mem_closedBall, dist_zero_right, norm_circle_param' s x hs0,
      abs_of_nonneg hs0, le_refl]
  set A : ℝ → ℝ := fun x => Real.log ‖(1 - ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))) *
      thetaR (eF τ) ((r : ℂ) * Complex.exp (↑(2 * π * x) * I))‖ with hAdef
  set B : ℝ → ℝ := fun x => Real.log ‖thetaR (eF τ)
      ((s : ℂ) * Complex.exp (-(↑(2 * π * x) * I)))‖ with hBdef
  have hABi : IntervalIntegrable (fun x => A x + B x) MeasureTheory.volume 0 1 :=
    (cA.add cB).intervalIntegrable 0 1
  have h1 : ∫ x in (0 : ℝ)..1, Real.log ‖theta τ ((x : ℂ) + y * I)‖ =
      ∫ x in (0 : ℝ)..1, (2 * π * y + (A x + B x)) :=
    intervalIntegral.integral_congr fun x _ => hdec x
  rw [h1, intervalIntegral.integral_add intervalIntegrable_const hABi,
    intervalIntegral.integral_add (cA.intervalIntegrable _ _) (cB.intervalIntegrable _ _),
    hAdef, hBdef]
  simp only
  rw [integral_circle_pos hA, integral_circle_neg hB]
  simp [thetaR]


/-- The slice mean of the theta Green function: `∫₀¹ Ĝ_τ (x + i y) dx = π y² / Im τ - π y`
for `0 < y < Im τ`. -/
theorem integral_thetaGreen0_slice {τ : ℂ} (hτ : 0 < τ.im) {y : ℝ} (hy0 : 0 < y)
    (hy1 : y < τ.im) :
    ∫ x in (0 : ℝ)..1, thetaGreen0 τ ((x : ℂ) + y * I) = π * y ^ 2 / τ.im - π * y := by
  have hne : ∀ x : ℝ, theta τ ((x : ℂ) + y * I) ≠ 0 := fun x =>
    theta_ne_zero_of_im hτ (by simpa using hy0) (by simpa using hy1)
  have hc : Continuous fun x : ℝ => Real.log ‖theta τ ((x : ℂ) + y * I)‖ :=
    (((differentiable_theta hτ).continuous.comp (by fun_prop)).norm).log
      fun x => norm_ne_zero_iff.2 (hne x)
  have h1 : ∀ x : ℝ, thetaGreen0 τ ((x : ℂ) + y * I) =
      -Real.log ‖theta τ ((x : ℂ) + y * I)‖ + (π * y ^ 2 / τ.im + π * y) := by
    intro x
    simp only [thetaGreen0, hne x, ite_false, thetaGreen]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im]
    ring
  simp_rw [h1]
  have hneg : IntervalIntegrable (fun x : ℝ => -Real.log ‖theta τ ((x : ℂ) + y * I)‖)
      MeasureTheory.volume 0 1 := (hc.neg).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hneg intervalIntegrable_const,
    intervalIntegral.integral_neg, integral_log_norm_theta hτ hy0 hy1]
  simp
  ring

end ClosedForm

end SandierSerfaty

end
