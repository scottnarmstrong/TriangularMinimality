/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.GreenSymmetry
public import SandierSerfaty.Torus.GreenLocal
public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The holomorphic part of the theta Green function of the hexagonal lattice

Ingredients of the proof of `cal:green-expansion`, part 2.

With `θ = theta ρ` (`ρ = e^{πi/3}`), write `θ(w) = w q(w)` with `q = thetaQ` entire
(`Torus.exists_theta_factor`) and `q 0 ≠ 0`. The zeros of `θ` are the points of `ℤ + ℤρ`, whose nonzero
elements have norm at least `1` (`one_le_norm_of_mem_hexLattice`), so `q` has no zero on the unit disc.
The logarithmic derivative `q'/q` is holomorphic there, hence has a primitive `M` on the disc
(`DifferentiableOn.isExactOn_ball`), and `q = q 0 · e^M` on the disc.

Then `Ĝ = thetaGreen0 ρ` satisfies, for `0 < ‖w‖ < 1`,
`Ĝ w = - log ‖w‖ + C₀ + (π / (2 Im ρ)) ‖w‖² + Re F w`,
`F w = - M w - (π / (2 Im ρ)) w² - π i w` holomorphic on the disc
(`exists_green_holomorphic_part`). This is the statement "`h + log|z| - π|z|²/2 = Re F` with `F`
holomorphic" of the paper's proof, and shows that the
logarithmic singularity of `Ĝ` is exactly `-log‖w‖`, with a smooth (indeed holomorphic-real-part)
remainder, so that no simple-pole term appears.
-/

open Filter Topology Metric Complex
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm Torus

/-- `q = θ(w) / w`, the entire function with `θ(w) = w q(w)` (`dslope θ 0`). -/
@[expose] noncomputable def thetaQ : ℂ → ℂ := dslope (theta rho) 0

theorem differentiable_thetaQ : Differentiable ℂ thetaQ := by
  unfold thetaQ
  rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem,
    differentiableOn_univ]
  exact differentiable_theta rho_im_pos

theorem thetaQ_zero_ne_zero : thetaQ 0 ≠ 0 := by
  unfold thetaQ
  rw [dslope_same, (hasDerivAt_theta_zero rho_im_pos).deriv]
  have := thetaR_one_ne_zero rho_im_pos
  simp [Real.pi_ne_zero, this]

theorem theta_eq_mul_thetaQ (w : ℂ) : theta rho w = w * thetaQ w := by
  have := sub_smul_dslope (theta rho) 0 w
  simpa [thetaQ, theta_zero] using this.symm

/-- Nonzero points of `ℤ + ℤρ` have norm at least `1`. -/
theorem one_le_norm_of_mem_hexLattice {x : ℂ} (hx : x ∈ hexPair.lattice) (h0 : x ≠ 0) :
    1 ≤ ‖x‖ := by
  obtain ⟨m, n, rfl⟩ := mem_hexPair_lattice.1 hx
  have hint : (1 : ℤ) ≤ m ^ 2 + m * n + n ^ 2 := by
    by_contra hlt
    push Not at hlt
    have h1 : m ^ 2 + m * n + n ^ 2 ≤ 0 := by omega
    have hm : m = 0 := by nlinarith [sq_nonneg (m + 2 * n), sq_nonneg m, sq_nonneg n]
    have hn : n = 0 := by subst hm; nlinarith [sq_nonneg n]
    apply h0
    simp [hm, hn]
  have hreal : (1 : ℝ) ≤ (m : ℝ) ^ 2 + m * n + n ^ 2 := by exact_mod_cast hint
  have hsq : ‖(m : ℂ) * rho + n‖ ^ 2 = (m : ℝ) ^ 2 + m * n + n ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, rho_re,
      rho_im, Complex.add_im, Complex.mul_im]
    have : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  nlinarith [norm_nonneg ((m : ℂ) * rho + n)]

theorem theta_ne_zero_of_norm_lt_one {w : ℂ} (hw1 : ‖w‖ < 1) (hw0 : w ≠ 0) : theta rho w ≠ 0 := by
  intro h
  obtain ⟨m, n, hmn⟩ := (theta_eq_zero_iff rho_im_pos w).1 h
  have hmem : w ∈ hexPair.lattice := mem_hexPair_lattice.2 ⟨n, m, by rw [hmn]; ring⟩
  exact absurd (one_le_norm_of_mem_hexLattice hmem hw0) (not_le.2 hw1)

theorem thetaQ_ne_zero_of_norm_lt_one {w : ℂ} (hw1 : ‖w‖ < 1) : thetaQ w ≠ 0 := by
  by_cases hw0 : w = 0
  · rw [hw0]; exact thetaQ_zero_ne_zero
  · intro h
    exact theta_ne_zero_of_norm_lt_one hw1 hw0 (by rw [theta_eq_mul_thetaQ, h, mul_zero])

/-- The logarithmic derivative of `q`, holomorphic on the unit disc. -/
@[expose] noncomputable def thetaQlog (w : ℂ) : ℂ := deriv thetaQ w / thetaQ w

theorem differentiableOn_thetaQlog : DifferentiableOn ℂ thetaQlog (ball 0 1) := by
  intro w hw
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hd : Differentiable ℂ (deriv thetaQ) := differentiable_thetaQ.deriv
  exact ((hd w).div (differentiable_thetaQ w) (thetaQ_ne_zero_of_norm_lt_one hw1)).differentiableWithinAt

/-- A primitive `M` of `q'/q` on the unit disc with `M 0 = 0`. -/
theorem exists_primitive_thetaQlog :
    ∃ M : ℂ → ℂ, M 0 = 0 ∧ ∀ w ∈ ball (0 : ℂ) 1, HasDerivAt M (thetaQlog w) w :=
  differentiableOn_thetaQlog.isExactOn_ball.with_val_at 0 0

/-- `q = q 0 · e^M` on the unit disc. -/
theorem thetaQ_eq_exp {M : ℂ → ℂ} (hM0 : M 0 = 0)
    (hM : ∀ w ∈ ball (0 : ℂ) 1, HasDerivAt M (thetaQlog w) w) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    thetaQ w = thetaQ 0 * Complex.exp (M w) := by
  set φ : ℂ → ℂ := fun x => thetaQ x * Complex.exp (-M x) with hφ
  have hder : ∀ x ∈ ball (0 : ℂ) 1, HasDerivAt φ 0 x := by
    intro x hx
    have hx1 : ‖x‖ < 1 := by simpa using hx
    have hq : HasDerivAt thetaQ (deriv thetaQ x) x := (differentiable_thetaQ x).hasDerivAt
    have hE : HasDerivAt (fun y => Complex.exp (-M y)) (Complex.exp (-M x) * (-thetaQlog x)) x :=
      (hM x hx).neg.cexp
    have := hq.mul hE
    convert this using 1
    have hqx := thetaQ_ne_zero_of_norm_lt_one hx1
    unfold thetaQlog
    field_simp
    ring
  have hdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) := fun x hx =>
    (hder x hx).differentiableAt.differentiableWithinAt
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    hdiff (fun x hx => (hder x hx).deriv) hw (mem_ball_self one_pos)
  simp only [hφ, hM0, neg_zero, Complex.exp_zero, mul_one] at hconst
  have : thetaQ w = thetaQ w * Complex.exp (-M w) * Complex.exp (M w) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [this, hconst]

/-- **The holomorphic part of the theta Green function.** On the unit disc,
`Ĝ w = - log ‖w‖ + C₀ + (π / (2 Im ρ)) ‖w‖² + Re F w` off `0`, with `F` holomorphic and
`F'' = - (q'/q)' - π / Im ρ`. -/
theorem exists_green_holomorphic_part :
    ∃ (F : ℂ → ℂ) (C₀ : ℝ), DifferentiableOn ℂ F (ball 0 1) ∧
      (∀ w ∈ ball (0 : ℂ) 1,
        deriv (deriv F) w = -deriv thetaQlog w - Real.pi / rho.im) ∧
      ∀ w ∈ ball (0 : ℂ) 1, w ≠ 0 →
        thetaGreen0 rho w = -Real.log ‖w‖ + C₀ + Real.pi / (2 * rho.im) * ‖w‖ ^ 2 + (F w).re := by
  obtain ⟨M, hM0, hM⟩ := exists_primitive_thetaQlog
  have hτ : 0 < rho.im := rho_im_pos
  set α : ℂ := ((Real.pi / (2 * rho.im) : ℝ) : ℂ) with hα
  set F : ℂ → ℂ := fun w => -M w - α * w ^ 2 - Real.pi * Complex.I * w with hF
  have hFd : ∀ w ∈ ball (0 : ℂ) 1,
      HasDerivAt F (-thetaQlog w - 2 * α * w - Real.pi * Complex.I) w := by
    intro w hw
    have h1 := (hM w hw).neg
    have h2 : HasDerivAt (fun x : ℂ => α * x ^ 2) (α * (2 * w)) w := by
      simpa using (hasDerivAt_pow 2 w).const_mul α
    have h3 : HasDerivAt (fun x : ℂ => (Real.pi * Complex.I) * x) (Real.pi * Complex.I) w := by
      simpa using (hasDerivAt_id w).const_mul ((Real.pi : ℂ) * Complex.I)
    have := (h1.sub h2).sub h3
    convert this using 1
    ring
  have hFdiff : DifferentiableOn ℂ F (ball 0 1) := fun w hw =>
    (hFd w hw).differentiableAt.differentiableWithinAt
  refine ⟨F, -Real.log ‖thetaQ 0‖, hFdiff, ?_, ?_⟩
  · intro w hw
    have h1 : deriv F =ᶠ[𝓝 w] fun x => -thetaQlog x - 2 * α * x - Real.pi * Complex.I := by
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx
      exact (hFd x hx).deriv
    rw [h1.deriv_eq]
    have hq : DifferentiableAt ℂ thetaQlog w := differentiableOn_thetaQlog.differentiableAt
      (isOpen_ball.mem_nhds hw)
    have : HasDerivAt (fun x => -thetaQlog x - 2 * α * x - Real.pi * Complex.I)
        (-deriv thetaQlog w - 2 * α) w := by
      have h1 := hq.hasDerivAt.neg
      have h2 : HasDerivAt (fun x : ℂ => 2 * α * x) (2 * α) w := by
        simpa using (hasDerivAt_id w).const_mul (2 * α)
      have := (h1.sub h2).sub_const ((Real.pi : ℂ) * Complex.I)
      convert this using 1
    rw [this.deriv, hα]
    push_cast
    field_simp
  · intro w hw hw0
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hθ : theta rho w ≠ 0 := theta_ne_zero_of_norm_lt_one hw1 hw0
    have hq := thetaQ_eq_exp hM0 hM hw
    have hnorm : ‖theta rho w‖ = ‖w‖ * (‖thetaQ 0‖ * Real.exp (M w).re) := by
      rw [theta_eq_mul_thetaQ, norm_mul, hq, norm_mul, Complex.norm_exp]
    have hw0' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
    have hq0 : ‖thetaQ 0‖ ≠ 0 := norm_ne_zero_iff.2 thetaQ_zero_ne_zero
    have hlog : Real.log ‖theta rho w‖ = Real.log ‖w‖ + Real.log ‖thetaQ 0‖ + (M w).re := by
      rw [hnorm, Real.log_mul hw0' (mul_ne_zero hq0 (Real.exp_pos _).ne'),
        Real.log_mul hq0 (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hre : (F w).re = -(M w).re - Real.pi / (2 * rho.im) * (w.re ^ 2 - w.im ^ 2) +
        Real.pi * w.im := by
      simp only [hF, hα, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, pow_two, Complex.I_re, Complex.I_im, Complex.mul_im]
      ring
    unfold thetaGreen0 thetaGreen
    simp only [hθ, ↓reduceIte]
    rw [hlog, hre]
    have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn]
    field_simp
    ring

end Calibration

end SandierSerfaty

end
