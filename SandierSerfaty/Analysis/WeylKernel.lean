/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.WeylRadial
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The radial mollifier on `ℂ`

A fixed smooth profile `prof : ℝ → ℝ` (a `ContDiffBump`) with values in `[0, 1]`, vanishing outside
`(3/8, 7/8)`, gives the radial kernels `kern δ w = prof (‖w‖² / δ²)`, supported in the annulus
`δ √(3/8) < ‖w‖ < δ √(7/8)`. The normalised kernel is `rho δ w = kern δ w / (δ² * kmass)` where
`kmass = ∫ kern 1`; it is smooth, nonnegative, even, supported in the closed disk of radius `δ`, of
integral one (`integral_rho`). `mollify δ u x = ∫ u y * rho δ (y - x) dy`.

Scale independence of the mollification of a weakly harmonic function is in
`SandierSerfaty.Analysis.WeylMollifier`; here only the kernel and the smoothness of `mollify`.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- The fixed bump profile. -/
@[expose] noncomputable def bump₀ : ContDiffBump (5 / 8 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The profile of the radial kernel, a function of `‖w‖²`. -/
@[expose] noncomputable def prof (s : ℝ) : ℝ := bump₀ s

theorem contDiff_prof : ContDiff ℝ ∞ prof := bump₀.contDiff (n := ⊤)

theorem prof_nonneg (s : ℝ) : 0 ≤ prof s := bump₀.nonneg

theorem prof_eq_zero_of_ne {s : ℝ} (h : s ∉ Metric.ball (5 / 8 : ℝ) (1 / 4)) : prof s = 0 := by
  have : s ∉ Function.support (bump₀ : ℝ → ℝ) := by
    rw [bump₀.support_eq]; exact h
  exact Function.notMem_support.mp this

theorem prof_eq_zero_of_le {s : ℝ} (h : s ≤ 1 / 4) : prof s = 0 := by
  refine prof_eq_zero_of_ne ?_
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  intro ⟨h1, _⟩
  have : (bump₀.rOut : ℝ) = 1 / 4 := rfl
  linarith

theorem prof_eq_zero_of_ge {s : ℝ} (h : 1 ≤ s) : prof s = 0 := by
  refine prof_eq_zero_of_ne ?_
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  intro ⟨_, h2⟩
  linarith

theorem prof_five_eighths : prof (5 / 8) = 1 :=
  bump₀.one_of_mem_closedBall (Metric.mem_closedBall_self (by
    show (0 : ℝ) ≤ 1 / 8
    norm_num))

/-- The unnormalised radial kernel at scale `δ`. -/
@[expose] noncomputable def kern (δ : ℝ) (w : ℂ) : ℝ := prof (‖w‖ ^ 2 / δ ^ 2)

/-- The mass of the unnormalised kernel at scale one. -/
@[expose] noncomputable def kmass : ℝ := ∫ w : ℂ, kern 1 w

/-- The normalised mollifying density at scale `δ`. -/
@[expose] noncomputable def rho (δ : ℝ) (w : ℂ) : ℝ := kern δ w / (δ ^ 2 * kmass)

theorem contDiff_kern (δ : ℝ) : ContDiff ℝ ∞ (kern δ) :=
  contDiff_prof.comp (((contDiff_norm_sq ℝ).div_const _))

theorem kern_nonneg (δ : ℝ) (w : ℂ) : 0 ≤ kern δ w := prof_nonneg _

theorem kern_eq_zero {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ ‖w‖) : kern δ w = 0 := by
  apply prof_eq_zero_of_ge
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem hasCompactSupport_kern {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (kern δ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ) fun w hw =>
    kern_eq_zero hδ (by
      have : δ < ‖w‖ := by simpa [mem_closedBall, not_le] using hw
      exact this.le)

theorem kmass_pos : 0 < kmass := by
  have hc : Continuous (kern 1) := (contDiff_kern 1).continuous
  have hx : kern 1 ((Real.sqrt (5 / 8) : ℝ) : ℂ) ≠ 0 := by
    simp only [kern, Complex.norm_real, Real.norm_eq_abs, one_pow, div_one]
    rw [sq_abs, Real.sq_sqrt (by norm_num), prof_five_eighths]
    norm_num
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (hasCompactSupport_kern one_pos)
    (fun w => kern_nonneg 1 w) hx

theorem integral_kern {δ : ℝ} (hδ : 0 < δ) : ∫ w : ℂ, kern δ w = δ ^ 2 * kmass := by
  have h1 : ∀ w : ℂ, kern δ w = kern 1 (δ⁻¹ • w) := by
    intro w
    simp only [kern, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ, one_pow, div_one]
    congr 1
    field_simp
  have h2 := Measure.integral_comp_smul (volume : Measure ℂ) (kern 1) δ⁻¹
  simp only [← h1, Complex.finrank_real_complex] at h2
  rw [h2]
  simp only [kmass, smul_eq_mul]
  rw [abs_of_pos (by positivity)]
  field_simp

theorem rho_nonneg (δ : ℝ) (w : ℂ) : 0 ≤ rho δ w :=
  div_nonneg (kern_nonneg δ w) (mul_nonneg (sq_nonneg _) kmass_pos.le)

theorem rho_eq_zero {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : δ ≤ ‖w‖) : rho δ w = 0 := by
  simp [rho, kern_eq_zero hδ hw]

theorem contDiff_rho (δ : ℝ) : ContDiff ℝ ∞ (rho δ) := (contDiff_kern δ).div_const _

theorem hasCompactSupport_rho {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (rho δ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) δ) fun w hw =>
    rho_eq_zero hδ (by
      have : δ < ‖w‖ := by simpa [mem_closedBall, not_le] using hw
      exact this.le)

theorem rho_sub_comm (δ : ℝ) (x y : ℂ) : rho δ (x - y) = rho δ (y - x) := by
  simp [rho, kern, norm_sub_rev x y]

theorem integral_rho {δ : ℝ} (hδ : 0 < δ) : ∫ w : ℂ, rho δ w = 1 := by
  have : ∫ w : ℂ, rho δ w = (∫ w : ℂ, kern δ w) / (δ ^ 2 * kmass) := by
    simp only [rho]; rw [integral_div]
  rw [this, integral_kern hδ]
  have := kmass_pos
  field_simp

theorem integral_rho_sub {δ : ℝ} (hδ : 0 < δ) (x : ℂ) : ∫ y : ℂ, rho δ (y - x) = 1 := by
  rw [integral_sub_right_eq_self (rho δ) x, integral_rho hδ]

theorem integrable_rho {δ : ℝ} (hδ : 0 < δ) : Integrable (rho δ) :=
  (contDiff_rho δ).continuous.integrable_of_hasCompactSupport (hasCompactSupport_rho hδ)

/-- The mollification of `u` at scale `δ`. -/
@[expose] noncomputable def mollify (δ : ℝ) (u : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, u y * rho δ (y - x)

theorem mollify_eq_convolution (δ : ℝ) (u : ℂ → ℝ) :
    mollify δ u = fun x => convolution u (rho δ) (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  funext x
  simp only [mollify, convolution_mul, rho_sub_comm δ x]

/-- The mollification of a locally integrable function is smooth. -/
theorem contDiff_mollify {δ : ℝ} (hδ : 0 < δ) {u : ℂ → ℝ} (hu : LocallyIntegrable u volume) :
    ContDiff ℝ ∞ (mollify δ u) := by
  rw [mollify_eq_convolution]
  exact (hasCompactSupport_rho hδ).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hu
    (contDiff_rho δ)

theorem integrable_mul_rho_sub {δ : ℝ} (hδ : 0 < δ) {u : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (x : ℂ) : Integrable (fun y => u y * rho δ (y - x)) := by
  have hg : Continuous fun y : ℂ => rho δ (y - x) :=
    (contDiff_rho δ).continuous.comp (continuous_id.sub continuous_const)
  have hcs : HasCompactSupport fun y : ℂ => rho δ (y - x) :=
    (hasCompactSupport_rho hδ).comp_homeomorph (Homeomorph.subRight x)
  simpa using hu.integrable_smul_right_of_hasCompactSupport hg hcs

end SandierSerfaty.Weyl

end
