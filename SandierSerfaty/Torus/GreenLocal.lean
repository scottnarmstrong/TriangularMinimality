/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.GreenOne
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The local form of the single-charge Green function

For the theta-product Green function `greenOne p τ`, the regular part at the lattice point `0` is
smooth: `greenOne p τ z = r z - log ‖z‖` near `0` with `r` of class `C^∞` at `0`
(`SandierSerfaty.Torus.greenOne_localForm`). This is the "explicit local form near each charge" used
by the pair-energy identity: `θ(w) = w q(w)` with `q = dslope θ 0` entire and `q 0 = θ'(0) ≠ 0`.
-/

open Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- `θ(w) = w · q(w)` with `q` entire and `q 0 ≠ 0`. -/
theorem exists_theta_factor {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ q 0 ≠ 0 ∧ ∀ w, theta τ w = w * q w := by
  refine ⟨dslope (theta τ) 0, ?_, ?_, ?_⟩
  · rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem, differentiableOn_univ]
    exact differentiable_theta hτ
  · rw [dslope_same, (hasDerivAt_theta_zero hτ).deriv]
    have := thetaR_one_ne_zero hτ
    simp [Real.pi_ne_zero, this]
  · intro w
    have := sub_smul_dslope (theta τ) 0 w
    simpa [theta_zero] using this.symm

/-- The regular part of `greenOne` at `0` is smooth: `greenOne p τ z = r z - log ‖z‖` near `0`. -/
theorem greenOne_localForm {τ p : ℂ} (hτ : 0 < τ.im) (hp : p ≠ 0) :
    ∃ r : ℂ → ℝ, ContDiffAt ℝ ∞ r 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ), greenOne p τ z = r z - Real.log ‖z‖ := by
  obtain ⟨q, hqd, hq0, hθq⟩ := exists_theta_factor hτ
  have hqc : ContDiff ℝ ∞ fun z : ℂ => q (z / p) :=
    ((hqd.comp (differentiable_id.div_const p)).contDiff (n := ∞)).restrict_scalars ℝ
  have hq0' : q (0 / p) ≠ 0 := by simpa using hq0
  have hlog : ContDiffAt ℝ ∞ (fun z : ℂ => Real.log ‖q (z / p)‖) 0 :=
    (hqc.contDiffAt.norm ℝ hq0').log (norm_ne_zero_iff.2 hq0')
  have hL := (imDiv p).contDiff (n := ∞) (𝕜 := ℝ)
  have hquad : ContDiffAt ℝ ∞
      (fun x : ℂ => Real.pi / τ.im * imDiv p x ^ 2 + Real.pi * imDiv p x) 0 :=
    (((hL.pow 2).const_smul (Real.pi / τ.im)).add (hL.const_smul Real.pi)).contDiffAt
  refine ⟨fun z => Real.log ‖p‖ - Real.log ‖q (z / p)‖ +
    (Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z), ?_, ?_⟩
  · exact (contDiffAt_const.sub hlog).add hquad
  · have hmap : Tendsto (fun z : ℂ => z / p) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun z : ℂ => z / p) (𝓝 0) (𝓝 (0 / p)) :=
          (continuous_id.div_const p).tendsto 0
        rw [zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa [hp] using hz
    filter_upwards [hmap.eventually (eventually_theta_ne_zero hτ), self_mem_nhdsWithin]
      with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [greenOne_eq hz]
    have hzp : z / p ≠ 0 := div_ne_zero hz0' hp
    have hqz : q (z / p) ≠ 0 := by
      intro h; apply hz; rw [hθq, h, mul_zero]
    have e1 : Real.log ‖theta τ (z / p)‖ =
        Real.log ‖z‖ - Real.log ‖p‖ + Real.log ‖q (z / p)‖ := by
      rw [hθq, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hzp) (norm_ne_zero_iff.2 hqz), norm_div,
        Real.log_div (norm_ne_zero_iff.2 hz0') (norm_ne_zero_iff.2 hp)]
    rw [e1]
    ring


/-- Reflection of the theta product: `θ(-w) = -e(w) θ(w)`. -/
theorem theta_neg (τ w : ℂ) : theta τ (-w) = -eF w * theta τ w := by
  have hyy : eF w * eF (-w) = 1 := by rw [eF_neg]; exact mul_inv_cancel₀ (eF_ne_zero w)
  unfold theta
  rw [neg_neg]
  linear_combination (-(thetaR (eF τ) (eF w) * thetaR (eF τ) (eF (-w)))) * hyy

/-- The theta Green function is even. -/
theorem thetaGreen0_neg (τ w : ℂ) : thetaGreen0 τ (-w) = thetaGreen0 τ w := by
  unfold thetaGreen0
  by_cases h : theta τ w = 0
  · have : theta τ (-w) = 0 := by rw [theta_neg, h, mul_zero]
    simp [h, this]
  · have h' : theta τ (-w) ≠ 0 := by
      rw [theta_neg]; exact mul_ne_zero (neg_ne_zero.2 (eF_ne_zero w)) h
    simp only [h, h', ite_false]
    unfold thetaGreen
    have e1 : Real.log ‖theta τ (-w)‖ = -(2 * Real.pi * w.im) + Real.log ‖theta τ w‖ := by
      rw [theta_neg, norm_mul, norm_neg, norm_eF,
        Real.log_mul (Real.exp_pos _).ne' (norm_ne_zero_iff.2 h), Real.log_exp]
    rw [e1, Complex.neg_im]
    ring

theorem greenOne_neg {τ p : ℂ} (z : ℂ) : greenOne p τ (-z) = greenOne p τ z := by
  unfold greenOne
  rw [neg_div, thetaGreen0_neg]

end Torus

end SandierSerfaty

end
