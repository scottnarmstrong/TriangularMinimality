/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PolarAnnulus
public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Circle means and the integral of the truncated logarithm

* `integral_circle_eq`: if `Δ v = 2π` on `B(0, R)` and `v` is smooth there, then for `0 < ρ < R`
  `∫_{-π}^{π} v(ρ e^{iθ}) dθ = 2π (v 0 + π ρ² / 2)`. This is the mean value property for the harmonic
  function `v - (2π/4)‖·‖²`.
* `integral_truncLog`: `∫_ℂ f_η = π η² / 2`, where `f_η = (log η - log ‖·‖)₊`.
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

theorem circleMap_zero_eq (ρ θ : ℝ) : circleMap 0 ρ θ = (ρ : ℂ) * dir θ := by
  simp only [circleMap, dir, zero_add, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem dir_add_two_pi (θ : ℝ) : dir (θ + 2 * Real.pi) = dir θ := by
  simp [dir, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **Mean value property for `Δ v = 2π`.** -/
theorem integral_circle_eq {v : ℂ → ℝ} {R ρ : ℝ} (hv : ContDiffOn ℝ ∞ v (ball 0 R))
    (hΔ : ∀ x ∈ ball 0 R, Δ v x = 2 * Real.pi) (hρ : 0 < ρ) (hρR : ρ < R) :
    ∫ θ in Ioo (-Real.pi) Real.pi, v ((ρ : ℂ) * dir θ) =
      2 * Real.pi * (v 0 + Real.pi / 2 * ρ ^ 2) := by
  set q : ℂ → ℝ := fun y => 2 * Real.pi / 4 * ‖y - 0‖ ^ 2 with hq
  set w : ℂ → ℝ := fun y => v y - q y with hw
  have hqs : ContDiff ℝ ∞ q :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hharm : HarmonicOnNhd w (closedBall 0 |ρ|) := by
    intro x hx
    have hxb : x ∈ ball 0 R := by
      rw [mem_closedBall_zero_iff, abs_of_pos hρ] at hx
      rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hx hρR
    refine ⟨?_, ?_⟩
    · exact ((hv.contDiffAt (isOpen_ball.mem_nhds hxb)).of_le (by norm_num)).sub
        ((hqs.of_le (by norm_num)).contDiffAt)
    · filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
      have hv2 : ContDiffAt ℝ 2 v y :=
        (hv.contDiffAt (isOpen_ball.mem_nhds hy)).of_le (by norm_num)
      have := ContDiffAt.laplacian_sub hv2 ((hqs.of_le (by norm_num)).contDiffAt (x := y))
      have e : w = v - q := rfl
      rw [e, this, hΔ y hy, hq, Weyl.lap_quadratic]
      simp
  have h0 : Real.circleAverage w 0 ρ = w 0 := hharm.circleAverage_eq
  rw [Real.circleAverage_def] at h0
  have hcmap : Continuous fun θ : ℝ => (ρ : ℂ) * dir θ := continuous_const.mul continuous_dir
  have hg : Continuous fun θ : ℝ => v ((ρ : ℂ) * dir θ) :=
    hv.continuousOn.comp_continuous hcmap (fun θ => by
      rw [mem_ball_zero_iff, norm_ofReal_mul_dir, abs_of_pos hρ]; exact hρR)
  have hwc : ∀ θ : ℝ, w (circleMap 0 ρ θ) = v ((ρ : ℂ) * dir θ) - 2 * Real.pi / 4 * ρ ^ 2 := by
    intro θ
    simp only [hw, hq, circleMap_zero_eq, sub_zero, norm_ofReal_mul_dir, abs_of_pos hρ]
  have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, w (circleMap 0 ρ θ) =
      (∫ θ in (0 : ℝ)..2 * Real.pi, v ((ρ : ℂ) * dir θ)) - 2 * Real.pi * (2 * Real.pi / 4 * ρ ^ 2) := by
    simp only [hwc]
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  have hw0 : w 0 = v 0 := by simp [hw, hq]
  rw [hw0, hint, smul_eq_mul] at h0
  have hper : Function.Periodic (fun θ : ℝ => v ((ρ : ℂ) * dir θ)) (2 * Real.pi) := by
    intro θ; simp only [dir_add_two_pi]
  have hshift : ∫ θ in (-Real.pi)..Real.pi, v ((ρ : ℂ) * dir θ) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, v ((ρ : ℂ) * dir θ) := by
    have := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
    exact this
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    hshift]
  have hpi := Real.pi_pos
  have Y := (inv_mul_eq_iff_eq_mul₀ (by positivity : (2 * Real.pi) ≠ 0)).1 h0
  linear_combination Y

theorem continuous_circle {v : ℂ → ℝ} {R ρ : ℝ} (hv : ContDiffOn ℝ ∞ v (ball 0 R)) (hρ : 0 < ρ)
    (hρR : ρ < R) : Continuous fun θ : ℝ => v ((ρ : ℂ) * dir θ) :=
  hv.continuousOn.comp_continuous (continuous_const.mul continuous_dir) (fun θ => by
    rw [mem_ball_zero_iff, norm_ofReal_mul_dir, abs_of_pos hρ]; exact hρR)

/-- **The radial-derivative integral over an annulus**, for `Δ v = 2π`:
`∫_{ε ≤ ‖x‖ < ρ} ‖x‖⁻² ∂v(x)[x] = π² (ρ² - ε²)`. -/
theorem integral_fderiv_div_sq_annulus_eq {v : ℂ → ℝ} {R ε ρ : ℝ} (hv : ContDiffOn ℝ ∞ v (ball 0 R))
    (hΔ : ∀ x ∈ ball (0 : ℂ) R, Δ v x = 2 * Real.pi) (hε : 0 < ε) (hερ : ε < ρ) (hρR : ρ < R) :
    ∫ x in {x : ℂ | ε ≤ ‖x‖ ∧ ‖x‖ < ρ}, (‖x‖ ^ 2)⁻¹ * fderiv ℝ v x x =
      Real.pi ^ 2 * (ρ ^ 2 - ε ^ 2) := by
  rw [integral_fderiv_div_sq_annulus (hv.of_le (by norm_num)) hε hερ hρR]
  have hρ : 0 < ρ := hε.trans hερ
  have i1 : IntegrableOn (fun θ : ℝ => v ((ρ : ℂ) * dir θ)) (Ioo (-Real.pi) Real.pi) :=
    (continuous_circle hv hρ hρR).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have i2 : IntegrableOn (fun θ : ℝ => v ((ε : ℂ) * dir θ)) (Ioo (-Real.pi) Real.pi) :=
    (continuous_circle hv hε (hερ.trans hρR)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [integral_sub i1 i2, integral_circle_eq hv hΔ hρ hρR,
    integral_circle_eq hv hΔ hε (hερ.trans hρR)]
  ring

/-- The integral of the truncated logarithm: `∫ f_η = π η² / 2`. -/
theorem integral_truncLog {η : ℝ} (hη : 0 < η) :
    ∫ x : ℂ, truncLog η x = Real.pi * η ^ 2 / 2 := by
  set S : Set ℂ := {x | ‖x‖ ∈ Ioo 0 η} with hS
  set g : ℂ → ℝ := fun x => Real.log η - Real.log ‖x‖ with hg
  have hae : truncLog η =ᵐ[volume] S.indicator g := by
    filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with x hx0
    have hx0' : x ≠ 0 := hx0
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0'
    unfold truncLog
    by_cases hlt : ‖x‖ < η
    · have hxS : x ∈ S := ⟨hxn, hlt⟩
      rw [indicator_of_mem hxS, hg]
      have : 0 ≤ Real.log η - Real.log ‖x‖ :=
        sub_nonneg.2 (Real.log_le_log hxn hlt.le)
      simp only
      rw [max_eq_left (by linarith)]
      ring
    · have hxS : x ∉ S := fun h => hlt h.2
      rw [indicator_of_notMem hxS]
      push Not at hlt
      have : Real.log η ≤ Real.log ‖x‖ := Real.log_le_log hη hlt
      rw [max_eq_right (by linarith)]
  have hSm : MeasurableSet S := measurable_norm measurableSet_Ioo
  rw [integral_congr_ae hae, integral_indicator hSm]
  have hcont : Continuous fun p : ℝ × ℝ =>
      p.1 * (Real.log η - Real.log ‖(p.1 : ℂ) * dir p.2‖) := by
    have : (fun p : ℝ × ℝ => p.1 * (Real.log η - Real.log ‖(p.1 : ℂ) * dir p.2‖)) =
        fun p => p.1 * Real.log η - p.1 * Real.log p.1 := by
      funext p
      rw [norm_ofReal_mul_dir, Real.log_abs]; ring
    rw [this]
    exact (continuous_fst.mul continuous_const).sub (Real.continuous_mul_log.comp continuous_fst)
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * g ((p.1 : ℂ) * dir p.2))
      (Ioo 0 η ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [integral_polar_radial measurableSet_Ioo (fun r hr => hr.1) hint]
  have hin : ∀ θ : ℝ, ∫ r in Ioo 0 η, r * g ((r : ℂ) * dir θ) = η ^ 2 / 4 := by
    intro θ
    have h1 : ∀ r ∈ Ioo (0 : ℝ) η, r * g ((r : ℂ) * dir θ) = r * Real.log η - r * Real.log r := by
      intro r hr
      simp only [hg, norm_ofReal_mul_dir, abs_of_pos hr.1]; ring
    rw [setIntegral_congr_fun measurableSet_Ioo h1, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hη.le]
    set F : ℝ → ℝ := fun r => r ^ 2 / 2 * Real.log η - (r ^ 2 / 2 * Real.log r - r ^ 2 / 4) with hF
    have hFc : ContinuousOn F (Icc 0 η) := by
      have : Continuous F := by
        have e : F = fun r => r ^ 2 / 2 * Real.log η - (r / 2 * (r * Real.log r) - r ^ 2 / 4) := by
          funext r; simp only [hF]; ring
        rw [e]
        exact (by fun_prop : Continuous fun r : ℝ => r ^ 2 / 2 * Real.log η).sub
          (((continuous_id.div_const 2).mul Real.continuous_mul_log).sub (by fun_prop))
      exact this.continuousOn
    have hder : ∀ r ∈ Ioo (0 : ℝ) η, HasDerivWithinAt F (r * Real.log η - r * Real.log r) (Ioi r) r := by
      intro r hr
      have hr0 : r ≠ 0 := hr.1.ne'
      have h1 : HasDerivAt (fun r : ℝ => r ^ 2 / 2 * Real.log η) (r * Real.log η) r := by
        have := ((hasDerivAt_pow 2 r).div_const 2).mul_const (Real.log η)
        convert this using 1; simp
      have h2 : HasDerivAt (fun r : ℝ => r ^ 2 / 2 * Real.log r - r ^ 2 / 4)
          (r * Real.log r) r := by
        have := (((hasDerivAt_pow 2 r).div_const 2).mul (Real.hasDerivAt_log hr0)).sub
          ((hasDerivAt_pow 2 r).div_const 4)
        convert this using 1; field_simp; ring
      exact (h1.sub h2).hasDerivWithinAt |>.congr_deriv (by ring)
    have hcI : Continuous fun r : ℝ => r * Real.log η - r * Real.log r :=
      (continuous_id.mul continuous_const).sub Real.continuous_mul_log
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hη.le hFc hder
      (hcI.intervalIntegrable _ _)]
    simp only [hF]
    simp
  simp only [hin]
  rw [integral_const_Ioo_pi]
  ring

end Torus

end SandierSerfaty

end
