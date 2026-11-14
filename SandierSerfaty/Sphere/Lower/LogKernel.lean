/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.RadialGreen
public import SandierSerfaty.Sphere.GreenPlane
public import SandierSerfaty.Sphere.ChartIntegrable

/-!
# The logarithmic kernel and the Laplacian of a test function

* `Lower.integrableOn_log_norm_sub`: `log ‖· - p‖` is integrable on every bounded set.
* `Lower.integral_lap_eq_zero`: `∫ Δφ = 0` for `φ` smooth with compact support.
* `Lower.integral_log_norm_sub_mul_lap`: `∫ log ‖x - p‖ Δφ(x) dx = 2π φ(p)` (`Δ log ‖· - p‖ = 2π δ_p`), for `φ` smooth
  with compact support.  It is the radial Green identity (`Sphere.circleAverage_sub_eq_integral`) with a radius
  large enough that `φ` vanishes on the circle.
* `Lower.integral_truncLog_mul_lap`: `∫ f_α(x - p) Δφ(x) dx = 2π (⨍_{∂B(p,α)} φ - φ(p))`.
-/

open MeasureTheory Set Metric Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem integrableOn_log_norm_sub (p : ℂ) {R : ℝ} :
    IntegrableOn (fun x : ℂ => Real.log ‖x - p‖) (closedBall 0 R) := by
  have h := (integrable_log_dens p).integrableOn (s := closedBall (0 : ℂ) R)
  have hpi := Real.pi_pos
  set δ : ℝ := 1 / (Real.pi * (1 + R ^ 2) ^ 2) with hδ
  have hδpos : 0 < δ := by positivity
  have hdens : ∀ y ∈ closedBall (0 : ℂ) R, δ ≤ dens y := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    rw [dens_eq]
    have h1 : (1 + ‖y‖ ^ 2) ≤ 1 + R ^ 2 := by
      have := norm_nonneg y
      nlinarith
    have h2 : (1 + ‖y‖ ^ 2) ^ 2 ≤ (1 + R ^ 2) ^ 2 := by
      have := norm_nonneg y
      gcongr
    rw [hδ]
    exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hm : AEStronglyMeasurable (fun x : ℂ => Real.log ‖x - p‖) (volume.restrict (closedBall 0 R)) :=
    (Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub_const p))).aestronglyMeasurable
  have hh : IntegrableOn (fun x : ℂ => δ⁻¹ * |Real.log ‖p - x‖ * dens x|) (closedBall 0 R) :=
    (h.norm.const_mul δ⁻¹)
  refine hh.mono' hm ?_
  refine (ae_restrict_iff' measurableSet_closedBall).2 (Filter.Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (dens_pos y), norm_sub_rev p y, ← mul_assoc]
  have := hdens y hy
  have hl := abs_nonneg (Real.log ‖y - p‖)
  have hd := dens_pos y
  calc |Real.log ‖y - p‖| = δ⁻¹ * (δ * |Real.log ‖y - p‖|) := by field_simp
    _ ≤ δ⁻¹ * (|Real.log ‖y - p‖| * dens y) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hδpos.le)
        nlinarith [mul_le_mul_of_nonneg_left this hl]
    _ = _ := by ring

theorem integral_lap_eq_zero {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ x, Δ φ x = 0 := by
  have h1 : ∀ x, Δ φ x = Weyl.pd 1 (Weyl.pd 1 φ) x + Weyl.pd Complex.I (Weyl.pd Complex.I φ) x :=
    fun x => Weyl.lap_eq_pd ((hφ.of_le (by norm_cast)).contDiffAt)
  have hpd : ∀ v : ℂ, ContDiff ℝ 1 (Weyl.pd v φ) := fun v =>
    Weyl.contDiff_pd (m := 1) hφ (by norm_cast) v
  have hpc : ∀ v : ℂ, HasCompactSupport (Weyl.pd v φ) := fun v => hc.fderiv_apply ℝ v
  have h2 : ∀ v : ℂ, ∫ x, Weyl.pd v (Weyl.pd v φ) x = 0 := fun v =>
    integral_fderiv_apply_eq_zero (hpd v) (hpc v) v
  have hi : ∀ v : ℂ, Integrable (Weyl.pd v (Weyl.pd v φ)) := fun v =>
    ((Weyl.contDiff_pd (m := 0) (hpd v) (by norm_cast) v).continuous).integrable_of_hasCompactSupport
      ((hpc v).fderiv_apply ℝ v)
  simp only [h1]
  rw [integral_add (hi 1) (hi Complex.I), h2, h2, add_zero]

theorem contDiff_lap {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (fun x => Δ φ x) := by
  have h1 : ∀ x, Δ φ x = Weyl.pd 1 (Weyl.pd 1 φ) x + Weyl.pd Complex.I (Weyl.pd Complex.I φ) x :=
    fun x => Weyl.lap_eq_pd ((hφ.of_le (by norm_cast)).contDiffAt)
  have hp : ∀ v : ℂ, ContDiff ℝ ∞ (Weyl.pd v φ) := fun v => Weyl.contDiff_pd (m := ∞) hφ (by simp) v
  have e : (fun x => Δ φ x) = fun x =>
      Weyl.pd 1 (Weyl.pd 1 φ) x + Weyl.pd Complex.I (Weyl.pd Complex.I φ) x := funext h1
  rw [e]
  exact (Weyl.contDiff_pd (m := ∞) (hp 1) (by simp) 1).add (Weyl.contDiff_pd (m := ∞) (hp Complex.I) (by simp) Complex.I)

/-- **Laplacian of the truncated logarithm**: `∫ f_α(x - p) Δφ(x) dx = 2π (⨍_{∂B(p, α)} φ - φ(p))`. -/
theorem integral_truncLog_mul_lap {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) {α : ℝ} (hα : 0 < α) (p : ℂ) :
    ∫ x, truncLog α (x - p) * Δ φ x = 2 * Real.pi * (Real.circleAverage φ p α - φ p) := by
  have hpi := Real.pi_pos
  have hlap := contDiff_lap hφ
  have key := circleAverage_sub_eq_integral (u := φ) (ϱ := fun x => Δ φ x / (2 * Real.pi)) (p := p) hα
    ((hφ.of_le (by norm_cast)).contDiffAt)
    (fun x _ _ => (hφ.of_le (by norm_cast)).contDiffAt)
    ((hlap.continuous.div_const _).continuousOn)
    (fun x _ _ => by field_simp)
  have hsupp : ∀ x ∉ ball p α, truncLog α (x - p) * Δ φ x = 0 := by
    intro x hx
    rw [mem_ball, dist_eq_norm, not_lt] at hx
    rw [Screening.truncLog_eq_zero hα hx, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have : ∫ x in ball p α, truncLog α (x - p) * Δ φ x =
      2 * Real.pi * ∫ x in ball p α, truncLog α (x - p) * (Δ φ x / (2 * Real.pi)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    field_simp
  rw [this, ← key]

/-- **`Δ log ‖· - p‖ = 2π δ_p`**: `∫ log ‖x - p‖ Δφ(x) dx = 2π φ(p)` for `φ` smooth with compact support. -/
theorem integral_log_norm_sub_mul_lap {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (p : ℂ) : ∫ x, Real.log ‖x - p‖ * Δ φ x = 2 * Real.pi * φ p := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set α : ℝ := |R| + ‖p‖ + 1 with hα
  have hα1 : 1 ≤ α := by have := abs_nonneg R; have := norm_nonneg p; linarith
  have hα0 : 0 < α := by linarith
  have hvan : ∀ x : ℂ, α ≤ ‖x - p‖ → φ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun h => by
      have := hR h
      rw [mem_closedBall_zero_iff] at this
      have h3 : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := norm_sub_le x p
      have := le_abs_self R
      linarith
    exact image_eq_zero_of_notMem_tsupport hx'
  have hca : Real.circleAverage φ p α = 0 := by
    rw [Real.circleAverage_def]
    have : ∀ θ : ℝ, φ (circleMap p α θ) = 0 := fun θ => by
      apply hvan
      rw [circleMap, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0.le,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [this]
  have h1 := integral_truncLog_mul_lap hφ hα0 p
  rw [hca, zero_sub] at h1
  -- the integrand, away from the support
  have hlap0 : ∀ x : ℂ, α ≤ ‖x - p‖ → Δ φ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun h => by
      have := hR h
      rw [mem_closedBall_zero_iff] at this
      have h3 : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := norm_sub_le x p
      have := le_abs_self R
      linarith
    exact Weyl.lap_eq_zero_of_notMem_tsupport hx'
  have hlapc : HasCompactSupport (fun x => Δ φ x) := by
    refine hc.mono' ?_
    intro x hx
    by_contra hx'
    exact hx (Weyl.lap_eq_zero_of_notMem_tsupport hx')
  have hint1 : Integrable (fun x : ℂ => Real.log ‖x - p‖ * Δ φ x) := by
    have hI : IntegrableOn (fun x : ℂ => Real.log ‖x - p‖ * Δ φ x) (closedBall 0 R) :=
      (integrableOn_log_norm_sub p).mul_continuousOn (contDiff_lap hφ).continuous.continuousOn
        (isCompact_closedBall _ _)
    refine hI.integrable_of_forall_notMem_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport φ := fun h => hx (hR h)
    rw [Weyl.lap_eq_zero_of_notMem_tsupport hx', mul_zero]
  have hint2 : Integrable (fun x : ℂ => Real.log α * Δ φ x) :=
    ((contDiff_lap hφ).continuous.const_mul _).integrable_of_hasCompactSupport hlapc.mul_left
  have heq : ∀ x : ℂ, truncLog α (x - p) * Δ φ x = Real.log α * Δ φ x - Real.log ‖x - p‖ * Δ φ x := by
    intro x
    by_cases hx : α ≤ ‖x - p‖
    · rw [hlap0 x hx]; ring
    · rw [not_le] at hx
      unfold truncLog
      rw [max_eq_left]
      · ring
      · by_cases h0 : x - p = 0
        · simp [h0, Real.log_nonneg hα1]
        · have : Real.log ‖x - p‖ ≤ Real.log α := Real.log_le_log (norm_pos_iff.2 h0) hx.le
          linarith
  simp only [heq] at h1
  rw [integral_sub hint2 hint1, integral_const_mul, integral_lap_eq_zero hφ hc] at h1
  linarith

end Lower

end Sphere

end SandierSerfaty

end
