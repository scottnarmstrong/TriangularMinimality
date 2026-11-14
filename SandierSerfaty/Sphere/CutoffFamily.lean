/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.GreenCutoff

/-!
# Large cutoffs

`Sphere.cutoffR R x = χ₁(x / R)` for a fixed smooth bump `χ₁` (`= 1` on the unit disc, `= 0` outside the
disc of radius `2`): `0 ≤ cutoffR R ≤ 1`, `cutoffR R = 1` on `‖x‖ ≤ R`, `= 0` on `‖x‖ ≥ 2R`, and
`‖∇ cutoffR R‖ ≤ K / R` with an absolute constant `K` (`Sphere.exists_norm_fderiv_cutoffR_le`).
-/

open Filter Topology
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem bump_nonneg {ρ : ℝ} (hρ : 0 < ρ) (c x : ℂ) : 0 ≤ bump ρ hρ c x :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).nonneg

theorem bump_le_one {ρ : ℝ} (hρ : 0 < ρ) (c x : ℂ) : bump ρ hρ c x ≤ 1 :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).le_one

/-- The large cutoff `χ₁(x / R)`. -/
@[expose] noncomputable def cutoffR (R : ℝ) (x : ℂ) : ℝ := bump 1 one_pos 0 ((R⁻¹ : ℝ) • x)

theorem contDiff_cutoffR (R : ℝ) : ContDiff ℝ ∞ (cutoffR R) := by
  have h : ContDiff ℝ ∞ (fun y : ℂ => (R⁻¹ : ℝ) • y) := contDiff_id.const_smul _
  exact (contDiff_bump one_pos 0).comp h

theorem cutoffR_nonneg (R : ℝ) (x : ℂ) : 0 ≤ cutoffR R x := bump_nonneg one_pos 0 _

theorem cutoffR_le_one (R : ℝ) (x : ℂ) : cutoffR R x ≤ 1 := bump_le_one one_pos 0 _

theorem cutoffR_eq_one {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : ‖x‖ ≤ R) : cutoffR R x = 1 := by
  unfold cutoffR
  refine bump_eq_one one_pos ?_
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  rw [inv_mul_le_iff₀ hR]; linarith

theorem cutoffR_eq_zero {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : 2 * R ≤ ‖x‖) : cutoffR R x = 0 := by
  unfold cutoffR
  refine bump_eq_zero one_pos ?_
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), le_inv_mul_iff₀ hR]
  linarith

theorem cutoffR_hasCompactSupport {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoffR R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun x hx => ?_
  refine cutoffR_eq_zero hR ?_
  by_contra hlt
  exact hx (by simpa using (not_le.1 hlt).le)

theorem exists_norm_fderiv_bump_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖fderiv ℝ (bump 1 one_pos (0 : ℂ)) y‖ ≤ K := by
  have hc : Continuous (fderiv ℝ (bump 1 one_pos (0 : ℂ))) :=
    (contDiff_bump one_pos 0).continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support
    ((bump_hasCompactSupport one_pos 0).fderiv ℝ)
  exact ⟨max K 0, le_max_right _ _, fun y => (hK y).trans (le_max_left _ _)⟩

theorem norm_fderiv_cutoffR_le {R : ℝ} (hR : 0 < R) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ (bump 1 one_pos (0 : ℂ)) y‖ ≤ K) (x : ℂ) :
    ‖fderiv ℝ (cutoffR R) x‖ ≤ K / R := by
  have hd : HasFDerivAt (cutoffR R)
      ((fderiv ℝ (bump 1 one_pos (0 : ℂ)) ((R⁻¹ : ℝ) • x)).comp ((R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ)) x := by
    have h1 : HasFDerivAt (fun y : ℂ => (R⁻¹ : ℝ) • y) ((R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ) x :=
      (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (R⁻¹ : ℝ)
    have h2 : HasFDerivAt (bump 1 one_pos (0 : ℂ)) (fderiv ℝ (bump 1 one_pos (0 : ℂ)) ((R⁻¹ : ℝ) • x))
        ((R⁻¹ : ℝ) • x) :=
      (((contDiff_bump one_pos 0).differentiable (by simp)) _).hasFDerivAt
    exact h2.comp x h1
  rw [hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : ‖(R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ‖ ≤ R⁻¹ := by
    refine (norm_smul _ _).trans_le ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ R⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_pos.2 hR).le
      _ = R⁻¹ := mul_one _
  calc ‖fderiv ℝ (bump 1 one_pos (0 : ℂ)) ((R⁻¹ : ℝ) • x)‖ * ‖(R⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ‖
      ≤ K * R⁻¹ := mul_le_mul (hK _) this (norm_nonneg _)
        ((norm_nonneg _).trans (hK 0))
    _ = K / R := by rw [div_eq_mul_inv]

theorem cutoffR_eventuallyEq_one {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : ‖x‖ < R) :
    cutoffR R =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < R - ‖x‖)] with y hy
  refine cutoffR_eq_one hR ?_
  have h1 : ‖y - x‖ < R - ‖x‖ := by simpa [dist_eq_norm] using hy
  have h2 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    calc ‖y‖ = ‖(y - x) + x‖ := by ring_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
  linarith

theorem cutoffR_eventuallyEq_zero {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : 2 * R < ‖x‖) :
    cutoffR R =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < ‖x‖ - 2 * R)] with y hy
  refine cutoffR_eq_zero hR ?_
  have h1 : ‖y - x‖ < ‖x‖ - 2 * R := by simpa [dist_eq_norm] using hy
  have h2 : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
    calc ‖x‖ = ‖y - (y - x)‖ := by ring_nf
      _ ≤ ‖y‖ + ‖y - x‖ := norm_sub_le _ _
  linarith

end Sphere

end SandierSerfaty

end
