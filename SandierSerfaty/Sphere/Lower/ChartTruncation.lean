/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Constants
public import SandierSerfaty.Sphere.TruncationIdentity
public import SandierSerfaty.Screening.TruncDiff

/-!
# Truncation of the chart energy at depth radii (sphere note, Lemma 6.10(i), abstract chart form)

Let `D = B(0, ρ)`, `Z ⊂ D` a `1`-separated finite set, `H` admissible on `(D, Z)` with `ΔH = 2π ϱ` off `Z`,
`0 ≤ ϱ ≤ M`, and `α p = min (1/4, (ρ - |p|)/2)`.  Then
`W_D(H) = ½ ∫_D |∇H_α|² + π ∑ log α_p - 2π ∑ ∫_{B(p, α_p)} f_{α_p}(· - p) ϱ`
(`Lower.chart_truncation_eq`) and `W_D(H) ≥ ½ ∫_D |∇H_α|² + ∑_p [π log (1/4) - π log₊ (1 / (2 (ρ - |p|)))] - |Z| π² M / 16`
(`Lower.chart_truncation_ge`).
-/

open MeasureTheory Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The truncation radius `α_p = min (1/4, (ρ - |p|)/2)` in the disc `B(0, ρ)`. -/
@[expose] noncomputable def depthRadius (ρ : ℝ) (p : ℂ) : ℝ := min (1 / 4) ((ρ - ‖p‖) / 2)

theorem depthRadius_pos {ρ : ℝ} {p : ℂ} (hp : ‖p‖ < ρ) : 0 < depthRadius ρ p :=
  lt_min (by norm_num) (by linarith)

theorem depthRadius_le_quarter (ρ : ℝ) (p : ℂ) : depthRadius ρ p ≤ 1 / 4 := min_le_left _ _

theorem integral_truncLog_ball_mul_le {α M : ℝ} (hα : 0 < α) {p : ℂ} {ϱ : ℂ → ℝ}
    (hϱ : ContinuousOn ϱ (ball p α)) (h0 : ∀ x ∈ ball p α, 0 ≤ ϱ x)
    (hM : ∀ x ∈ ball p α, ϱ x ≤ M) :
    ∫ x in ball p α, truncLog α (x - p) * ϱ x ≤ M * (Real.pi * α ^ 2 / 2) := by
  have hint : Integrable (truncLog α) volume := Screening.integrable_truncLog hα
  have hint' : Integrable (fun x : ℂ => truncLog α (x - p)) volume := hint.comp_sub_right p
  have hsupp : ∀ x ∉ ball p α, truncLog α (x - p) = 0 := by
    intro x hx
    rw [mem_ball, dist_eq_norm, not_lt] at hx
    exact Screening.truncLog_eq_zero hα hx
  have hMi : IntegrableOn (fun x : ℂ => M * truncLog α (x - p)) (ball p α) :=
    (hint'.const_mul M).integrableOn
  have hmeas : AEStronglyMeasurable (fun x : ℂ => truncLog α (x - p) * ϱ x)
      (volume.restrict (ball p α)) :=
    ((Screening.measurable_truncLog α).comp (measurable_id.sub_const p)).aestronglyMeasurable.mul
      (hϱ.aestronglyMeasurable isOpen_ball.measurableSet)
  have hle : ∀ x ∈ ball p α, truncLog α (x - p) * ϱ x ≤ M * truncLog α (x - p) := by
    intro x hx
    have := Screening.truncLog_nonneg α (x - p)
    nlinarith [hM x hx]
  have hI : IntegrableOn (fun x : ℂ => truncLog α (x - p) * ϱ x) (ball p α) := by
    refine hMi.mono' hmeas ?_
    refine (ae_restrict_iff' isOpen_ball.measurableSet).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have h1 := Screening.truncLog_nonneg α (x - p)
    rw [Real.norm_of_nonneg (mul_nonneg h1 (h0 x hx))]
    exact hle x hx
  calc ∫ x in ball p α, truncLog α (x - p) * ϱ x
      ≤ ∫ x in ball p α, M * truncLog α (x - p) := setIntegral_mono_on hI hMi isOpen_ball.measurableSet hle
    _ = M * ∫ x, truncLog α (x - p) := by
        rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx; exact hsupp x hx
    _ = M * (Real.pi * α ^ 2 / 2) := by rw [Screening.integral_truncLog_sub hα]

variable {ρ : ℝ} {Z : Finset ℂ} {H ϱ : ℂ → ℝ}

theorem depthRadius_closedBall_subset (hρ : ∀ p ∈ Z, ‖p‖ < ρ) {p : ℂ} (hp : p ∈ Z) :
    closedBall p (depthRadius ρ p) ⊆ ball 0 ρ := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  have h1 : depthRadius ρ p ≤ (ρ - ‖p‖) / 2 := min_le_right _ _
  have := hρ p hp
  rw [mem_ball, dist_zero_right]
  have h2 := norm_sub_norm_le x p
  have h3 : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
    have := norm_add_le (x - p) p
    simpa using this
  linarith

theorem depthRadius_disjoint (hsep : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → 1 ≤ ‖p - q‖) {p q : ℂ} (hp : p ∈ Z)
    (hq : q ∈ Z) (hpq : p ≠ q) :
    Disjoint (closedBall p (depthRadius ρ p)) (closedBall q (depthRadius ρ q)) := by
  apply closedBall_disjoint_closedBall
  rw [dist_eq_norm]
  have := hsep p hp q hq hpq
  have h1 := depthRadius_le_quarter ρ p
  have h2 := depthRadius_le_quarter ρ q
  linarith

/-- **Truncation identity at the depth radii** (Lemma 6.10(i), exact form). -/
theorem chart_truncation_eq (hH : PunctureAdmissible (ball 0 ρ) Z H)
    (hϱ : ContDiffOn ℝ 1 ϱ (ball 0 ρ))
    (hΔ : ∀ x ∈ ball (0 : ℂ) ρ, x ∉ (Z : Set ℂ) → Laplacian.laplacian H x = 2 * Real.pi * ϱ x)
    (hsep : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → 1 ≤ ‖p - q‖) :
    punctureEnergy (ball 0 ρ) Z H =
      (1 / 2 : ℝ) * (∫ x in ball (0 : ℂ) ρ,
          ‖gradient (fun y => H y - ∑ p ∈ Z, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2) +
        Real.pi * ∑ p ∈ Z, Real.log (depthRadius ρ p) -
        2 * Real.pi * ∑ p ∈ Z, ∫ x in ball p (depthRadius ρ p),
          truncLog (depthRadius ρ p) (x - p) * ϱ x := by
  have hρ : ∀ p ∈ Z, ‖p‖ < ρ := fun p hp => by
    have := hH.subset hp
    simpa using this
  exact truncation_identity hH hϱ hΔ (fun p hp => depthRadius_pos (hρ p hp))
    (fun p hp => depthRadius_closedBall_subset hρ hp) fun p hp q hq hpq =>
      depthRadius_disjoint hsep hp hq hpq

/-- **Lower bound for the chart energy** (Lemma 6.10(i), inequality form), for `0 ≤ ϱ ≤ M`. -/
theorem chart_truncation_ge {M : ℝ} (hH : PunctureAdmissible (ball 0 ρ) Z H)
    (hϱ : ContDiffOn ℝ 1 ϱ (ball 0 ρ))
    (hΔ : ∀ x ∈ ball (0 : ℂ) ρ, x ∉ (Z : Set ℂ) → Laplacian.laplacian H x = 2 * Real.pi * ϱ x)
    (hsep : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → 1 ≤ ‖p - q‖)
    (h0 : ∀ x ∈ ball (0 : ℂ) ρ, 0 ≤ ϱ x) (hM : ∀ x ∈ ball (0 : ℂ) ρ, ϱ x ≤ M) :
    (1 / 2 : ℝ) * (∫ x in ball (0 : ℂ) ρ,
          ‖gradient (fun y => H y - ∑ p ∈ Z, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2) +
        ∑ p ∈ Z, (Real.pi * Real.log (1 / 4) -
          Real.pi * logPlus (1 / (2 * (ρ - ‖p‖)))) - Z.card * (Real.pi ^ 2 * M / 16) ≤
      punctureEnergy (ball 0 ρ) Z H := by
  have hρ : ∀ p ∈ Z, ‖p‖ < ρ := fun p hp => by
    have := hH.subset hp
    simpa using this
  rw [chart_truncation_eq hH hϱ hΔ hsep]
  have hpi := Real.pi_pos
  have hlog : ∀ p ∈ Z, Real.pi * Real.log (1 / 4) - Real.pi * logPlus (1 / (2 * (ρ - ‖p‖))) ≤
      Real.pi * Real.log (depthRadius ρ p) := by
    intro p hp
    have := log_min_ge (d := ρ - ‖p‖) (by linarith [hρ p hp])
    have e : depthRadius ρ p = min (1 / 4) ((ρ - ‖p‖) / 2) := rfl
    rw [e]
    nlinarith
  have hint : ∀ p ∈ Z, ∫ x in ball p (depthRadius ρ p), truncLog (depthRadius ρ p) (x - p) * ϱ x ≤
      M * (Real.pi * (1 / 4) ^ 2 / 2) := by
    intro p hp
    have hα := depthRadius_pos (hρ p hp)
    have hsubset : ball p (depthRadius ρ p) ⊆ ball 0 ρ :=
      ball_subset_closedBall.trans (depthRadius_closedBall_subset hρ hp)
    refine (integral_truncLog_ball_mul_le hα (hϱ.continuousOn.mono hsubset) (fun x hx => h0 x (hsubset hx))
      (fun x hx => hM x (hsubset hx))).trans ?_
    have hM0 : 0 ≤ M := by
      have := hM p (by simpa using hρ p hp); have := h0 p (by simpa using hρ p hp); linarith
    have := depthRadius_le_quarter ρ p
    have h2 : depthRadius ρ p ^ 2 ≤ (1 / 4) ^ 2 := by gcongr
    nlinarith [mul_nonneg hM0 hpi.le]
  have hsum := Finset.sum_le_sum hlog
  have hsum2 := Finset.sum_le_sum hint
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum2
  have e : 2 * Real.pi * (Z.card * (M * (Real.pi * (1 / 4) ^ 2 / 2))) =
      Z.card * (Real.pi ^ 2 * M / 16) := by ring
  have h3 := mul_le_mul_of_nonneg_left hsum2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  rw [e] at h3
  linarith

end Lower

end Sphere

end SandierSerfaty

end
