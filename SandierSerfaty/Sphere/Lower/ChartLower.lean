/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.AdmissibleSmul
public import SandierSerfaty.Sphere.Lower.BlowupLaplacian
public import SandierSerfaty.Sphere.Lower.ChartTruncation
public import SandierSerfaty.Sphere.TwoChart

/-!
# The blown-up chart energy bounded below by the truncated Dirichlet energy (sphere note, Lemma 6.10(i))

For `X` injective in `ℂⁿ`, `H = blowupPot X`, `ϱ = blowupDens n`, `0 < ρ ≤ 2 s_n` with `|s xᵢ| ≠ ρ`, and the blown-up
points of `D = B(0, ρ)` `1`-separated (`Z = {s xᵢ : |s xᵢ| < ρ}`), `Lower.chartEnergy_ge`:
`W_D(H) + π ∑_{s |xᵢ| < ρ} log λ(xᵢ) ≥ ½ ∫_D |∇H_α|² - C₁ |Z| - π ∑ log₊ (1 / (2 (ρ - s|xᵢ|)))`
with `C₁ = π log 4 + π log (5/2) + π² m₊ / 16`.
-/

open MeasureTheory Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The constant `C₁` of Lemma 6.10(i). -/
@[expose] noncomputable def constC1 : ℝ :=
  Real.pi * Real.log 4 + Real.pi * Real.log (5 / 2) + Real.pi ^ 2 * mPlus / 16

theorem constC1_nonneg : 0 ≤ constC1 := by
  unfold constC1
  have hp := Real.pi_pos
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h5 : 0 ≤ Real.log (5 / 2) := Real.log_nonneg (by norm_num)
  have := mPlus_pos
  positivity

/-- The inner points `T = {i | s |xᵢ| < ρ}` (blown up) as a finset in the plane. -/
@[expose] noncomputable def innerBlown {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) : Finset ℂ :=
  (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).image fun i => blowupScale n • X i

theorem innerBlown_eq {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) :
    innerBlown X ρ = innerPunct (Finset.univ.image fun i => blowupScale n • X i) ρ := by
  unfold innerBlown
  rw [innerPunct_image (fun i => blowupScale n • X i) ρ]

theorem blowupPot_admissible {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    {ρ : ℝ} (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ) :
    PunctureAdmissible (ball (0 : ℂ) ρ) (innerBlown X ρ) (blowupPot X) := by
  have hs := blowupScale_pos hn
  have h1 := (chartPot_admissible X hX).smul hs
  rw [Set.smul_set_univ₀ hs.ne', Finset.image_image] at h1
  have h2 : PunctureAdmissible (Set.univ : Set ℂ)
      (Finset.univ.image fun i => blowupScale n • X i) (blowupPot X) := by
    have e : (fun i => blowupScale n • X i) = (fun p => blowupScale n • p) ∘ X := rfl
    rw [e]
    exact h1
  rw [innerBlown_eq]
  refine admissible_inner h2 ?_
  intro p hp
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
  exact hρ i

/-- **Lemma 6.10(i)**: lower bound of the chart energy by the truncated Dirichlet energy. -/
theorem chartEnergy_ge {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * blowupScale n) (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ)
    (hsep : ∀ i j, ‖blowupScale n • X i‖ < ρ → ‖blowupScale n • X j‖ < ρ → i ≠ j →
      1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) :
    (1 / 2 : ℝ) * (∫ x in ball (0 : ℂ) ρ, ‖gradient (fun y => blowupPot X y -
          ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2) -
        constC1 * (innerBlown X ρ).card -
        Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
      punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
        Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ),
          Real.log (lam (X i)) := by
  classical
  have hs := blowupScale_pos hn
  have hadm := blowupPot_admissible hn X hX hρ
  have hmem : ∀ p ∈ innerBlown X ρ, ∃ i, ‖blowupScale n • X i‖ < ρ ∧ blowupScale n • X i = p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩
  have hΔ : ∀ x ∈ ball (0 : ℂ) ρ, x ∉ (↑(innerBlown X ρ) : Set ℂ) →
      Laplacian.laplacian (blowupPot X) x = 2 * Real.pi * blowupDens n x := by
    intro x hx hxP
    refine laplacian_blowupPot hn X fun i h => ?_
    rcases lt_or_gt_of_ne (hρ i) with hlt | hgt
    · exact hxP (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩, h.symm⟩))
    · rw [mem_ball, dist_zero_right] at hx
      rw [h] at hx
      linarith
  have hsepZ : ∀ p ∈ innerBlown X ρ, ∀ q ∈ innerBlown X ρ, p ≠ q → 1 ≤ ‖p - q‖ := by
    intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := hmem p hp
    obtain ⟨j, hj, rfl⟩ := hmem q hq
    exact hsep i j hi hj fun h => hpq (by rw [h])
  have hwin : ∀ x ∈ ball (0 : ℂ) ρ, blowupDens n x ∈ Set.Icc mMinus mPlus := by
    intro x hx
    rw [mem_ball, dist_zero_right] at hx
    exact blowupDens_mem_Icc hn (by linarith)
  have hmain := chart_truncation_ge (M := mPlus) hadm ((contDiff_blowupDens n).of_le (by exact_mod_cast le_top)).contDiffOn hΔ hsepZ
    (fun x hx => (mMinus_pos.le.trans (hwin x hx).1)) fun x hx => (hwin x hx).2
  -- the chart factors
  have hcard : (innerBlown X ρ).card = (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card :=
    Finset.card_image_of_injective _ fun a b h => hX ((smul_right_injective ℂ hs.ne') h)
  have hlam : ∀ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ),
      Real.log (2 / 5) ≤ Real.log (lam (X i)) := by
    intro i hi
    have hlt := (Finset.mem_filter.1 hi).2
    have hx : ‖X i‖ ≤ 2 := by
      rw [norm_smul, Real.norm_of_nonneg hs.le] at hlt
      by_contra h
      rw [not_le] at h
      nlinarith
    refine Real.log_le_log (by norm_num) ?_
    unfold lam
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [norm_nonneg (X i)]
  have hsumlam := Finset.sum_le_sum hlam
  rw [Finset.sum_const, nsmul_eq_mul, ← hcard] at hsumlam
  have hp := Real.pi_pos
  have h1 : Real.pi * Real.log (1 / 4) = -(Real.pi * Real.log 4) := by
    rw [one_div, Real.log_inv]; ring
  have h2 : Real.pi * Real.log (2 / 5) = -(Real.pi * Real.log (5 / 2)) := by
    rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num, Real.log_inv]; ring
  have hsumP : ∑ p ∈ innerBlown X ρ, (Real.pi * Real.log (1 / 4) -
      Real.pi * logPlus (1 / (2 * (ρ - ‖p‖)))) =
      -(Real.pi * Real.log 4) * (innerBlown X ρ).card -
        Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, h1]
    ring
  rw [hsumP] at hmain
  have h3 := mul_le_mul_of_nonneg_left hsumlam hp.le
  unfold constC1
  nlinarith

end Lower

end Sphere

end SandierSerfaty

end
