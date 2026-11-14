/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartLower
public import SandierSerfaty.Sphere.Lower.ChooseRadius

/-!
# Crude and a priori bounds (sphere note, Lemma 6.10)

For `X` injective in `ℂⁿ` with all `xᵢ ≠ 0`, `r > 0`, `|xᵢ| ≠ r`, and the blown-up points `1`-separated in both charts
(`X` and `X̃ = ι X`), write `Φ_S`, `Φ_N` for the two bracketed terms of the two-chart decomposition
(`Lower.chartS`, `Lower.chartN`).  `Lower.chartS_ge`, `Lower.chartN_ge` are Lemma 6.10(i) and
`Lower.apriori_energy` is Lemma 6.10(ii): if `𝔎(T X) ≤ C_U n` and `Λ(r) ≤ 20 √n / κ`, then the sum of the truncated
Dirichlet energies of the two charts is at most `C_A n`.
-/

open MeasureTheory Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The truncated Dirichlet energy of the chart `X'` on `B(0, ρ)` (the integral in Lemma 6.10). -/
@[expose] noncomputable def truncDirichlet {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) : ℝ :=
  ∫ x in ball (0 : ℂ) ρ, ‖gradient (fun y => blowupPot X y -
    ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2

theorem truncDirichlet_nonneg {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) : 0 ≤ truncDirichlet X ρ :=
  setIntegral_nonneg measurableSet_ball fun _ _ => by positivity

theorem card_innerBlown {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X) (ρ : ℝ) :
    (innerBlown X ρ).card = (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card :=
  Finset.card_image_of_injective _ fun _a _b h =>
    hX ((smul_right_injective ℂ (blowupScale_pos hn).ne') h)

/-- The logarithmic sum over the inner points is bounded by the corresponding term of `Λ`. -/
theorem sum_logPlus_innerBlown_le {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    {c : ℝ} (_hc : 0 < c) :
    ∑ p ∈ innerBlown X (blowupScale n * c), logPlus (1 / (2 * (blowupScale n * c - ‖p‖))) ≤
      ∑ i, logPlus (1 / (2 * (blowupScale n * |‖X i‖ - c|))) := by
  classical
  have hs := blowupScale_pos hn
  unfold innerBlown
  rw [Finset.sum_image (fun a _ b _ h => hX ((smul_right_injective ℂ hs.ne') h)), Finset.sum_filter]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with h
  · rw [norm_smul, Real.norm_of_nonneg hs.le] at h ⊢
    have h1 : ‖X i‖ < c := lt_of_mul_lt_mul_left h hs.le
    rw [abs_of_neg (by linarith)]
    apply le_of_eq
    congr 3
    ring
  · exact logPlus_nonneg _

theorem innerBlown_smul_eq {n : ℕ} (X : Fin n → ℂ) (r : ℝ) (hs : 0 < blowupScale n) :
    (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < blowupScale n * r) =
      Finset.univ.filter fun i => ‖X i‖ < r := by
  refine Finset.filter_congr fun i _ => ?_
  rw [norm_smul, Real.norm_of_nonneg hs.le]
  exact mul_lt_mul_iff_right₀ hs

theorem innerBlown_S_eq {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (r : ℝ) :
    innerBlown X (blowupScale n * r) =
      (Finset.univ.filter fun i => ‖X i‖ < r).image fun i => blowupScale n • X i := by
  unfold innerBlown
  rw [innerBlown_smul_eq X r (blowupScale_pos hn)]

theorem innerBlown_N_eq {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX0 : ∀ i, X i ≠ 0) {r : ℝ}
    (hr : 0 < r) :
    innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹) =
      (Finset.univ.filter fun i => r < ‖X i‖).image fun i => blowupScale n • invC (X i) := by
  unfold innerBlown
  rw [innerBlown_smul_eq (fun i => invC (X i)) r⁻¹ (blowupScale_pos hn)]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  have hpos : 0 < ‖X i‖ := norm_pos_iff.2 (hX0 i)
  simp only [invC, norm_inv, Complex.norm_conj]
  exact inv_lt_inv₀ hpos hr

/-- **Lemma 6.10(ii)** (a priori bound): the truncated Dirichlet energies of the two charts add up to at most
`C_A n`, with `C_A = 2π C_U + 2π |log κ| + 2 C₁ + 40 π / κ`. -/
theorem apriori_energy {n : ℕ} (hn : 2 ≤ n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hX0 : ∀ i, X i ≠ 0) {r : ℝ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hrX : ∀ i, ‖X i‖ ≠ r)
    (hsepS : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖)
    (hsepN : ∀ i j, i ≠ j →
      1 ≤ ‖blowupScale n • invC (X i) - blowupScale n • invC (X j)‖)
    {CU : ℝ} (hK : normalizedEnergy (fun i => stereo (X i)) ≤ CU * n)
    (hΛ : lambdaSum X r ≤ 20 * Real.sqrt n / blowupKappa) :
    truncDirichlet X (blowupScale n * r) + truncDirichlet (fun i => invC (X i)) (blowupScale n * r⁻¹) ≤
      (2 * Real.pi * CU + 2 * Real.pi * |Real.log blowupKappa| + 2 * constC1 +
        40 * Real.pi / blowupKappa) * n := by
  classical
  have hn0 : 0 < n := by omega
  have hs := blowupScale_pos hn0
  have hr0 : 0 < r := by linarith
  have hXt : Function.Injective fun i => invC (X i) := fun a b h => hX (invC_injective h)
  have hdec := two_chart_decomposition hn0 X hX hX0 hr0 hrX
  -- the south chart
  have hS := chartEnergy_ge hn0 X hX (ρ := blowupScale n * r) (by positivity)
    (by nlinarith) (fun i h => by
      rw [norm_smul, Real.norm_of_nonneg hs.le] at h
      exact hrX i (mul_left_cancel₀ hs.ne' h))
    (fun i j hi hj hij => hsepS i j hij)
  have hN := chartEnergy_ge hn0 (fun i => invC (X i)) hXt (ρ := blowupScale n * r⁻¹)
    (by positivity) (by
      have : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
      nlinarith)
    (fun i h => by
      rw [norm_smul, Real.norm_of_nonneg hs.le] at h
      have h' := mul_left_cancel₀ hs.ne' h
      simp only [invC, norm_inv, Complex.norm_conj] at h'
      exact hrX i (by simpa using congrArg (·⁻¹) h'))
    (fun i j hi hj hij => hsepN i j hij)
  rw [innerBlown_smul_eq X r hs] at hS
  have hfN : (Finset.univ.filter fun i => ‖blowupScale n • invC (X i)‖ < blowupScale n * r⁻¹) =
      Finset.univ.filter fun i => r < ‖X i‖ := by
    rw [innerBlown_smul_eq (fun i => invC (X i)) r⁻¹ hs]
    refine Finset.filter_congr fun i _ => ?_
    have hpos : 0 < ‖X i‖ := norm_pos_iff.2 (hX0 i)
    simp only [invC, norm_inv, Complex.norm_conj]
    exact inv_lt_inv₀ hpos hr0
  rw [hfN] at hN
  -- restate the decomposition with `innerBlown`
  rw [← innerBlown_S_eq hn0 X r, ← innerBlown_N_eq hn0 X hX0 hr0, mul_comm r (blowupScale n),
    div_eq_mul_inv] at hdec
  have hcard : ((innerBlown X (blowupScale n * r)).card : ℝ) +
      (innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹)).card = n := by
    rw [card_innerBlown hn0 X hX, card_innerBlown hn0 _ hXt, innerBlown_smul_eq X r hs, hfN]
    have hNe : (Finset.univ.filter fun i => r < ‖X i‖) =
        Finset.univ.filter fun i => ¬ ‖X i‖ < r := by
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · intro h; exact not_lt.2 h.le
      · intro h; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm (hrX i))
    rw [hNe, ← Nat.cast_add, Finset.card_filter_add_card_filter_not]
    simp
  have hLS := sum_logPlus_innerBlown_le hn0 X hX hr0
  have hLN := sum_logPlus_innerBlown_le hn0 (fun i => invC (X i)) hXt (inv_pos.2 hr0)
  have hΛ' : lambdaSum X r = ∑ i, logPlus (1 / (2 * (blowupScale n * |‖X i‖ - r|))) +
      ∑ i, logPlus (1 / (2 * (blowupScale n * |‖invC (X i)‖ - r⁻¹|))) := by
    unfold lambdaSum
    rw [← Finset.sum_add_distrib]
  have hsq : Real.sqrt n ≤ n := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    calc Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
          have : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact h1
          exact le_mul_of_one_le_right (Real.sqrt_nonneg n) this
      _ = n := Real.mul_self_sqrt (by positivity)
  have hk := blowupKappa_pos
  have hp := Real.pi_pos
  have hC1 := constC1_nonneg
  have hlog : Real.log blowupKappa ≤ |Real.log blowupKappa| := le_abs_self _
  have h20 : 20 * Real.sqrt n / blowupKappa ≤ 20 * n / blowupKappa := by gcongr
  unfold truncDirichlet
  have hKl : Real.pi * normalizedEnergy (fun i => stereo (X i)) ≤ Real.pi * (CU * n) :=
    mul_le_mul_of_nonneg_left hK hp.le
  have hΛn : lambdaSum X r ≤ 20 * n / blowupKappa := hΛ.trans h20
  have hmul : Real.pi * lambdaSum X r ≤ Real.pi * (20 * n / blowupKappa) :=
    mul_le_mul_of_nonneg_left hΛn hp.le
  have hnκ : (40 * Real.pi / blowupKappa) * n = 2 * (Real.pi * (20 * n / blowupKappa)) := by
    field_simp; ring
  have hCn : constC1 * ((innerBlown X (blowupScale n * r)).card +
      (innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹)).card : ℝ) = constC1 * n := by
    rw [hcard]
  have hlogn : Real.pi * n * Real.log blowupKappa ≤ Real.pi * n * |Real.log blowupKappa| :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith [hS, hN, hdec, hmul, hKl, hnκ, hCn, hlogn, congrArg (Real.pi * ·) hΛ',
    mul_le_mul_of_nonneg_left hLS hp.le, mul_le_mul_of_nonneg_left hLN hp.le]

end Lower

end Sphere

end SandierSerfaty

end
