/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartLowerFinal

/-!
# Putting the two charts together (sphere note, Theorem 6.14, assembly)

For `X` the south chart, `Xt = ι X` the north chart and `r ∈ [1,2]` with `|X i| ≠ r`:

* `Lower.charts_energy_split`: `π 𝔎 + π n log κ = (W_S + π ∑ log λ) + (W_N + π ∑ log λ)` in the form of
  `chart_lower_bound`;
* `Lower.charts_card`: `#inner_S + #inner_N = n`;
* `Lower.charts_logPlus`: `∑_S log₊ + ∑_N log₊ ≤ Λ(r)`;
* `Lower.chartCtx_south`, `Lower.chartCtx_north`: the standing facts `ChartCtx` of the two charts.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem chartCtx_south {n : ℕ} (hn : 0 < n) {X : Fin n → ℂ} (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {r : ℝ} (hr1 : 1 ≤ r)
    (hr2 : r ≤ 2) (hrX : ∀ i, ‖X i‖ ≠ r) : ChartCtx n X (blowupScale n * r) := by
  have hs := blowupScale_pos hn
  refine ⟨hn, hX, hsep, fun i hi => ?_, by nlinarith, by nlinarith⟩
  rw [norm_smul, Real.norm_of_nonneg hs.le] at hi
  exact hrX i (mul_left_cancel₀ hs.ne' hi)

theorem chartCtx_north {n : ℕ} (hn : 0 < n) {X : Fin n → ℂ} (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • invC (X i) - blowupScale n • invC (X j)‖) {r : ℝ}
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hrX : ∀ i, ‖X i‖ ≠ r) :
    ChartCtx n (fun i => invC (X i)) (blowupScale n * r⁻¹) := by
  have hs := blowupScale_pos hn
  have hr0 : 0 < r := by linarith
  have hri : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hri2 : 1 / 2 ≤ r⁻¹ := by
    rw [one_div]; exact inv_anti₀ hr0 hr2
  refine ⟨hn, fun a b h => hX (invC_injective h), hsep, fun i hi => ?_, by nlinarith, by nlinarith⟩
  rw [norm_smul, Real.norm_of_nonneg hs.le] at hi
  have h' := mul_left_cancel₀ hs.ne' hi
  simp only [invC, norm_inv, Complex.norm_conj] at h'
  exact hrX i (by simpa using congrArg (·⁻¹) h')

theorem charts_energy_split {n : ℕ} (hn : 0 < n) {X : Fin n → ℂ} (hX : Function.Injective X)
    (hX0 : ∀ i, X i ≠ 0) {r : ℝ} (hr0 : 0 < r) (hrX : ∀ i, ‖X i‖ ≠ r) :
    Real.pi * normalizedEnergy (fun i => stereo (X i)) + Real.pi * n * Real.log blowupKappa =
      (punctureEnergy (ball (0 : ℂ) (blowupScale n * r)) (innerBlown X (blowupScale n * r)) (blowupPot X) +
        Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < blowupScale n * r),
          Real.log (lam (X i))) +
      (punctureEnergy (ball (0 : ℂ) (blowupScale n * r⁻¹))
          (innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹)) (blowupPot fun i => invC (X i)) +
        Real.pi * ∑ i ∈ Finset.univ.filter (fun i =>
          ‖blowupScale n • invC (X i)‖ < blowupScale n * r⁻¹), Real.log (lam (invC (X i)))) := by
  have hs := blowupScale_pos hn
  have hdec := two_chart_decomposition hn X hX hX0 hr0 hrX
  rw [← innerBlown_S_eq hn X r, ← innerBlown_N_eq hn X hX0 hr0, mul_comm r (blowupScale n),
    div_eq_mul_inv] at hdec
  have hfS : (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < blowupScale n * r) =
      Finset.univ.filter fun i => ‖X i‖ < r := innerBlown_smul_eq X r hs
  have hfN : (Finset.univ.filter fun i => ‖blowupScale n • invC (X i)‖ < blowupScale n * r⁻¹) =
      Finset.univ.filter fun i => r < ‖X i‖ := by
    rw [innerBlown_smul_eq (fun i => invC (X i)) r⁻¹ hs]
    refine Finset.filter_congr fun i _ => ?_
    have hpos : 0 < ‖X i‖ := norm_pos_iff.2 (hX0 i)
    simp only [invC, norm_inv, Complex.norm_conj]
    exact inv_lt_inv₀ hpos hr0
  rw [hfS, hfN]
  linarith

theorem charts_card {n : ℕ} (hn : 0 < n) {X : Fin n → ℂ} (hX : Function.Injective X) (hX0 : ∀ i, X i ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hrX : ∀ i, ‖X i‖ ≠ r) :
    ((innerBlown X (blowupScale n * r)).card : ℝ) +
      ((innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹)).card : ℝ) = n := by
  have hs := blowupScale_pos hn
  have hXt : Function.Injective fun i => invC (X i) := fun a b h => hX (invC_injective h)
  have hfN : (Finset.univ.filter fun i => ‖blowupScale n • invC (X i)‖ < blowupScale n * r⁻¹) =
      Finset.univ.filter fun i => r < ‖X i‖ := by
    rw [innerBlown_smul_eq (fun i => invC (X i)) r⁻¹ hs]
    refine Finset.filter_congr fun i _ => ?_
    have hpos : 0 < ‖X i‖ := norm_pos_iff.2 (hX0 i)
    simp only [invC, norm_inv, Complex.norm_conj]
    exact inv_lt_inv₀ hpos hr0
  rw [card_innerBlown hn X hX, card_innerBlown hn _ hXt, innerBlown_smul_eq X r hs, hfN]
  have hNe : (Finset.univ.filter fun i => r < ‖X i‖) =
      Finset.univ.filter fun i => ¬ ‖X i‖ < r := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h; exact not_lt.2 h.le
    · intro h; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm (hrX i))
  rw [hNe, ← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  simp

theorem charts_logPlus {n : ℕ} (hn : 0 < n) {X : Fin n → ℂ} (hX : Function.Injective X) {r : ℝ} (hr0 : 0 < r) :
    ∑ p ∈ innerBlown X (blowupScale n * r), logPlus (1 / (2 * (blowupScale n * r - ‖p‖))) +
      ∑ p ∈ innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹),
        logPlus (1 / (2 * (blowupScale n * r⁻¹ - ‖p‖))) ≤ lambdaSum X r := by
  have hXt : Function.Injective fun i => invC (X i) := fun a b h => hX (invC_injective h)
  have hLS := sum_logPlus_innerBlown_le hn X hX hr0
  have hLN := sum_logPlus_innerBlown_le hn (fun i => invC (X i)) hXt (inv_pos.2 hr0)
  have hΛ' : lambdaSum X r = ∑ i, logPlus (1 / (2 * (blowupScale n * |‖X i‖ - r|))) +
      ∑ i, logPlus (1 / (2 * (blowupScale n * |‖invC (X i)‖ - r⁻¹|))) := by
    unfold lambdaSum
    rw [← Finset.sum_add_distrib]
  rw [hΛ']
  exact add_le_add hLS hLN

end Lower

end Sphere

end SandierSerfaty

end
