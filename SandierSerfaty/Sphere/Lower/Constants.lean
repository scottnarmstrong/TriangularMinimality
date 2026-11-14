/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChooseRadius
public import SandierSerfaty.Sphere.Separation
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Density window and truncation-radius arithmetic (sphere note, Definition 6.8, Lemma 6.10)

* `Lower.mMinus = (2/5)² / (4 π κ²)` and `Lower.mPlus = 1 / (π κ²)`: the window of the blown-up density on the chart
  disc, with `mPlus / mMinus = 25`, `4 mPlus / mMinus = 100` and `mPlus < 1/150`
  (`Lower.four_mul_mPlus_div_mMinus`, `Lower.mPlus_lt`).
* `Lower.blowupDens n z = λ(z/s_n)² / (4 π κ²)`, the density `m` of Definition 3.6; it lies in
  `[mMinus, mPlus]` on `|z| ≤ 2 s_n` (`Lower.blowupDens_mem_Icc`).
* `Lower.log_min_ge`: with `α = min (1/4) (d/2)`, `log α ≥ log (1/4) - log₊ (1/(2d))` (used in Lemma 6.10(i)).
-/

open Real

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- `κ² = 40 / log 2`. -/
theorem blowupKappa_sq : blowupKappa ^ 2 = 40 / Real.log 2 := by
  have hlog := Real.log_pos (one_lt_two (α := ℝ))
  unfold blowupKappa cSep
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- The lower end `m₋ = (2/5)² / (4 π κ²)` of the density window. -/
@[expose] noncomputable def mMinus : ℝ := (2 / 5) ^ 2 / (4 * Real.pi * blowupKappa ^ 2)

/-- The upper end `m₊ = 1 / (π κ²)` of the density window. -/
@[expose] noncomputable def mPlus : ℝ := 1 / (Real.pi * blowupKappa ^ 2)

theorem mMinus_pos : 0 < mMinus := by
  have := Real.pi_pos
  have := blowupKappa_pos
  unfold mMinus; positivity

theorem mPlus_pos : 0 < mPlus := by
  have := Real.pi_pos
  have := blowupKappa_pos
  unfold mPlus; positivity

theorem mMinus_le_mPlus : mMinus ≤ mPlus := by
  have hp := Real.pi_pos
  have hk := blowupKappa_pos
  unfold mMinus mPlus
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hp (pow_pos hk 2)]

theorem four_mul_mPlus_div_mMinus : 4 * mPlus / mMinus = 100 := by
  have hp := Real.pi_pos
  have hk := blowupKappa_pos
  unfold mMinus mPlus
  field_simp
  norm_num

theorem mPlus_lt : mPlus < 1 / 150 := by
  have hp := Real.pi_pos
  have hlog := Real.log_pos (one_lt_two (α := ℝ))
  have hlog1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hpi : 3.14 < Real.pi := Real.pi_gt_d2
  unfold mPlus
  rw [blowupKappa_sq]
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  have : (150 : ℝ) < Real.pi * (40 / Real.log 2) := by
    rw [mul_div_assoc', lt_div_iff₀ hlog]
    nlinarith
  linarith

/-- The blown-up density `m(z) = λ(z/s_n)² / (4 π κ²)` (Definition 3.6). -/
@[expose] noncomputable def blowupDens (n : ℕ) (z : ℂ) : ℝ :=
  lam (((blowupScale n)⁻¹ : ℝ) • z) ^ 2 / (4 * Real.pi * blowupKappa ^ 2)

/-- On `|z| ≤ 2 s_n` the density lies in `[m₋, m₊]`. -/
theorem blowupDens_mem_Icc {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : ‖z‖ ≤ 2 * blowupScale n) :
    blowupDens n z ∈ Set.Icc mMinus mPlus := by
  have hs := blowupScale_pos hn
  have hp := Real.pi_pos
  have hk := blowupKappa_pos
  have hx : ‖((blowupScale n)⁻¹ : ℝ) • z‖ ≤ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_le_iff₀ hs]
    linarith
  have hl1 : 2 / 5 ≤ lam (((blowupScale n)⁻¹ : ℝ) • z) := by
    unfold lam
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [norm_nonneg (((blowupScale n)⁻¹ : ℝ) • z)]
  have hl2 := lam_le_two (((blowupScale n)⁻¹ : ℝ) • z)
  have hl0 : 0 ≤ lam (((blowupScale n)⁻¹ : ℝ) • z) := (lam_pos _).le
  unfold blowupDens mMinus mPlus
  constructor
  · gcongr
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : lam (((blowupScale n)⁻¹ : ℝ) • z) ^ 2 ≤ 4 := by nlinarith
    nlinarith [mul_pos hp (pow_pos hk 2)]

/-- `log (min (1/4) (d/2)) ≥ log (1/4) - log₊ (1/(2 d))` for `d > 0`. -/
theorem log_min_ge {d : ℝ} (hd : 0 < d) :
    Real.log (1 / 4) - logPlus (1 / (2 * d)) ≤ Real.log (min (1 / 4) (d / 2)) := by
  rcases le_total (1 / 4 : ℝ) (d / 2) with h | h
  · rw [min_eq_left h]
    linarith [logPlus_nonneg (1 / (2 * d))]
  · rw [min_eq_right h]
    have h1 : 1 ≤ 1 / (2 * d) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    unfold logPlus
    rw [max_eq_left (Real.log_nonneg h1), ← Real.log_div (by norm_num) (by positivity)]
    apply le_of_eq
    congr 1
    field_simp
    norm_num

end Lower

end Sphere

end SandierSerfaty

end
