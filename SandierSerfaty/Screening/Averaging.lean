/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# The averaging choice (screening note, Lemma 4.6)

The screening note, Lemma 4.6 (`lem:avg`): if `h ≥ 0` is measurable on
`[s₁, s₂]` and `∫_{s₁}^{s₂} h ≤ M`, then `h(s) ≤ M / (s₂ - s₁)` for some `s ∈ [s₁, s₂]`.

* `exists_le_of_lintegral_le`: the statement with a lower Lebesgue integral (`h : ℝ → ℝ≥0∞`
  a.e.-measurable on `[s₁, s₂]`; no integrability needed);
* `exists_le_of_integral_le`: the statement for real `h` integrable on `[s₁, s₂]` (no sign needed).
-/

open MeasureTheory Set Filter
open scoped ENNReal

public section

namespace SandierSerfaty.Screening

/-- **Averaging choice** (screening note, Lemma 4.6), lower-integral form: if `∫_{[s₁,s₂]} h ≤ M` then
`h(s) ≤ M / (s₂ - s₁)` for some `s ∈ [s₁, s₂]`. -/
theorem exists_le_of_lintegral_le {s₁ s₂ : ℝ} (hs : s₁ < s₂) {h : ℝ → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict (Icc s₁ s₂))) {M : ℝ≥0∞}
    (hM : ∫⁻ s in Icc s₁ s₂, h s ≤ M) :
    ∃ s ∈ Icc s₁ s₂, h s ≤ M / ENNReal.ofReal (s₂ - s₁) := by
  by_contra hcon
  push Not at hcon
  set L := ENNReal.ofReal (s₂ - s₁) with hL
  have hL0 : L ≠ 0 := by rw [hL]; simpa using hs
  have hLt : L ≠ ⊤ := ENNReal.ofReal_ne_top
  have hMt : M ≠ ⊤ := by
    intro hMt
    have := hcon s₁ ⟨le_rfl, hs.le⟩
    rw [hMt, ENNReal.top_div_of_ne_top hLt] at this
    exact not_top_lt this
  have hconst : ∫⁻ _s in Icc s₁ s₂, M / L = M := by
    rw [setLIntegral_const, Real.volume_Icc, ← hL, ENNReal.div_mul_cancel hL0 hLt]
  have hae : ∀ᵐ s ∂volume, s ∈ Icc s₁ s₂ → M / L < hh.mk h s := by
    have h1 := hh.ae_eq_mk
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Icc] at h1
    filter_upwards [h1] with s hs' hsI
    rw [← hs' hsI]
    exact hcon s hsI
  have hlt := setLIntegral_strict_mono measurableSet_Icc (by rw [Real.volume_Icc]; simpa using hs)
    hh.measurable_mk (by rw [hconst]; exact hMt) hae
  rw [hconst, ← lintegral_congr_ae hh.ae_eq_mk] at hlt
  exact absurd hM (not_le.2 hlt)

/-- **Averaging choice** (screening note, Lemma 4.6), Bochner form: if `h` is integrable on `[s₁, s₂]` and
`∫_{s₁}^{s₂} h ≤ M`, then `h(s) ≤ M / (s₂ - s₁)` for some `s ∈ [s₁, s₂]`. -/
theorem exists_le_of_integral_le {s₁ s₂ : ℝ} (hs : s₁ < s₂) {h : ℝ → ℝ}
    (hh : IntegrableOn h (Icc s₁ s₂)) {M : ℝ} (hM : ∫ s in s₁..s₂, h s ≤ M) :
    ∃ s ∈ Icc s₁ s₂, h s ≤ M / (s₂ - s₁) := by
  by_contra hcon
  push Not at hcon
  have hlen : 0 < s₂ - s₁ := sub_pos.2 hs
  have hi : IntervalIntegrable (fun s => h s - M / (s₂ - s₁)) volume s₁ s₂ :=
    ((hh.mono_set (uIcc_of_le hs.le).subset).intervalIntegrable).sub intervalIntegrable_const
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on hi
    (fun s hs' => sub_pos.2 (hcon s (Ioo_subset_Icc_self hs'))) hs
  rw [intervalIntegral.integral_sub
      ((hh.mono_set (uIcc_of_le hs.le).subset).intervalIntegrable) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, mul_div_cancel₀ _ hlen.ne'] at hpos
  linarith

end SandierSerfaty.Screening

end
