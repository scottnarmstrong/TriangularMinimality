/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Markov and a pigeonhole step (for the sphere note's Lemma 6.12)

If two nonnegative functions are integrable on a set `s` of finite positive measure, there is a point of `s` where each
is at most three times its average (`exists_two_le_three_avg`).
-/

open MeasureTheory Set Filter
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- Markov's inequality in the form used for the random grid offset. -/
theorem three_measure_bad_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) (hE : ∫⁻ x, f x ∂μ ≠ ⊤) :
    3 * μ {x | 3 * ∫⁻ y, f y ∂μ < f x * μ Set.univ} ≤ μ Set.univ := by
  set E := ∫⁻ y, f y ∂μ with hEdef
  set M := μ Set.univ with hM
  by_cases hE0 : E = 0
  · have hz : f =ᵐ[μ] 0 := (lintegral_eq_zero_iff hf).1 hE0
    have : μ {x | 3 * E < f x * M} = 0 := by
      refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hz)
      intro hfx
      have : f x = 0 := hfx
      simp [this, hE0] at hx
    rw [this]; simp
  · have hmark := mul_meas_ge_le_lintegral₀ (μ := μ) (f := fun x => f x * M)
      (hf.mul_const M).aemeasurable (3 * E)
    rw [lintegral_mul_const _ hf, ← hEdef] at hmark
    have hsub : μ {x | 3 * E < f x * M} ≤ μ {x | 3 * E ≤ f x * M} :=
      measure_mono fun x (hx : 3 * E < f x * M) => (le_of_lt hx : 3 * E ≤ f x * M)
    have h1 : E * (3 * μ {x | 3 * E < f x * M}) ≤ E * M := by
      calc E * (3 * μ {x | 3 * E < f x * M}) = (3 * E) * μ {x | 3 * E < f x * M} := by ring
        _ ≤ (3 * E) * μ {x | 3 * E ≤ f x * M} := by gcongr
        _ ≤ E * M := hmark
    exact (ENNReal.mul_le_mul_iff_right hE0 hE).1 h1

/-- Pigeonhole: two nonnegative functions on a finite measure space are simultaneously at most three times
their averages somewhere on a set carrying the measure. -/
theorem exists_two_le_three_avg {α : Type*} [MeasurableSpace α] (ν : Measure α) (s : Set α)
    (hs : MeasurableSet s) (h0 : ν s ≠ 0) (htop : ν s ≠ ⊤) {f₁ f₂ : α → ℝ≥0∞}
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (hE₁ : ∫⁻ x in s, f₁ x ∂ν ≠ ⊤) (hE₂ : ∫⁻ x in s, f₂ x ∂ν ≠ ⊤) :
    ∃ x ∈ s, f₁ x * ν s ≤ 3 * ∫⁻ y in s, f₁ y ∂ν ∧ f₂ x * ν s ≤ 3 * ∫⁻ y in s, f₂ y ∂ν := by
  set μ := ν.restrict s with hμ
  have hM : μ Set.univ = ν s := by rw [hμ, Measure.restrict_apply_univ]
  have h1 := three_measure_bad_le μ hf₁ hE₁
  have h2 := three_measure_bad_le μ hf₂ hE₂
  rw [hM] at h1 h2
  set B₁ := {x | 3 * ∫⁻ y, f₁ y ∂μ < f₁ x * ν s} with hB₁
  set B₂ := {x | 3 * ∫⁻ y, f₂ y ∂μ < f₂ x * ν s} with hB₂
  -- the union of the bad sets has measure < ν s
  have hlt : μ (B₁ ∪ B₂) < ν s := by
    have h3 : 3 * μ (B₁ ∪ B₂) ≤ 2 * ν s := by
      calc 3 * μ (B₁ ∪ B₂) ≤ 3 * (μ B₁ + μ B₂) := by gcongr; exact measure_union_le _ _
        _ = 3 * μ B₁ + 3 * μ B₂ := by ring
        _ ≤ ν s + ν s := add_le_add h1 h2
        _ = 2 * ν s := by ring
    by_contra hge
    push Not at hge
    have : 3 * ν s ≤ 3 * μ (B₁ ∪ B₂) := by gcongr
    have h4 : 3 * ν s ≤ 2 * ν s := this.trans h3
    have h5 : ν s * 3 ≤ ν s * 2 := by simpa [mul_comm] using h4
    have h6 := (ENNReal.mul_le_mul_iff_right h0 htop).1 h5
    norm_num at h6
  -- so the complement has positive measure
  have hpos : μ (B₁ ∪ B₂)ᶜ ≠ 0 := by
    intro hc
    have : ν s ≤ μ (B₁ ∪ B₂) + μ (B₁ ∪ B₂)ᶜ := by
      rw [← hM]
      exact le_trans (measure_mono (Set.union_compl_self (B₁ ∪ B₂)).symm.le) (measure_union_le _ _)
    rw [hc, add_zero] at this
    exact absurd hlt (not_lt.2 this)
  have hfreq : ∃ᵐ x ∂μ, x ∉ B₁ ∪ B₂ := by
    intro hall
    exact hpos (by simpa [ae_iff, Set.compl_def] using hall)
  have hmem : ∀ᵐ x ∂μ, x ∈ s := ae_restrict_mem hs
  obtain ⟨x, hx, hxs⟩ := (hfreq.and_eventually hmem).exists
  refine ⟨x, hxs, ?_, ?_⟩
  · have := hx; simp only [mem_union, hB₁, hB₂, mem_ofPred_eq, not_or, not_lt] at this
    exact this.1
  · have := hx; simp only [mem_union, hB₁, hB₂, mem_ofPred_eq, not_or, not_lt] at this
    exact this.2


end Lower

end Sphere

end SandierSerfaty

end
