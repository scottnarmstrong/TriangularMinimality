/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Layer cake and the logarithmic layer integral (comparison note, Lemmas `lem:layer`, `lem:logint`)

* `lintegral_ofReal_mul_eq_lintegral_layers`: for continuous `χ ≤ 1`,
  `∫_Ω χ f = ∫_0^1 ∫_{Ω ∩ {χ > t}} f dt` (Tonelli).
* `integral_Ioo_indicator_Iio_one`: `∫_0^1 1_{t < c} dt = c` for `c ∈ [0, 1]`.
* `integral_logLayer_le`: for `0 ≤ c ≤ 1 ≤ L` and `a ≥ 0`, the function
  `t ↦ 1_{t < c} (a + π log (L / (c - t)))` is integrable on `(0, 1)` with integral
  `≤ a + π (1 + log L)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Whole

/-- **Layer cake** (comparison note, Lemma `lem:layer`(b)). -/
theorem lintegral_ofReal_mul_eq_lintegral_layers {χ : ℂ → ℝ} (hχ : Continuous χ)
    (h1 : ∀ x, χ x ≤ 1) {f : ℂ → ℝ≥0∞} (hf : AEMeasurable f volume)
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) :
    ∫⁻ x in Ω, ENNReal.ofReal (χ x) * f x =
      ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ x in {x | t < χ x} ∩ Ω, f x := by
  have hA : ∀ t : ℝ, MeasurableSet {x : ℂ | t < χ x} := fun t =>
    measurableSet_lt measurable_const hχ.measurable
  have hrhs : ∀ t : ℝ, ∫⁻ x in {x | t < χ x} ∩ Ω, f x =
      ∫⁻ x in Ω, {x : ℂ | t < χ x}.indicator f x := fun t => by
    rw [lintegral_indicator (hA t), Measure.restrict_restrict (hA t)]
  simp_rw [hrhs]
  set G : ℝ → ℂ → ℝ≥0∞ := fun t x => {x : ℂ | t < χ x}.indicator f x with hG
  have hGm : AEMeasurable (Function.uncurry G)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict Ω)) := by
    have hset : MeasurableSet {p : ℝ × ℂ | p.1 < χ p.2} :=
      measurableSet_lt measurable_fst (hχ.measurable.comp measurable_snd)
    have e : Function.uncurry G = {p : ℝ × ℂ | p.1 < χ p.2}.indicator (fun p => f p.2) := by
      funext p
      simp only [Function.uncurry, hG, indicator, mem_ofPred_eq]
    rw [e]
    exact (hf.restrict.comp_snd).indicator hset
  rw [lintegral_lintegral_swap hGm]
  refine setLIntegral_congr_fun hΩ fun x _ => ?_
  have hx : ∫⁻ t in Ioo (0 : ℝ) 1, G t x = f x * volume (Ioo (0 : ℝ) 1 ∩ Iio (χ x)) := by
    have e : (fun t => G t x) = (Iio (χ x)).indicator fun _ => f x := by
      funext t
      simp only [hG, indicator, mem_ofPred_eq, mem_Iio]
    rw [e, lintegral_indicator measurableSet_Iio, setLIntegral_const,
      Measure.restrict_apply measurableSet_Iio, inter_comm]
  rw [hx]
  have hI : Ioo (0 : ℝ) 1 ∩ Iio (χ x) = Ioo 0 (χ x) := by
    ext t
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨h1', _⟩, h2'⟩; exact ⟨h1', h2'⟩
    · rintro ⟨h1', h2'⟩; exact ⟨⟨h1', lt_of_lt_of_le h2' (h1 x)⟩, h2'⟩
  rw [hI, Real.volume_Ioo, sub_zero, mul_comm]

/-- `∫_0^1 1_{t < c} dt = c` for `c ∈ [0, 1]`. -/
theorem integral_Ioo_indicator_Iio_one {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    ∫ t in Ioo (0 : ℝ) 1, (Iio c).indicator (fun _ => (1 : ℝ)) t = c := by
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hI : Iio c ∩ Ioo (0 : ℝ) 1 = Ioo 0 c := by
    ext t
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨h2', h1', _⟩; exact ⟨h1', h2'⟩
    · rintro ⟨h1', h2'⟩; exact ⟨h2', h1', lt_of_lt_of_le h2' h1⟩
  rw [hI, setIntegral_const, Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal h0,
    smul_eq_mul, mul_one]

theorem integrableOn_Ioo_indicator_Iio_one (c : ℝ) :
    IntegrableOn ((Iio c).indicator fun _ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
  (integrableOn_const (by simp)).indicator measurableSet_Iio

/-- The integrand of the logarithmic layer integral. -/
@[expose] noncomputable def logLayer (a L c : ℝ) (t : ℝ) : ℝ :=
  (Iio c).indicator (fun t => a + Real.pi * Real.log (L / (c - t))) t

/-- **The logarithmic layer integral** (comparison note, Lemma `lem:logint`). -/
theorem integral_logLayer_le {a L c : ℝ} (ha : 0 ≤ a) (hL : 1 ≤ L) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntegrableOn (logLayer a L c) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, logLayer a L c t ≤ a + Real.pi * (1 + Real.log L) := by
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hI : Iio c ∩ Ioo (0 : ℝ) 1 = Ioo 0 c := by
    ext t
    simp only [mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨h2', h1', _⟩; exact ⟨h1', h2'⟩
    · rintro ⟨h1', h2'⟩; exact ⟨h2', h1', lt_of_lt_of_le h2' hc1⟩
  set g : ℝ → ℝ := fun t => a + Real.pi * Real.log (L / (c - t)) with hg
  have hg' : ∀ t ∈ Ioo (0 : ℝ) c, g t = a + Real.pi * Real.log L - Real.pi * Real.log (c - t) := by
    intro t ht
    simp only [hg]
    rw [Real.log_div (by linarith) (by linarith [ht.2])]
    ring
  have hlogint : IntervalIntegrable (fun t => Real.log (c - t)) volume 0 c := by
    have := (intervalIntegral.intervalIntegrable_log' (a := c - c) (b := c - 0)).comp_sub_left c
    simpa using this.symm
  have hgint : IntegrableOn g (Ioo (0 : ℝ) c) := by
    have h1 : IntegrableOn (fun t => a + Real.pi * Real.log L - Real.pi * Real.log (c - t))
        (Ioc (0 : ℝ) c) := by
      have := ((intervalIntegrable_const (c := a + Real.pi * Real.log L)).sub
        (hlogint.const_mul Real.pi))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc0).1 this
    exact (h1.mono_set Ioo_subset_Ioc_self).congr_fun (fun t ht => (hg' t ht).symm) measurableSet_Ioo
  have hint : IntegrableOn (logLayer a L c) (Ioo (0 : ℝ) 1) := by
    unfold logLayer
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iio, hI]
    exact hgint
  refine ⟨hint, ?_⟩
  unfold logLayer
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hI,
    setIntegral_congr_fun measurableSet_Ioo hg', integral_Ioc_eq_integral_Ioo.symm,
    ← intervalIntegral.integral_of_le hc0,
    intervalIntegral.integral_sub intervalIntegrable_const (hlogint.const_mul Real.pi),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun u => Real.log u) c, sub_self, sub_zero, integral_log]
  simp only [sub_zero, smul_eq_mul, Real.log_zero, mul_zero]
  -- `c (a + π log L) - π (c log c - c) ≤ a + π (1 + log L)`
  have hc_log : c - c * Real.log c ≤ 1 := by
    rcases hc0.eq_or_lt with h | h
    · rw [← h]; simp
    · have h1 := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos h) h.le
      have h2 : c * (1 - c⁻¹) = c - 1 := by field_simp
      linarith
  have h3 : c * (a + Real.pi * Real.log L) ≤ a + Real.pi * Real.log L :=
    mul_le_of_le_one_left (by positivity) hc1
  nlinarith [Real.pi_pos]

end Whole

end SandierSerfaty

end
