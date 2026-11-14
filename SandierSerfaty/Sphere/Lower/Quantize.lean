/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectDomain
public import SandierSerfaty.Sphere.Lower.Neumann

/-!
# Integer mass squares (sphere note, Definition 6.8, the quantized squares `Q_K`)

For a density `ρ` with `0 ≤ ρ ≤ M` and the square `a + [0,t]²`, `Lower.sqMass ρ a t = ∫_{a+[0,t]²} ρ` is
continuous in `t ≥ 0` (`Lower.continuousOn_sqMass`) and increases by at least `mLo (t'² - t²)` between `t ≤ t'`
when `ρ ≥ mLo` on `a + [0,t']²`. `Lower.exists_quantized_side`: when `mLo (R - 3/4) ≥ 1`
there is `t ∈ [R-1, R-1/2]` with `∫_{a+[0,t]²} ρ ∈ ℕ`.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The mass `∫_{a + [0,t]²} ρ`. -/
@[expose] noncomputable def sqMass (ρ : ℂ → ℝ) (a : ℂ) (t : ℝ) : ℝ := ∫ x in sqAt a t, ρ x

theorem measurableSet_sqAt (a : ℂ) (t : ℝ) : MeasurableSet (sqAt a t) := by
  have : sqAt a t = (Complex.re ⁻¹' Icc a.re (a.re + t)) ∩ (Complex.im ⁻¹' Icc a.im (a.im + t)) := by
    ext x; simp [sqAt, and_assoc]
  rw [this]
  exact (measurableSet_Icc.preimage Complex.measurable_re).inter
    (measurableSet_Icc.preimage Complex.measurable_im)

theorem volume_sqAt (a : ℂ) (t : ℝ) :
    volume (sqAt a t) = ENNReal.ofReal t * ENNReal.ofReal t := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Icc a.re (a.re + t) ×ˢ Icc a.im (a.im + t))
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)
  have e : sqAt a t = Complex.measurableEquivRealProd ⁻¹' (Icc a.re (a.re + t) ×ˢ Icc a.im (a.im + t)) := by
    ext x
    simp only [sqAt, Complex.measurableEquivRealProd, mem_ofPred_eq, mem_preimage, mem_prod,
      mem_Icc]
    tauto
  rw [e, h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  simp

theorem sqAt_mono (a : ℂ) {t t' : ℝ} (h : t ≤ t') : sqAt a t ⊆ sqAt a t' := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  exact ⟨h1, by linarith, h3, by linarith⟩

variable {ρ : ℂ → ℝ} {M : ℝ}

theorem integrableOn_sqAt (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (a : ℂ)
    (t : ℝ) : IntegrableOn ρ (sqAt a t) := by
  have hfin : volume (sqAt a t) ≠ ⊤ := by
    rw [volume_sqAt]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine Measure.integrableOn_of_bounded (M := M) hfin hρm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]; exact hρM x

/-- Increment of the mass between nested squares. -/
theorem sqMass_sub_eq (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (a : ℂ)
    {t t' : ℝ} (h : t ≤ t') :
    sqMass ρ a t' - sqMass ρ a t = ∫ x in sqAt a t' \ sqAt a t, ρ x := by
  unfold sqMass
  rw [setIntegral_sdiff (measurableSet_sqAt a t) (integrableOn_sqAt hρm hρ0 hρM a t') (sqAt_mono a h)]

theorem volume_real_sdiff (a : ℂ) {t t' : ℝ} (ht : 0 ≤ t) (h : t ≤ t') :
    volume.real (sqAt a t' \ sqAt a t) = t' ^ 2 - t ^ 2 := by
  have h1 : volume (sqAt a t' \ sqAt a t) = volume (sqAt a t') - volume (sqAt a t) :=
    measure_sdiff (sqAt_mono a h) (measurableSet_sqAt a t).nullMeasurableSet
      (by rw [volume_sqAt]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  rw [measureReal_def, h1, volume_sqAt, volume_sqAt, ← ENNReal.ofReal_mul ht,
    ← ENNReal.ofReal_mul (ht.trans h),
    ← ENNReal.ofReal_sub _ (by positivity), ENNReal.toReal_ofReal (by nlinarith)]
  ring

theorem volume_sdiff_ne_top (a : ℂ) (t t' : ℝ) : volume (sqAt a t' \ sqAt a t) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono Set.sdiff_subset)
  rw [volume_sqAt]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem sqMass_sub_le (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (a : ℂ)
    {t t' : ℝ} (ht : 0 ≤ t) (h : t ≤ t') :
    sqMass ρ a t' - sqMass ρ a t ≤ M * (t' ^ 2 - t ^ 2) := by
  rw [sqMass_sub_eq hρm hρ0 hρM a h, ← volume_real_sdiff a ht h]
  have := setIntegral_mono_on (μ := volume) (s := sqAt a t' \ sqAt a t)
    ((integrableOn_sqAt hρm hρ0 hρM a t').mono_set Set.sdiff_subset)
    (integrableOn_const (volume_sdiff_ne_top a t t') (C := M))
    ((measurableSet_sqAt a t').diff (measurableSet_sqAt a t)) (fun x _ => hρM x)
  rw [setIntegral_const, smul_eq_mul] at this
  linarith

theorem sqMass_sub_ge (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (a : ℂ)
    {mLo : ℝ} {t t' : ℝ} (ht : 0 ≤ t) (h : t ≤ t') (hlow : ∀ x ∈ sqAt a t', mLo ≤ ρ x) :
    mLo * (t' ^ 2 - t ^ 2) ≤ sqMass ρ a t' - sqMass ρ a t := by
  rw [sqMass_sub_eq hρm hρ0 hρM a h, ← volume_real_sdiff a ht h]
  have := setIntegral_mono_on (μ := volume) (s := sqAt a t' \ sqAt a t)
    (integrableOn_const (volume_sdiff_ne_top a t t') (C := mLo))
    ((integrableOn_sqAt hρm hρ0 hρM a t').mono_set Set.sdiff_subset)
    ((measurableSet_sqAt a t').diff (measurableSet_sqAt a t)) (fun x hx => hlow x hx.1)
  rw [setIntegral_const, smul_eq_mul] at this
  linarith

theorem continuousOn_sqMass (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (a : ℂ) :
    ContinuousOn (sqMass ρ a) (Ici 0) := by
  have hM : 0 ≤ M := (hρ0 0).trans (hρM 0)
  have key : ∀ t ∈ Ici (0 : ℝ), ∀ t' ∈ Ici (0 : ℝ), |sqMass ρ a t' - sqMass ρ a t| ≤
      M * |t' ^ 2 - t ^ 2| := by
    intro t ht t' ht'
    rcases le_total t t' with h | h
    · have h1 := sqMass_sub_le hρm hρ0 hρM a ht h
      have h2 : 0 ≤ sqMass ρ a t' - sqMass ρ a t := by
        have := sqMass_sub_ge hρm hρ0 hρM a (mLo := 0) ht h (fun x _ => hρ0 x)
        simpa using this
      rw [abs_of_nonneg h2, abs_of_nonneg (by nlinarith [mem_Ici.1 ht])]
      exact h1
    · have h1 := sqMass_sub_le hρm hρ0 hρM a ht' h
      have h2 : 0 ≤ sqMass ρ a t - sqMass ρ a t' := by
        have := sqMass_sub_ge hρm hρ0 hρM a (mLo := 0) ht' h (fun x _ => hρ0 x)
        simpa using this
      rw [abs_sub_comm, abs_of_nonneg h2, abs_sub_comm, abs_of_nonneg (by nlinarith [mem_Ici.1 ht'])]
      exact h1
  intro t ht
  rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hg : ContinuousAt (fun t : ℝ => M * t ^ 2) t := by fun_prop
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hg (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun t' ht' hd => ?_⟩
  have h3 := key t ht t' ht'
  have h4 : M * |t' ^ 2 - t ^ 2| < ε / 2 := by
    have := hδ' hd
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hM] at this
    exact this
  rw [Real.dist_eq]
  linarith

/-- If `f` is continuous on `[a,b]` and increases by at least `1` there, it takes a natural-number value. -/
theorem exists_natCast_value {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h0 : 0 ≤ f a) (h : f a + 1 ≤ f b) : ∃ t ∈ Icc a b, ∃ k : ℕ, f t = k := by
  have h1 : (⌈f a⌉₊ : ℝ) ∈ Icc (f a) (f b) :=
    ⟨Nat.le_ceil _, by have := Nat.ceil_lt_add_one h0; linarith⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf h1
  exact ⟨t, ht, ⌈f a⌉₊, hft⟩

/-- **Definition 6.8, quantized squares.** If `ρ ≥ mLo` on `a + [0, R - 1/2]²`, `0 ≤ ρ ≤ M`, `R ≥ 1` and
`mLo (R - 3/4) ≥ 1`, there is `t ∈ [R - 1, R - 1/2]` with `∫_{a + [0,t]²} ρ ∈ ℕ`. -/
theorem exists_quantized_side (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρM : ∀ x, ρ x ≤ M) (a : ℂ)
    {mLo R : ℝ} (hR : 1 ≤ R) (hlow : ∀ x ∈ sqAt a (R - 1 / 2), mLo ≤ ρ x)
    (hbig : 1 ≤ mLo * (R - 3 / 4)) :
    ∃ t ∈ Icc (R - 1) (R - 1 / 2), ∃ k : ℕ, ∫ x in sqAt a t, ρ x = k := by
  have ht0 : (0 : ℝ) ≤ R - 1 := by linarith
  refine exists_natCast_value (f := sqMass ρ a) (by linarith)
    ((continuousOn_sqMass hρm hρ0 hρM a).mono (fun t ht => ht0.trans ht.1)) ?_ ?_
  · exact setIntegral_nonneg (measurableSet_sqAt a _) (fun x _ => hρ0 x)
  · have := sqMass_sub_ge hρm hρ0 hρM a ht0 (by linarith : R - 1 ≤ R - 1 / 2) hlow
    nlinarith [this]

end Lower

end Sphere

end SandierSerfaty

end
