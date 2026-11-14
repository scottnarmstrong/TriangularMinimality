/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Polar sectors and angle packing

`polarSector a b ε` is the open polar sector about `0` with radii in `(0, ε)` and angles in `(a, b)`.

* `volume_polarSector`: for `-π ≤ a ≤ b ≤ π` its area is `(b - a) ε² / 2`;
* `volume_image_mul_add`: a map `z ↦ c + u z` with `‖u‖ = 1` preserves areas;
* `sum_angle_le_two_pi`: **angle packing.** Finitely many pairwise disjoint sectors of radius `ε`
  with apex at the same point `c` (rotated by unit complex numbers `u i`) have total angle
  at most `2π`. This is the inequality behind both packing steps (site packing and vertex packing)
  of the incidence count `M₀ ≤ 6n` (`SandierSerfaty.Geometry.VoronoiIncidence`).


-/

open MeasureTheory Metric Set Real

public section

namespace SandierSerfaty

/-- Polar sector about `0`: radii `(0, ε)`, angles `(a, b)`. -/
@[expose] noncomputable def polarSector (a b ε : ℝ) : Set ℂ :=
  Complex.polarCoord.symm '' (Ioo 0 ε ×ˢ Ioo a b)

theorem mem_polarSector_iff {a b ε : ℝ} {z : ℂ} :
    z ∈ polarSector a b ε ↔ ∃ r φ : ℝ, 0 < r ∧ r < ε ∧ a < φ ∧ φ < b ∧
      z = r * (Real.cos φ + Real.sin φ * Complex.I) := by
  constructor
  · rintro ⟨⟨r, φ⟩, ⟨⟨hr0, hr⟩, ⟨ha, hb⟩⟩, rfl⟩
    exact ⟨r, φ, hr0, hr, ha, hb, by rw [Complex.polarCoord_symm_apply]⟩
  · rintro ⟨r, φ, hr0, hr, ha, hb, rfl⟩
    exact ⟨⟨r, φ⟩, ⟨⟨hr0, hr⟩, ⟨ha, hb⟩⟩, by rw [Complex.polarCoord_symm_apply]⟩

theorem polarSector_eq_preimage {a b ε : ℝ} (ha : -π ≤ a) (hb : b ≤ π) :
    polarSector a b ε = Complex.polarCoord.source ∩ Complex.polarCoord ⁻¹' (Ioo 0 ε ×ˢ Ioo a b) := by
  have hTt : Ioo 0 ε ×ˢ Ioo a b ⊆ polarCoord.target := by
    rw [polarCoord_target]
    rintro ⟨r, φ⟩ ⟨hr, hφ⟩
    exact ⟨hr.1, lt_of_le_of_lt ha hφ.1, lt_of_lt_of_le hφ.2 hb⟩
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Complex.polarCoord.map_target (hTt hp), ?_⟩
    rw [mem_preimage, Complex.polarCoord.right_inv (hTt hp)]
    exact hp
  · rintro ⟨hz, hzT⟩
    exact ⟨_, hzT, Complex.polarCoord.left_inv hz⟩

theorem isOpen_polarSector {a b ε : ℝ} (ha : -π ≤ a) (hb : b ≤ π) :
    IsOpen (polarSector a b ε) := by
  rw [polarSector_eq_preimage ha hb]
  exact Complex.polarCoord.continuousOn.isOpen_inter_preimage Complex.polarCoord.open_source
    (isOpen_Ioo.prod isOpen_Ioo)

theorem measurableSet_polarSector {a b ε : ℝ} (ha : -π ≤ a) (hb : b ≤ π) :
    MeasurableSet (polarSector a b ε) :=
  (isOpen_polarSector ha hb).measurableSet

/-- **Area of a polar sector.** -/
theorem volume_polarSector {a b ε : ℝ} (ha : -π ≤ a) (hb : b ≤ π) (hε : 0 ≤ ε) (_hab : a ≤ b) :
    volume (polarSector a b ε) = ENNReal.ofReal ((b - a) * ε ^ 2 / 2) := by
  set T : Set (ℝ × ℝ) := Ioo 0 ε ×ˢ Ioo a b with hT
  have hTt : T ⊆ polarCoord.target := by
    rw [polarCoord_target]
    rintro ⟨r, φ⟩ ⟨hr, hφ⟩
    exact ⟨hr.1, lt_of_le_of_lt ha hφ.1, lt_of_lt_of_le hφ.2 hb⟩
  have hTm : MeasurableSet T := measurableSet_Ioo.prod measurableSet_Ioo
  have hSm := measurableSet_polarSector (ε := ε) ha hb
  rw [← lintegral_indicator_one hSm, ← Complex.lintegral_comp_polarCoord_symm]
  have key : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (polarSector a b ε).indicator 1 (Complex.polarCoord.symm p) =
        T.indicator (fun p => ENNReal.ofReal p.1) p := by
    intro p hp
    by_cases hpT : p ∈ T
    · have hm : Complex.polarCoord.symm p ∈ polarSector a b ε := mem_image_of_mem _ hpT
      rw [Set.indicator_of_mem hpT, Set.indicator_of_mem hm]
      simp
    · have : Complex.polarCoord.symm p ∉ polarSector a b ε := by
        rintro ⟨q, hq, hqp⟩
        exact hpT (Complex.polarCoord.symm.injOn (hTt hq) hp hqp ▸ hq)
      rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem this]
      simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet key,
    setLIntegral_indicator hTm, Set.inter_eq_self_of_subset_left hTt]
  rw [Measure.volume_eq_prod, hT, ← Measure.prod_restrict,
    lintegral_prod _ (by fun_prop : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1) _)]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo]
  rw [lintegral_mul_const _ (by fun_prop)]
  have h1 : ∫⁻ x in Ioo 0 ε, ENNReal.ofReal x = ENNReal.ofReal (ε ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε, integral_id]
      ring_nf
    · exact (continuous_id.integrableOn_Icc (a := 0) (b := ε)).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => hx.1.le)
  rw [h1, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

/-- The map `z ↦ c + u z` for a unit complex number `u` preserves Lebesgue measure. -/
theorem volume_image_mul_add {u : ℂ} (hu : ‖u‖ = 1) (c : ℂ) {S : Set ℂ} (hS : MeasurableSet S) :
    volume ((fun z => c + u * z) '' S) = volume S := by
  obtain ⟨a, rfl⟩ : ∃ a : Circle, (a : ℂ) = u := ⟨⟨u, mem_sphere_zero_iff_norm.2 hu⟩, rfl⟩
  set e : ℂ ≃ₗᵢ[ℝ] ℂ := rotation a with he
  have himg : (fun z => c + a * z) '' S = (fun z => -c + z) ⁻¹' (e.symm ⁻¹' S) := by
    ext z
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : e y = a * y := by rw [he, rotation_apply]
      rw [neg_add_cancel_left, ← this, LinearIsometryEquiv.symm_apply_apply]
      exact hy
    · intro h
      refine ⟨_, h, ?_⟩
      have : (a : ℂ) * e.symm (-c + z) = e (e.symm (-c + z)) := by rw [he, rotation_apply]
      rw [this, LinearIsometryEquiv.apply_symm_apply]
      ring
  rw [himg, measure_preimage_add, (e.symm.measurePreserving).measure_preimage hS.nullMeasurableSet]

theorem measurableSet_image_mul_add {u : ℂ} (hu : u ≠ 0) (c : ℂ) {S : Set ℂ}
    (hS : MeasurableSet S) : MeasurableSet ((fun z => c + u * z) '' S) := by
  have : (fun z => c + u * z) '' S = (fun z => (z - c) / u) ⁻¹' S := by
    ext z
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      field_simp
      ring
    · intro h
      exact ⟨_, h, by field_simp; ring⟩
  rw [this]
  exact hS.preimage (by fun_prop)

/-- **Angle packing.** Pairwise disjoint polar sectors of a common radius `ε > 0`, all with apex
`c` and rotated by unit complex numbers, have total angle at most `2π`. -/
theorem sum_angle_le_two_pi {ι : Type*} (s : Finset ι) (c : ℂ) (u : ι → ℂ) (a b : ι → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hu : ∀ i ∈ s, ‖u i‖ = 1) (ha : ∀ i ∈ s, -π ≤ a i) (hb : ∀ i ∈ s, b i ≤ π)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hdisj : (s : Set ι).PairwiseDisjoint
      fun i => (fun z => c + u i * z) '' polarSector (a i) (b i) ε) :
    ∑ i ∈ s, (b i - a i) ≤ 2 * π := by
  set K : ι → Set ℂ := fun i => (fun z => c + u i * z) '' polarSector (a i) (b i) ε with hK
  have hmeas : ∀ i ∈ s, MeasurableSet (K i) := fun i hi =>
    measurableSet_image_mul_add (by rw [← norm_ne_zero_iff, hu i hi]; exact one_ne_zero) c
      (measurableSet_polarSector (ha i hi) (hb i hi))
  have hsub : (⋃ i ∈ s, K i) ⊆ ball c ε := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨r, φ, hr0, hr, -, -, rfl⟩ := mem_polarSector_iff.1 hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hu i hi, one_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have : ‖(Real.cos φ : ℂ) + Real.sin φ * Complex.I‖ = 1 := by
      rw [← Complex.norm_exp_ofReal_mul_I φ, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    rw [this, mul_one]
    exact hr
  have hvol := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hdisj hmeas, Complex.volume_ball] at hvol
  have hKvol : ∀ i ∈ s, volume (K i) = ENNReal.ofReal ((b i - a i) * ε ^ 2 / 2) := fun i hi => by
    rw [hK, volume_image_mul_add (hu i hi) c (measurableSet_polarSector (ha i hi) (hb i hi)),
      volume_polarSector (ha i hi) (hb i hi) hε.le (hab i hi)]
  rw [Finset.sum_congr rfl hKvol, ← ENNReal.ofReal_sum_of_nonneg (fun i hi => by
    have := hab i hi; have : 0 ≤ b i - a i := by linarith
    positivity), ← ENNReal.ofReal_pow hε.le, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
  rw [← Finset.sum_div, ← Finset.sum_mul] at hvol
  have hε2 : 0 < ε ^ 2 := by positivity
  by_contra hcon
  rw [not_le] at hcon
  have : ε ^ 2 * π < (∑ i ∈ s, (b i - a i)) * ε ^ 2 / 2 := by nlinarith
  linarith

end SandierSerfaty

end
