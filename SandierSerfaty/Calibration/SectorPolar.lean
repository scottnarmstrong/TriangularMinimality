/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.PolarInt
public import SandierSerfaty.Geometry.VoronoiSectorTotals

/-!
# Polar integration over the model sector

Paper `geo:sector` and `cal:trial-potential`. The model sector
`S(d, α, β) = modelSector d α β = {(r, φ) : -α < φ < β, 0 < r < d sec φ}` (signed `|α|, |β| < π/2`).

* `polarRegion d α β η`: the polar region `{(r, φ) | -α < φ < β, η < r, r cos φ < d}` of `S ∩ {η < ‖w‖}`;
* `integral_modelSector_inter_polar`: for `F` with `r F(r e^{iφ})` integrable on the region,
  `∫_{S ∩ {η < ‖w‖}} F = ∫_{-α}^{β} ∫_{η}^{d sec φ} r F(r e^{iφ}) dr dφ`, together with integrability of the
  inner integral (as a function of `φ`);
* `integrableOn_polarRegion`: the integrability hypothesis holds for a function that is bounded on the
  sector and measurable in polar coordinates.
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty

namespace Calibration

/-- The polar region `{(r, φ) | -α < φ < β, η < r, r cos φ < d}` of `S(d, α, β) ∩ {‖w‖ > η}`. -/
@[expose] def polarRegion (d α β η : ℝ) : Set (ℝ × ℝ) :=
  {x | x.2 ∈ Ioo (-α) β ∧ η < x.1 ∧ x.1 * Real.cos x.2 < d}

theorem measurableSet_polarRegion (d α β η : ℝ) : MeasurableSet (polarRegion d α β η) := by
  have h1 : MeasurableSet {x : ℝ × ℝ | x.2 ∈ Ioo (-α) β} := measurable_snd measurableSet_Ioo
  have h2 : MeasurableSet {x : ℝ × ℝ | η < x.1} := measurableSet_lt measurable_const measurable_fst
  have h3 : MeasurableSet {x : ℝ × ℝ | x.1 * Real.cos x.2 < d} :=
    measurableSet_lt (measurable_fst.mul (Real.measurable_cos.comp measurable_snd)) measurable_const
  exact h1.inter (h2.inter h3)

theorem polarCoord_symm_norm {x : ℝ × ℝ} (hx : 0 < x.1) : ‖(Complex.polarCoord.symm x : ℂ)‖ = x.1 := by
  have hsymm : Complex.polarCoord.symm x = (x.1 : ℂ) * (Complex.cos x.2 + Complex.sin x.2 * Complex.I) := by
    rw [Complex.polarCoord_symm_apply]; push_cast; rfl
  rw [hsymm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
    Complex.norm_cos_add_sin_mul_I, mul_one]

theorem polarCoord_symm_arg {x : ℝ × ℝ} (hx : 0 < x.1) (hx2 : x.2 ∈ Ioc (-π) π) :
    Complex.arg (Complex.polarCoord.symm x : ℂ) = x.2 := by
  have hsymm : Complex.polarCoord.symm x = (x.1 : ℂ) * (Complex.cos x.2 + Complex.sin x.2 * Complex.I) := by
    rw [Complex.polarCoord_symm_apply]; push_cast; rfl
  rw [hsymm]
  exact Complex.arg_mul_cos_add_sin_mul_I hx hx2

theorem polarCoord_symm_ne_zero {x : ℝ × ℝ} (hx : 0 < x.1) : (Complex.polarCoord.symm x : ℂ) ≠ 0 := by
  intro h
  have := polarCoord_symm_norm hx
  rw [h] at this; simp at this; linarith

/-- For a point of the polar target, membership of `polar.symm` in `S ∩ {‖w‖ > η}` is membership of the
region. -/
theorem polarCoord_symm_mem_iff {d α β η : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) {x : ℝ × ℝ}
    (hx : x ∈ polarCoord.target) :
    (Complex.polarCoord.symm x : ℂ) ∈ modelSector d α β ∩ {w : ℂ | η < ‖w‖} ↔ x ∈ polarRegion d α β η := by
  rw [polarCoord_target] at hx
  have hr : 0 < x.1 := hx.1
  have hθ : x.2 ∈ Ioc (-π) π := ⟨hx.2.1, hx.2.2.le⟩
  have hn := polarCoord_symm_norm hr
  have ha := polarCoord_symm_arg hr hθ
  have hne := polarCoord_symm_ne_zero hr
  rw [modelSector_eq_polar hα hβ]
  simp only [mem_inter_iff, mem_ofPred_eq, ha, hn, polarRegion, mem_Ioo]
  constructor
  · rintro ⟨⟨-, h1, h2, h3⟩, h4⟩; exact ⟨⟨h1, h2⟩, h4, h3⟩
  · rintro ⟨⟨h1, h2⟩, h4, h3⟩; exact ⟨⟨hne, h1, h2, h3⟩, h4⟩

theorem polarRegion_subset_target {d α β η : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) (hη : 0 ≤ η) :
    polarRegion d α β η ⊆ polarCoord.target := by
  intro x hx
  rw [polarCoord_target]
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := hx
  obtain ⟨-, a2⟩ := abs_lt.1 hα
  obtain ⟨a1, -⟩ := abs_lt.1 hα
  obtain ⟨b1, b2⟩ := abs_lt.1 hβ
  exact ⟨lt_of_le_of_lt hη h3, by linarith [pi_pos], by linarith [pi_pos]⟩

/-- **Polar integration over the model sector.** -/
theorem integral_modelSector_inter_polar {d α β η : ℝ} (_hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hη : 0 ≤ η) (F : ℂ → ℝ)
    (hF : IntegrableOn (fun x : ℝ × ℝ => x.1 * F (Complex.polarCoord.symm x)) (polarRegion d α β η)) :
    IntegrableOn (fun φ : ℝ => ∫ r in Ioo η (d / Real.cos φ), r * F (Complex.polarCoord.symm (r, φ)))
        (Ioo (-α) β) ∧
      ∫ w in modelSector d α β ∩ {w : ℂ | η < ‖w‖}, F w =
        ∫ φ in Ioo (-α) β, ∫ r in Ioo η (d / Real.cos φ), r * F (Complex.polarCoord.symm (r, φ)) := by
  set A : Set ℂ := modelSector d α β ∩ {w : ℂ | η < ‖w‖} with hA
  set R : Set (ℝ × ℝ) := polarRegion d α β η with hR
  set G : ℝ × ℝ → ℝ := fun x => x.1 * F (Complex.polarCoord.symm x) with hG
  have hAm : MeasurableSet A := (measurableSet_modelSector d α β).inter
    (measurableSet_lt measurable_const measurable_norm)
  have hRm : MeasurableSet R := measurableSet_polarRegion d α β η
  have hsub : R ⊆ polarCoord.target := polarRegion_subset_target hα hβ hη
  -- the polar integrand
  have hcongr : ∀ x ∈ polarCoord.target,
      x.1 • A.indicator F (Complex.polarCoord.symm x) = R.indicator G x := by
    intro x hx
    by_cases hmem : x ∈ R
    · have : (Complex.polarCoord.symm x : ℂ) ∈ A := (polarCoord_symm_mem_iff hα hβ hx).2 hmem
      rw [indicator_of_mem this, indicator_of_mem hmem]; rfl
    · have : (Complex.polarCoord.symm x : ℂ) ∉ A := fun h => hmem ((polarCoord_symm_mem_iff hα hβ hx).1 h)
      rw [indicator_of_notMem this, indicator_of_notMem hmem]; simp
  have h1 : ∫ w in A, F w = ∫ x, R.indicator G x := by
    rw [← integral_indicator hAm, ← Complex.integral_comp_polarCoord_symm,
      setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr,
      setIntegral_indicator hRm, inter_eq_right.2 hsub, integral_indicator hRm]
  have hInt : Integrable (R.indicator G) (volume.prod volume) := by
    have : IntegrableOn G R := hF
    exact (integrable_indicator_iff hRm).2 this
  -- slices
  set I : ℝ → ℝ := fun φ => ∫ r in Ioo η (d / Real.cos φ), r * F (Complex.polarCoord.symm (r, φ)) with hI
  have hslice : ∀ φ : ℝ, ∫ r, R.indicator G (r, φ) = (Ioo (-α) β).indicator I φ := by
    intro φ
    by_cases hφ : φ ∈ Ioo (-α) β
    · have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [(abs_lt.1 hα).2, hφ.1, pi_pos, (abs_lt.1 hα).1], by linarith [(abs_lt.1 hβ).2, hφ.2]⟩
      have : (fun r => R.indicator G (r, φ)) =
          (Ioo η (d / Real.cos φ)).indicator (fun r => r * F (Complex.polarCoord.symm (r, φ))) := by
        funext r
        by_cases hr : r ∈ Ioo η (d / Real.cos φ)
        · have : (r, φ) ∈ R := ⟨hφ, hr.1, by have := hr.2; rwa [lt_div_iff₀ hc] at this⟩
          rw [indicator_of_mem this, indicator_of_mem hr]
        · have : (r, φ) ∉ R := fun h => hr ⟨h.2.1, by rw [lt_div_iff₀ hc]; exact h.2.2⟩
          rw [indicator_of_notMem this, indicator_of_notMem hr]
      rw [indicator_of_mem hφ]
      simp only [this]
      exact integral_indicator measurableSet_Ioo
    · rw [indicator_of_notMem hφ]
      have : (fun r => R.indicator G (r, φ)) = fun _ => 0 := by
        funext r
        have : (r, φ) ∉ R := fun h => hφ h.1
        rw [indicator_of_notMem this]
      simp only [this, integral_zero]
  have hIint : Integrable (fun φ => ∫ r, R.indicator G (r, φ)) volume := hInt.integral_prod_right
  simp_rw [hslice] at hIint
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).1 hIint, ?_⟩
  rw [h1]
  have := integral_prod_symm (R.indicator G) hInt
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl, this]
  simp_rw [hslice]
  exact integral_indicator measurableSet_Ioo

/-- On the sector, `cos φ ≥ cos (max |α| |β|) > 0` and `r < d / cos (max |α| |β|)`. -/
theorem polarRegion_subset_box {d α β η : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hη : 0 ≤ η) :
    polarRegion d α β η ⊆ Ioc 0 (d / Real.cos (max |α| |β|)) ×ˢ Ioo (-α) β := by
  have hm : max |α| |β| < π / 2 := max_lt hα hβ
  have hm0 : 0 ≤ max |α| |β| := le_max_of_le_left (abs_nonneg _)
  have hc0 : 0 < Real.cos (max |α| |β|) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hm⟩
  rintro x ⟨hx2, hx1, hx3⟩
  refine ⟨⟨lt_of_le_of_lt hη hx1, ?_⟩, hx2⟩
  have hφ : |x.2| ≤ max |α| |β| := by
    rw [abs_le]
    constructor
    · have := le_abs_self α; have := le_max_left |α| |β|; linarith [hx2.1]
    · have := le_abs_self β; have := le_max_right |α| |β|; linarith [hx2.2]
  have hcos : Real.cos (max |α| |β|) ≤ Real.cos x.2 := by
    rw [← Real.cos_abs x.2]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos]) hφ
  have hcx : 0 < Real.cos x.2 := lt_of_lt_of_le hc0 hcos
  have : x.1 < d / Real.cos x.2 := by rwa [lt_div_iff₀ hcx]
  refine this.le.trans ?_
  exact div_le_div_of_nonneg_left hd.le hc0 hcos

theorem integrableOn_polarRegion {d α β η : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hη : 0 ≤ η) {F : ℂ → ℝ} {C : ℝ}
    (hmeas : AEStronglyMeasurable (fun x : ℝ × ℝ => x.1 * F (Complex.polarCoord.symm x))
      (volume.restrict (polarRegion d α β η)))
    (hbd : ∀ w ∈ modelSector d α β ∩ {w : ℂ | η < ‖w‖}, ‖w‖ * |F w| ≤ C) :
    IntegrableOn (fun x : ℝ × ℝ => x.1 * F (Complex.polarCoord.symm x)) (polarRegion d α β η) := by
  have hbox := polarRegion_subset_box hd hα hβ hη
  have hfin : volume (polarRegion d α β η) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hbox)
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have : IsFiniteMeasure (volume.restrict (polarRegion d α β η)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
  refine Integrable.of_bound hmeas |C| ?_
  refine (ae_restrict_iff' (measurableSet_polarRegion d α β η)).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hxt : x ∈ polarCoord.target := polarRegion_subset_target hα hβ hη hx
  have hmem := (polarCoord_symm_mem_iff hα hβ hxt).2 hx
  have h3 : 0 < x.1 := (hbox hx).1.1
  have h1 := hbd _ hmem
  rw [polarCoord_symm_norm h3] at h1
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h3]
  exact h1.trans (le_abs_self C)

theorem continuous_polarCoord_symm : Continuous fun x : ℝ × ℝ => (Complex.polarCoord.symm x : ℂ) := by
  simp_rw [Complex.polarCoord_symm_apply]
  fun_prop

theorem measurable_polarCoord_symm : Measurable fun x : ℝ × ℝ => (Complex.polarCoord.symm x : ℂ) :=
  continuous_polarCoord_symm.measurable

/-- A function continuous on the sector has an almost everywhere strongly measurable polar integrand. -/
theorem aestronglyMeasurable_polar_of_continuousOn {d α β η : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hη : 0 ≤ η) {F : ℂ → ℝ} (hF : ContinuousOn F (modelSector d α β)) :
    AEStronglyMeasurable (fun x : ℝ × ℝ => x.1 * F (Complex.polarCoord.symm x))
      (volume.restrict (polarRegion d α β η)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_polarRegion d α β η)
  refine continuous_fst.continuousOn.mul (hF.comp continuous_polarCoord_symm.continuousOn ?_)
  intro x hx
  exact ((polarCoord_symm_mem_iff hα hβ (polarRegion_subset_target hα hβ hη hx)).2 hx).1

/-- A globally measurable function has a measurable polar integrand. -/
theorem aestronglyMeasurable_polar_of_measurable {d α β η : ℝ} {F : ℂ → ℝ} (hF : Measurable F) :
    AEStronglyMeasurable (fun x : ℝ × ℝ => x.1 * F (Complex.polarCoord.symm x))
      (volume.restrict (polarRegion d α β η)) :=
  (measurable_fst.mul (hF.comp measurable_polarCoord_symm)).aestronglyMeasurable

end Calibration

end SandierSerfaty

end
