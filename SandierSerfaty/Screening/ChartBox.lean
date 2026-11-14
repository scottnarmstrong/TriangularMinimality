/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.RectangleSolver

/-!
# Boxes in the chart of a rectangle

Bookkeeping for the screening note's §4.7–4.22: all the regions of the
screening construction (columns, top parts, filler parts, compensation strips, flux cells, carry
cells, filler pieces) are images `Ψ(I × J)` of coordinate boxes under the chart `Ψ = Rect.chart` of a
rectangle `H` (an affine isometry `w ↦ z₀ + M w`, `M` orthogonal).

* `Rect.box H I J = Ψ(I × J)` (as the preimage under the coordinates), `Rect.mem_box`,
  `Rect.chart_mem_box`, `Rect.box_inter`, `Rect.box_mono`;
* `Rect.volume_box`: `|Ψ(I × J)| = |I| |J|`; `Rect.volume_box_singleton_left/right`: segments are
  null;
* `Rect.setIntegral_box`, `Rect.integrableOn_box_iff`: integrals over `Ψ(I × J)` in coordinates;
* `Rect.sub H u v w h`: the sub-rectangle `Ψ([u, u + w] × [v, v + h])` with the same frame, so that the
  rectangle solver `t2Field` applies to it (`Rect.carrier_sub`).
-/

open MeasureTheory Set
open scoped ENNReal

public section

namespace SandierSerfaty.Screening

/-- `volume (I ×ℂ J) = volume I * volume J`. -/
theorem volume_reProdIm (I J : Set ℝ) : volume (I ×ℂ J) = volume I * volume J := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage_equiv (I ×ℂ J)
  rw [Rect.preimage_symm_reProdIm] at h
  rw [← h, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, Measure.prod_prod]

namespace Rect

variable (H : Rect)

/-- The box `Ψ(I × J)` in the chart of `H`. -/
@[expose] def box (I J : Set ℝ) : Set ℂ := H.coords ⁻¹' (I ×ℂ J)

variable {H} {I J I' J' : Set ℝ} {x : ℂ}

theorem mem_box : x ∈ H.box I J ↔ (H.coords x).re ∈ I ∧ (H.coords x).im ∈ J := Iff.rfl

theorem chart_mem_box {w : ℂ} : H.chart w ∈ H.box I J ↔ w.re ∈ I ∧ w.im ∈ J := by
  rw [mem_box, coords_chart]

theorem carrier_eq_box : H.carrier = H.box (Icc 0 H.width) (Icc 0 H.height) := rfl

theorem box_inter : H.box I J ∩ H.box I' J' = H.box (I ∩ I') (J ∩ J') := by
  ext x; simp only [mem_inter_iff, mem_box]; tauto

theorem box_mono (hI : I ⊆ I') (hJ : J ⊆ J') : H.box I J ⊆ H.box I' J' :=
  fun _ hx => ⟨hI hx.1, hJ hx.2⟩

theorem box_union_left : H.box (I ∪ I') J = H.box I J ∪ H.box I' J := by
  ext x; simp only [mem_union, mem_box]; tauto

theorem box_union_right : H.box I (J ∪ J') = H.box I J ∪ H.box I J' := by
  ext x; simp only [mem_union, mem_box]; tauto

theorem measurableSet_box (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    MeasurableSet (H.box I J) :=
  (hI.preimage Complex.measurable_re).inter (hJ.preimage Complex.measurable_im) |>.preimage
    H.continuous_coords.measurable

variable (H)

/-- The coordinates as a measurable equivalence. -/
@[expose] noncomputable def coordsEquiv : ℂ ≃ᵐ ℂ := H.chartHomeomorph.toMeasurableEquiv.symm

theorem coe_coordsEquiv : ⇑H.coordsEquiv = H.coords := by
  ext1 x
  show H.chartHomeomorph.symm x = H.coords x
  apply H.chartHomeomorph.injective
  rw [Homeomorph.apply_symm_apply, coe_chartHomeomorph, chart_coords]

theorem measurePreserving_coordsEquiv : MeasurePreserving H.coordsEquiv volume volume :=
  MeasurePreserving.symm _ H.measurePreserving_chart

theorem preimage_chart_box (I J : Set ℝ) : H.chart ⁻¹' H.box I J = I ×ℂ J := by
  ext w; simp only [mem_preimage, chart_mem_box]; exact Iff.rfl

theorem volume_box (I J : Set ℝ) : volume (H.box I J) = volume I * volume J := by
  rw [box, ← coe_coordsEquiv, H.measurePreserving_coordsEquiv.measure_preimage_equiv,
    volume_reProdIm]

theorem setIntegral_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E)
    (I J : Set ℝ) : ∫ x in H.box I J, F x = ∫ p in I ×ˢ J, F (H.chart ⟨p.1, p.2⟩) := by
  rw [← H.measurePreserving_chart.setIntegral_preimage_emb H.measurableEmbedding_chart,
    preimage_chart_box, setIntegral_reProdIm]

theorem setLIntegral_box (F : ℂ → ℝ≥0∞) (I J : Set ℝ) :
    ∫⁻ x in H.box I J, F x = ∫⁻ p in I ×ˢ J, F (H.chart ⟨p.1, p.2⟩) := by
  rw [← H.measurePreserving_chart.setLIntegral_comp_preimage_emb H.measurableEmbedding_chart,
    preimage_chart_box, setLIntegral_reProdIm]

theorem integrableOn_box_iff {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) (I J : Set ℝ) :
    IntegrableOn F (H.box I J) ↔
      IntegrableOn (fun p : ℝ × ℝ => F (H.chart ⟨p.1, p.2⟩)) (I ×ˢ J) := by
  rw [← H.measurePreserving_chart.integrableOn_comp_preimage H.measurableEmbedding_chart,
    preimage_chart_box, integrableOn_reProdIm_iff]
  rfl

/-- **Fubini on a box**: `∫_{Ψ([x, y] × [v₁, v₂])} F = ∫_x^y ∫_{v₁}^{v₂} F(Ψ(s, r)) dr ds`. -/
theorem setIntegral_box_Icc {x y v₁ v₂ : ℝ} (hxy : x ≤ y) (hv : v₁ ≤ v₂) {F : ℂ → ℝ}
    (hF : IntegrableOn F (H.box (Icc x y) (Icc v₁ v₂))) :
    ∫ z in H.box (Icc x y) (Icc v₁ v₂), F z =
      ∫ s in x..y, ∫ r in v₁..v₂, F (H.chart ⟨s, r⟩) := by
  have hF' := (H.integrableOn_box_iff F _ _).1 hF
  rw [setIntegral_box, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod _ hF', intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [intervalIntegral.integral_of_le hv, ← integral_Icc_eq_integral_Ioc]

/-- The line integrals `s ↦ ∫_{v₁}^{v₂} F(Ψ(s, r)) dr` are integrable on `[x, y]`. -/
theorem integrableOn_line_box {x y v₁ v₂ : ℝ} (hv : v₁ ≤ v₂) {F : ℂ → ℝ}
    (hF : IntegrableOn F (H.box (Icc x y) (Icc v₁ v₂))) :
    IntegrableOn (fun s => ∫ r in v₁..v₂, F (H.chart ⟨s, r⟩)) (Icc x y) := by
  have hF' := (H.integrableOn_box_iff F _ _).1 hF
  have h2 : Integrable (fun p : ℝ × ℝ => F (H.chart ⟨p.1, p.2⟩))
      ((volume.restrict (Icc x y)).prod (volume.restrict (Icc v₁ v₂))) := by
    rw [Measure.prod_restrict]; exact hF'
  refine h2.integral_prod_left.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [intervalIntegral.integral_of_le hv, ← integral_Icc_eq_integral_Ioc]

theorem volume_real_box (I J : Set ℝ) :
    volume.real (H.box I J) = volume.real I * volume.real J := by
  simp only [Measure.real, volume_box, ENNReal.toReal_mul]

theorem volume_box_singleton_left (u : ℝ) (J : Set ℝ) : volume (H.box {u} J) = 0 := by
  rw [volume_box, Real.volume_singleton, zero_mul]

theorem volume_box_singleton_right (I : Set ℝ) (v : ℝ) : volume (H.box I {v}) = 0 := by
  rw [volume_box, Real.volume_singleton, mul_zero]

theorem volume_box_Icc (a b a' b' : ℝ) :
    volume (H.box (Icc a b) (Icc a' b')) = ENNReal.ofReal (b - a) * ENNReal.ofReal (b' - a') := by
  rw [volume_box, Real.volume_Icc, Real.volume_Icc]

/-! ### Sub-rectangles -/

/-- The sub-rectangle `Ψ([u, u + w] × [v, v + h])` of `H`, with the frame of `H`. -/
@[expose] def sub (u v w h : ℝ) : Rect := ⟨H.chart ⟨u, v⟩, H.frame, w, h⟩

variable {u v w h : ℝ}

@[simp] theorem sub_frame : (H.sub u v w h).frame = H.frame := rfl

@[simp] theorem sub_width : (H.sub u v w h).width = w := rfl

@[simp] theorem sub_height : (H.sub u v w h).height = h := rfl

theorem chart_sub (z : ℂ) : (H.sub u v w h).chart z = H.chart (⟨u, v⟩ + z) := by
  simp only [chart, sub, map_add]; abel

theorem coords_sub (x : ℂ) : (H.sub u v w h).coords x = H.coords x - ⟨u, v⟩ := by
  apply (H.sub u v w h).chartHomeomorph.injective
  simp only [coe_chartHomeomorph, chart_coords, chart_sub, add_sub_cancel]

theorem carrier_sub : (H.sub u v w h).carrier = H.box (Icc u (u + w)) (Icc v (v + h)) := by
  ext x
  simp only [carrier, std, mem_preimage, coords_sub, Complex.mem_reProdIm, Complex.sub_re,
    Complex.sub_im, mem_box, mem_Icc, sub_width, sub_height]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The open rectangle `Ψ((0, a) × (0, b))`. -/
@[expose] def openCarrier : Set ℂ := H.box (Ioo 0 H.width) (Ioo 0 H.height)

theorem openCarrier_sub :
    (H.sub u v w h).openCarrier = H.box (Ioo u (u + w)) (Ioo v (v + h)) := by
  ext x
  simp only [openCarrier, mem_box, coords_sub, Complex.sub_re, Complex.sub_im, mem_Ioo, sub_width,
    sub_height]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem openCarrier_subset_carrier : H.openCarrier ⊆ H.carrier :=
  box_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

end Rect

end SandierSerfaty.Screening

end
