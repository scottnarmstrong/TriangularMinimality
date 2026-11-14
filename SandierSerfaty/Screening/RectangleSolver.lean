/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.RectangleEnergy
public import SandierSerfaty.Screening.LipschitzApprox

/-!
# The rectangle solver T2 (screening note, Lemma 4.4, rectangle solver)

The screening note, Lemma 4.4 (`lem:T2`), with a generalized
rectangle: the rectangle is the image of `[0, a] × [0, b]` under an
**arbitrary affine isometry** `x = z₀ + M(s + i r)`, `M` orthogonal (possibly orientation-reversing, as
the pinwheel charts of the screening note Def. 4.13 are), and the field is pushed forward as `M (A + i B)`.

* `SandierSerfaty.Screening.Rect`: origin `z₀`, frame `M : ℂ ≃ₗᵢ[ℝ] ℂ`, width `a`, height `b`;
  `Rect.carrier` is the closed rectangle, `Rect.src f (s, r) = f (z₀ + M(s + i r))` the source in
  coordinates;
* `SandierSerfaty.Screening.t2Field H f = M (A + i B) 1_H`, with `A`, `B` of
  `SandierSerfaty.Screening.RectangleCore` for the source `Rect.src f`.

Main results (`f ∈ L¹(H)` real with `∫_H f = 0`, `a, b > 0`):

* `integral_inner_t2Field` (Lemma 4.4(b)): for **every** Lipschitz `φ` on `ℂ` (no support condition)
  `∫_ℂ ⟪T2_H[f], ∇φ⟫ = -∫_H f φ`, i.e. `div T2_H[f] = f 1_H` in `𝒟'(ℂ)` with zero normal flux;
* `lintegral_norm_sq_t2Field`, `lintegral_norm_sq_t2Field_le'` (Lemma 4.4(a)):
  `∫ |T2_H[f]|² ≤ (a/b)(∫₀ᵃ G)² + 4b ∫₀ᵃ G² ≤ (a²/b + 4b) ∫₀ᵃ G²`, `G(s) = ∫₀ᵇ |f(z₀ + M(s + i r))| dr`;
* `t2Field_eq_zero_of_notMem`, `integrable_t2Field`: the values; the pointwise
  bounds and end values of Lemma 4.4(a) and Lemma 4.4(c) are `T2.abs_compA_le`, `T2.abs_compB_le`,
  `T2.compB_height`, `T2.compA_eq_zero_of_line`,
  `T2.compB_eq_of_line` applied to `Rect.src f`.

For Lipschitz `φ` the identity is proved for mollifications of `φ` (Fubini and the fundamental theorem
of calculus applied to the smooth test function only, `T2.integral_core`) and passed to the limit.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal ContDiff

public section

namespace SandierSerfaty.Screening

/-! ### Rectangles with an orthogonal frame -/

/-- A closed rectangle `{z₀ + M(s + i r) : 0 ≤ s ≤ a, 0 ≤ r ≤ b}`: origin `z₀`, orthogonal frame `M`
(a linear isometry of `ℂ`, possibly orientation-reversing; as in the screening note, Lemma 4.4 generalized), width `a` (along
`s`) and height `b` (along `r`). -/
structure Rect where
  /-- the corner `z₀` -/
  origin : ℂ
  /-- the orthogonal frame `M` -/
  frame : ℂ ≃ₗᵢ[ℝ] ℂ
  /-- the side `a` along the first coordinate `s` -/
  width : ℝ
  /-- the side `b` along the second coordinate `r` -/
  height : ℝ

namespace Rect

variable (H : Rect)

/-- The chart `w ↦ z₀ + M w` (`w = s + i r`). -/
@[expose] def chart (w : ℂ) : ℂ := H.origin + H.frame w

/-- The coordinates `x ↦ M⁻¹(x - z₀)`. -/
@[expose] noncomputable def coords (x : ℂ) : ℂ := H.frame.symm (x - H.origin)

/-- The standard rectangle `[0, a] × [0, b]` in the coordinates `w = s + i r`. -/
@[expose] def std : Set ℂ := Icc 0 H.width ×ℂ Icc 0 H.height

/-- The closed rectangle `z₀ + M([0, a] × [0, b])`. -/
@[expose] def carrier : Set ℂ := H.coords ⁻¹' H.std

/-- The source in the coordinates `(s, r)`. -/
@[expose] def src (f : ℂ → ℝ) (p : ℝ × ℝ) : ℝ := f (H.chart ⟨p.1, p.2⟩)

theorem coords_chart (w : ℂ) : H.coords (H.chart w) = w := by
  simp [coords, chart]

theorem chart_coords (x : ℂ) : H.chart (H.coords x) = x := by
  simp [coords, chart]

theorem chart_mem_carrier_iff {w : ℂ} : H.chart w ∈ H.carrier ↔ w ∈ H.std := by
  simp only [carrier, mem_preimage, coords_chart]

theorem preimage_chart_carrier : H.chart ⁻¹' H.carrier = H.std := by
  ext w; exact H.chart_mem_carrier_iff

theorem isClosed_std : IsClosed H.std := isClosed_Icc.reProdIm isClosed_Icc

theorem isCompact_std : IsCompact H.std := isCompact_Icc.reProdIm isCompact_Icc

/-- The chart as a homeomorphism. -/
@[expose] noncomputable def chartHomeomorph : ℂ ≃ₜ ℂ := H.frame.toHomeomorph.trans (Homeomorph.addLeft H.origin)

theorem coe_chartHomeomorph : ⇑H.chartHomeomorph = H.chart := rfl

theorem continuous_chart : Continuous H.chart := H.chartHomeomorph.continuous

theorem continuous_coords : Continuous H.coords := by
  unfold coords; fun_prop

theorem isometry_chart : Isometry H.chart :=
  (isometry_add_left H.origin).comp H.frame.isometry

theorem measurableEmbedding_chart : MeasurableEmbedding H.chart :=
  H.chartHomeomorph.measurableEmbedding

theorem measurePreserving_chart : MeasurePreserving H.chart volume volume :=
  (measurePreserving_add_left volume H.origin).comp H.frame.measurePreserving

theorem isClosed_carrier : IsClosed H.carrier := H.isClosed_std.preimage H.continuous_coords

theorem measurableSet_carrier : MeasurableSet H.carrier := H.isClosed_carrier.measurableSet

theorem isCompact_carrier : IsCompact H.carrier := by
  have h : H.carrier = H.chartHomeomorph '' H.std := by
    ext x
    refine ⟨fun hx => ⟨H.coords x, hx, H.chart_coords x⟩, ?_⟩
    rintro ⟨w, hw, rfl⟩
    exact H.chart_mem_carrier_iff.2 hw
  rw [h]
  exact H.isCompact_std.image H.chartHomeomorph.continuous

/-! #### Change of variables -/

/-- `ℂ ≃ ℝ × ℝ` on a product rectangle. -/
theorem preimage_symm_reProdIm (s t : Set ℝ) :
    Complex.measurableEquivRealProd.symm ⁻¹' (s ×ℂ t) = s ×ˢ t := by
  ext p
  simp only [mem_preimage, Complex.measurableEquivRealProd_symm_apply, mem_prod]
  exact Iff.rfl

theorem setIntegral_reProdIm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E)
    (s t : Set ℝ) : ∫ w in s ×ℂ t, F w = ∫ p in s ×ˢ t, F ⟨p.1, p.2⟩ := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding F (s ×ℂ t)
  rw [preimage_symm_reProdIm] at h
  rw [← h]
  rfl

theorem setLIntegral_reProdIm (F : ℂ → ℝ≥0∞) (s t : Set ℝ) :
    ∫⁻ w in s ×ℂ t, F w = ∫⁻ p in s ×ˢ t, F ⟨p.1, p.2⟩ := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding F (s ×ℂ t)
  rw [preimage_symm_reProdIm] at h
  rw [← h]
  rfl

theorem integrableOn_reProdIm_iff {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) (s t : Set ℝ) :
    IntegrableOn F (s ×ℂ t) ↔ IntegrableOn (fun p : ℝ × ℝ => F ⟨p.1, p.2⟩) (s ×ˢ t) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding (f := F) (s := s ×ℂ t)
  rw [preimage_symm_reProdIm] at h
  rw [← h]
  rfl

theorem setIntegral_carrier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E) :
    ∫ x in H.carrier, F x = ∫ p in Icc 0 H.width ×ˢ Icc 0 H.height, F (H.chart ⟨p.1, p.2⟩) := by
  rw [← H.measurePreserving_chart.setIntegral_preimage_emb H.measurableEmbedding_chart,
    preimage_chart_carrier, std, setIntegral_reProdIm]

theorem integrableOn_carrier_iff {E : Type*} [NormedAddCommGroup E] (F : ℂ → E) :
    IntegrableOn F H.carrier ↔
      IntegrableOn (fun p : ℝ × ℝ => F (H.chart ⟨p.1, p.2⟩)) (Icc 0 H.width ×ˢ Icc 0 H.height) := by
  rw [← H.measurePreserving_chart.integrableOn_comp_preimage H.measurableEmbedding_chart,
    preimage_chart_carrier, std, integrableOn_reProdIm_iff]
  rfl

theorem integrableOn_src {f : ℂ → ℝ} (hf : IntegrableOn f H.carrier) :
    IntegrableOn (H.src f) (Icc 0 H.width ×ˢ Icc 0 H.height) :=
  (H.integrableOn_carrier_iff f).1 hf

theorem integral_src (f : ℂ → ℝ) :
    ∫ p in Icc 0 H.width ×ˢ Icc 0 H.height, H.src f p = ∫ x in H.carrier, f x :=
  (H.setIntegral_carrier f).symm

/-- The gradient of `φ ∘ chart` is `M⁻¹ ∇φ ∘ chart`. -/
theorem gradient_comp_chart (φ : ℂ → ℝ) (w : ℂ) :
    gradient (fun w => φ (H.chart w)) w = H.frame.symm (gradient φ (H.chart w)) := by
  refine ext_inner_right ℝ fun v => ?_
  have hcomp : (fun w => φ (H.chart w)) =
      (fun y => φ (H.origin + y)) ∘ H.frame.toLinearIsometry.toContinuousLinearMap := rfl
  rw [inner_gradient_left, ← H.frame.inner_map_map, H.frame.apply_symm_apply,
    inner_gradient_left]
  have h := ContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ)
    (f := fun y => φ (H.origin + y)) (x := w) H.frame.toContinuousLinearEquiv
  have h' : (fun w => φ (H.chart w)) = (fun y => φ (H.origin + y)) ∘ H.frame.toContinuousLinearEquiv :=
    rfl
  rw [h', h, fderiv_comp_add_left]
  rfl

theorem lipschitzWith_comp_chart {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    LipschitzWith K fun w => φ (H.chart w) := by
  have h := hφ.comp H.isometry_chart.lipschitzWith
  rw [mul_one] at h
  exact h

end Rect

/-! ### The field in the standard frame -/

namespace T2

/-- The T2 field in the standard frame: `A(s) + i B(s, r)` on `[0, a] × [0, b]`, `0` outside. -/
@[expose] noncomputable def stdField (a b : ℝ) (g : ℝ × ℝ → ℝ) (w : ℂ) : ℂ :=
  (Icc 0 a ×ℂ Icc 0 b).indicator (fun w => vec b g (w.re, w.im)) w

theorem integrable_stdField {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) : Integrable (stdField a b g) := by
  unfold stdField
  rw [integrable_indicator_iff (isClosed_Icc.reProdIm isClosed_Icc).measurableSet,
    Rect.integrableOn_reProdIm_iff]
  exact integrableOn_vec ha hb hg

theorem inner_vec (b : ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (z : ℂ) :
    inner ℝ (vec b g p) z = compA b g p.1 * z.re + compB b g p.1 p.2 * z.im := by
  simp [vec, Complex.inner]; ring

theorem hasDerivAt_mk_re (r s : ℝ) : HasDerivAt (fun s : ℝ => (⟨s, r⟩ : ℂ)) 1 s := by
  have h := ((hasDerivAt_id s).ofReal_comp).add_const ((r : ℂ) * Complex.I)
  simp only [id, Complex.ofReal_one] at h
  convert h using 1
  funext s
  exact Complex.mk_eq_add_mul_I s r

theorem hasDerivAt_mk_im (s r : ℝ) : HasDerivAt (fun r : ℝ => (⟨s, r⟩ : ℂ)) Complex.I r := by
  have h := (((hasDerivAt_id r).ofReal_comp).mul_const Complex.I).const_add (s : ℂ)
  simp only [id, Complex.ofReal_one, one_mul] at h
  convert h using 1
  funext r
  exact Complex.mk_eq_add_mul_I s r

theorem continuous_mk : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := by
  simp_rw [Complex.mk_eq_add_mul_I]; fun_prop

/-- **The weak identity of T2 for `C¹` test functions** in the standard frame. -/
theorem integral_inner_stdField_of_contDiff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) (h0 : ∫ p in Icc 0 a ×ˢ Icc 0 b, g p = 0)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ w, inner ℝ (stdField a b g w) (gradient φ w) =
      -∫ p in Icc 0 a ×ˢ Icc 0 b, g p * φ ⟨p.1, p.2⟩ := by
  have hS : MeasurableSet (Icc 0 a ×ℂ Icc 0 b) := (isClosed_Icc.reProdIm isClosed_Icc).measurableSet
  have hind : (fun w => inner ℝ (stdField a b g w) (gradient φ w)) =
      (Icc 0 a ×ℂ Icc 0 b).indicator fun w => inner ℝ (vec b g (w.re, w.im)) (gradient φ w) := by
    ext w
    by_cases hw : w ∈ Icc 0 a ×ℂ Icc 0 b
    · rw [stdField, indicator_of_mem hw, indicator_of_mem hw]
    · rw [stdField, indicator_of_notMem hw, indicator_of_notMem hw, inner_zero_left]
  rw [hind, integral_indicator hS, Rect.setIntegral_reProdIm]
  have hD : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hDc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hpt : ∀ p : ℝ × ℝ, inner ℝ (vec b g ((⟨p.1, p.2⟩ : ℂ).re, (⟨p.1, p.2⟩ : ℂ).im))
      (gradient φ ⟨p.1, p.2⟩) = compA b g p.1 * fderiv ℝ φ ⟨p.1, p.2⟩ 1 +
        compB b g p.1 p.2 * fderiv ℝ φ ⟨p.1, p.2⟩ Complex.I := by
    intro p
    have h1 : ∀ z, (gradient φ z).re = fderiv ℝ φ z 1 := fun z => by
      rw [← inner_gradient_left, Complex.inner]; simp
    have h2 : ∀ z, (gradient φ z).im = fderiv ℝ φ z Complex.I := fun z => by
      rw [← inner_gradient_left, Complex.inner]; simp
    rw [inner_vec, h1, h2]
  simp only [hpt]
  exact integral_core ha hb hg h0 (hφ.continuous.comp continuous_mk)
    ((hDc.comp continuous_mk).clm_apply continuous_const)
    ((hDc.comp continuous_mk).clm_apply continuous_const)
    (fun s r => (hD _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_mk_re r s))
    (fun s r => (hD _).hasFDerivAt.comp_hasDerivAt r (hasDerivAt_mk_im s r))

/-- **The weak identity of T2 for Lipschitz test functions** in the standard frame. -/
theorem integral_inner_stdField {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) (h0 : ∫ p in Icc 0 a ×ˢ Icc 0 b, g p = 0)
    {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∫ w, inner ℝ (stdField a b g w) (gradient φ w) =
      -∫ p in Icc 0 a ×ˢ Icc 0 b, g p * φ ⟨p.1, p.2⟩ := by
  obtain ⟨ψ, δ, hδ, hψ, hψφ, hψB, hlim⟩ := exists_smooth_approx_lipschitz hφ
  have hL := tendsto_integral_inner_gradient MeasurableSet.univ
    (integrable_stdField ha.le hb hg).integrableOn
    (fun n x hx => absurd (mem_univ x) hx) hψB hlim
  have hEq : ∀ n, ∫ w, inner ℝ (stdField a b g w) (gradient (ψ n) w) =
      -∫ p in Icc 0 a ×ˢ Icc 0 b, g p * ψ n ⟨p.1, p.2⟩ := fun n =>
    integral_inner_stdField_of_contDiff ha hb hg h0 ((hψ n).of_le (by simp))
  simp only [hEq] at hL
  refine tendsto_nhds_unique hL (Tendsto.neg ?_)
  exact tendsto_setIntegral_mul_of_approx (isCompact_Icc.prod isCompact_Icc) hg
    (fun n => (hψ n).continuous.comp continuous_mk) (hφ.continuous.comp continuous_mk) hδ
    (fun n p => hψφ n _)

end T2

/-! ### The field on a rectangle with an orthogonal frame -/

/-- **The rectangle solver** `T2_H[f] = M (A + i B) 1_H` (screening note, Lemma 4.4, for an arbitrary orthogonal frame), `A`, `B`
computed from the source in coordinates `Rect.src f`. -/
@[expose] noncomputable def t2Field (H : Rect) (f : ℂ → ℝ) (x : ℂ) : ℂ :=
  H.carrier.indicator
    (fun x => H.frame (T2.vec H.height (H.src f) ((H.coords x).re, (H.coords x).im))) x

namespace Rect

variable (H : Rect) (f : ℂ → ℝ)

theorem t2Field_chart_eq_stdField (w : ℂ) :
    t2Field H f (H.chart w) = H.frame (T2.stdField H.width H.height (H.src f) w) := by
  by_cases hw : w ∈ H.std
  · rw [t2Field, indicator_of_mem (H.chart_mem_carrier_iff.2 hw), T2.stdField,
      indicator_of_mem (show w ∈ Icc 0 H.width ×ℂ Icc 0 H.height from hw), coords_chart]
  · rw [t2Field, indicator_of_notMem (fun h => hw (H.chart_mem_carrier_iff.1 h)), T2.stdField,
      indicator_of_notMem (show w ∉ Icc 0 H.width ×ℂ Icc 0 H.height from hw), map_zero]

end Rect

theorem t2Field_eq_zero_of_notMem (H : Rect) (f : ℂ → ℝ) {x : ℂ} (hx : x ∉ H.carrier) :
    t2Field H f x = 0 := indicator_of_notMem hx _

theorem integrable_t2Field (H : Rect) (ha : 0 ≤ H.width) (hb : 0 < H.height) {f : ℂ → ℝ}
    (hf : IntegrableOn f H.carrier) : Integrable (t2Field H f) := by
  have h := (T2.integrable_stdField ha hb (H.integrableOn_src hf)).norm
  rw [← H.measurePreserving_chart.integrable_comp_emb H.measurableEmbedding_chart]
  refine Integrable.mono' h ?_ (Eventually.of_forall fun w => ?_)
  · have hm : AEStronglyMeasurable (fun w => H.frame (T2.stdField H.width H.height (H.src f) w))
        volume :=
      H.frame.continuous.comp_aestronglyMeasurable
        (T2.integrable_stdField ha hb (H.integrableOn_src hf)).aestronglyMeasurable
    exact hm.congr (Eventually.of_forall fun w => (H.t2Field_chart_eq_stdField f w).symm)
  · simp only [Function.comp_apply, H.t2Field_chart_eq_stdField, LinearIsometryEquiv.norm_map,
      le_refl]

/-- **The weak identity of T2** (screening note, Lemma 4.4(b), for an arbitrary orthogonal frame): for `f ∈ L¹(H)` with
`∫_H f = 0` and every Lipschitz `φ` on `ℂ` (no support condition),
`∫_ℂ ⟪T2_H[f], ∇φ⟫ = -∫_H f φ`, i.e. `div T2_H[f] = f 1_H` in `𝒟'(ℂ)` (zero normal flux). -/
theorem integral_inner_t2Field (H : Rect) (ha : 0 < H.width) (hb : 0 < H.height) {f : ℂ → ℝ}
    (hf : IntegrableOn f H.carrier) (h0 : ∫ x in H.carrier, f x = 0) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (t2Field H f x) (gradient φ x) = -∫ x in H.carrier, f x * φ x := by
  have hg := H.integrableOn_src hf
  have h0' : ∫ p in Icc 0 H.width ×ˢ Icc 0 H.height, H.src f p = 0 := by
    rw [H.integral_src]; exact h0
  rw [← H.measurePreserving_chart.integral_comp H.measurableEmbedding_chart]
  have hpt : ∀ w, inner ℝ (t2Field H f (H.chart w)) (gradient φ (H.chart w)) =
      inner ℝ (T2.stdField H.width H.height (H.src f) w)
        (gradient (fun w => φ (H.chart w)) w) := by
    intro w
    rw [H.t2Field_chart_eq_stdField, H.gradient_comp_chart,
      ← H.frame.inner_map_map (T2.stdField H.width H.height (H.src f) w),
      H.frame.apply_symm_apply]
  simp only [hpt]
  rw [T2.integral_inner_stdField ha hb hg h0' (H.lipschitzWith_comp_chart hφ),
    H.setIntegral_carrier]
  rfl

/-- **Energy bound of T2** (screening note, Lemma 4.4(a), first form):
`∫ |T2_H[f]|² ≤ (a/b) (∫₀ᵃ G)² + 4b ∫₀ᵃ G²`, `G(s) = ∫₀ᵇ |f(z₀ + M(s + i r))| dr`. -/
theorem lintegral_norm_sq_t2Field (H : Rect) (ha : 0 ≤ H.width) (hb : 0 < H.height) {f : ℂ → ℝ}
    (hf : IntegrableOn f H.carrier) :
    ∫⁻ x, ENNReal.ofReal (‖t2Field H f x‖ ^ 2) ≤
      ENNReal.ofReal (H.width / H.height *
          (∫ s in (0 : ℝ)..H.width, T2.lineAbs H.height (H.src f) s) ^ 2) +
        ENNReal.ofReal (4 * H.height) *
          ∫⁻ s in Icc 0 H.width, ENNReal.ofReal (T2.lineAbs H.height (H.src f) s ^ 2) := by
  refine le_of_eq_of_le ?_ (T2.lintegral_sq_le ha hb (H.integrableOn_src hf))
  rw [← H.measurePreserving_chart.lintegral_comp_emb H.measurableEmbedding_chart]
  simp only [H.t2Field_chart_eq_stdField, LinearIsometryEquiv.norm_map]
  have hind : (fun w => ENNReal.ofReal (‖T2.stdField H.width H.height (H.src f) w‖ ^ 2)) =
      (Icc 0 H.width ×ℂ Icc 0 H.height).indicator
        fun w => ENNReal.ofReal (‖T2.vec H.height (H.src f) (w.re, w.im)‖ ^ 2) := by
    ext w
    by_cases hw : w ∈ Icc 0 H.width ×ℂ Icc 0 H.height
    · simp [T2.stdField, indicator_of_mem hw]
    · simp [T2.stdField, indicator_of_notMem hw]
  rw [hind, lintegral_indicator (isClosed_Icc.reProdIm isClosed_Icc).measurableSet,
    Rect.setLIntegral_reProdIm]
  simp only [T2.norm_vec_sq]

/-- **Energy bound of T2** (screening note, Lemma 4.4(a), second form): `∫ |T2_H[f]|² ≤ (a²/b + 4b) ∫₀ᵃ G²`. -/
theorem lintegral_norm_sq_t2Field_le' (H : Rect) (ha : 0 < H.width) (hb : 0 < H.height)
    {f : ℂ → ℝ} (hf : IntegrableOn f H.carrier) :
    ∫⁻ x, ENNReal.ofReal (‖t2Field H f x‖ ^ 2) ≤
      ENNReal.ofReal (H.width ^ 2 / H.height + 4 * H.height) *
        ∫⁻ s in Icc 0 H.width, ENNReal.ofReal (T2.lineAbs H.height (H.src f) s ^ 2) := by
  refine le_of_eq_of_le ?_ (T2.lintegral_sq_le' ha hb (H.integrableOn_src hf))
  rw [← H.measurePreserving_chart.lintegral_comp_emb H.measurableEmbedding_chart]
  simp only [H.t2Field_chart_eq_stdField, LinearIsometryEquiv.norm_map]
  have hind : (fun w => ENNReal.ofReal (‖T2.stdField H.width H.height (H.src f) w‖ ^ 2)) =
      (Icc 0 H.width ×ℂ Icc 0 H.height).indicator
        fun w => ENNReal.ofReal (‖T2.vec H.height (H.src f) (w.re, w.im)‖ ^ 2) := by
    ext w
    by_cases hw : w ∈ Icc 0 H.width ×ℂ Icc 0 H.height
    · simp [T2.stdField, indicator_of_mem hw]
    · simp [T2.stdField, indicator_of_notMem hw]
  rw [hind, lintegral_indicator (isClosed_Icc.reProdIm isClosed_Icc).measurableSet,
    Rect.setLIntegral_reProdIm]
  simp only [T2.norm_vec_sq]

end SandierSerfaty.Screening

end
