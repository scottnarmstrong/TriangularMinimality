/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.FillerPartition
public import SandierSerfaty.Screening.FieldGluing
public import SandierSerfaty.Screening.RectangleEnergy

/-!
# Piece fields (screening note, Lemma 4.22)

The screening note, Lemma 4.22 (`lem:piece`). Let `P` be a piece of the filler
partition (Lemma 4.21): a rectangle (`Rect`, any orthogonal frame) with sides `a' ∈ [1/(6√m), 6/√m]`,
`b' ∈ [1/(3√m), 4/√m]`, and `μ` measurable on `P` with `m/2 ≤ μ ≤ 3m/2` a.e. and `∫_P μ = 1`
(`Rect.IsFillerPiece`). Let `z` be its centre (`Rect.centre`), `0 < r₀ ≤ 1/(16√m)`, `u_z = u^{r₀}(· - z)`
and `Ψ_P = K^{r₀}(· - z) + T2_P[2π(μ - u_z)]` (`Rect.pieceField`). Then:

* `IsFillerPiece.closedBall_subset_openCarrier`: `B̄(z, r₀) ⊆ int P`;
* `IsFillerPiece.integral_inner_pieceField`: `∫ ⟪Ψ_P, ∇φ⟫ = 2π(φ(z) - ∫_P μ φ)` for every Lipschitz `φ`;
  `IsFillerPiece.isFieldPiece_pieceField`: `Ψ_P` is a field piece with charge `z` and source `2πμ 1_P`;
* `IsFillerPiece.lintegral_norm_sq_pieceField_sub_le`:
  `∫ |Ψ_P - ∇f_{r₀}(· - z)|² ≤ 2(π/2 + e_T(m))`, `e_T(m) = 1056π² + 256π/(r₀√m)`.

`IsFillerPartition.isFillerPiece`: the pieces of Lemma 4.21 are filler pieces.
-/

open MeasureTheory Metric Set Real Filter
open scoped ENNReal NNReal

public section

namespace SandierSerfaty.Screening

namespace Rect

variable (P : Rect)

/-- The centre `z = Ψ(a'/2, b'/2)` of the rectangle. -/
@[expose] noncomputable def centre : ℂ := P.chart ⟨P.width / 2, P.height / 2⟩

/-- The source `2π(μ - u_z)` of the T2 part of a piece field. -/
@[expose] noncomputable def pieceSrc (r : ℝ) (μ : ℂ → ℝ) (x : ℂ) : ℝ :=
  2 * π * (μ x - radialU r (x - P.centre))

/-- The piece field `Ψ_P = K^{r}(· - z) + T2_P[2π(μ - u_z)]` (screening note, Lemma 4.22). -/
@[expose] noncomputable def pieceField (r : ℝ) (μ : ℂ → ℝ) (x : ℂ) : ℂ :=
  radialK r (x - P.centre) + t2Field P (P.pieceSrc r μ) x

/-- The hypotheses of the screening note's Lemma 4.22 on a piece (the conclusions of Lemma 4.21). -/
structure IsFillerPiece (m : ℝ) (μ : ℂ → ℝ) : Prop where
  m_pos : 0 < m
  width_mem : P.width ∈ Icc (1 / (6 * √m)) (6 / √m)
  height_mem : P.height ∈ Icc (1 / (3 * √m)) (4 / √m)
  aestronglyMeasurable : AEStronglyMeasurable μ (volume.restrict P.carrier)
  bound : ∀ᵐ x, x ∈ P.carrier → μ x ∈ Icc (m / 2) (3 * m / 2)
  mass : ∫ x in P.carrier, μ x = 1

end Rect

theorem measurable_radialU (r : ℝ) : Measurable (radialU r) :=
  measurable_const.indicator measurableSet_ball

theorem radialU_le (r : ℝ) (y : ℂ) : radialU r y ≤ (π * r ^ 2)⁻¹ := by
  by_cases hy : y ∈ ball (0 : ℂ) r
  · rw [radialU_of_mem hy]
  · rw [radialU_of_notMem hy]; positivity

namespace Rect.IsFillerPiece

variable {P : Rect} {m : ℝ} {μ : ℂ → ℝ} (hP : P.IsFillerPiece m μ)
include hP

theorem sqrt_pos : 0 < √m := Real.sqrt_pos.2 hP.m_pos

theorem width_pos : 0 < P.width :=
  lt_of_lt_of_le (by have := hP.sqrt_pos; positivity) hP.width_mem.1

theorem height_pos : 0 < P.height :=
  lt_of_lt_of_le (by have := hP.sqrt_pos; positivity) hP.height_mem.1

theorem integrableOn : IntegrableOn μ P.carrier := by
  have : IsFiniteMeasure (volume.restrict P.carrier) :=
    isFiniteMeasure_restrict.2 P.isCompact_carrier.measure_lt_top.ne
  refine Integrable.mono' (integrable_const (3 * m / 2)) hP.aestronglyMeasurable ?_
  refine (ae_restrict_iff' P.measurableSet_carrier).2 (hP.bound.mono fun x hx hxP => ?_)
  have := hx hxP
  have := hP.m_pos
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this, (hx hxP).1, (hx hxP).2]

variable {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / (16 * √m))
include hr hr'

/-- `r₀ < a'/2` and `r₀ < b'/2`. -/
theorem lt_half : r < P.width / 2 ∧ r < P.height / 2 := by
  have hs := hP.sqrt_pos
  have h16 : r * (16 * √m) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hr'
  have hw : 1 ≤ P.width * (6 * √m) := by
    have := hP.width_mem.1; rwa [div_le_iff₀ (by positivity)] at this
  have hh : 1 ≤ P.height * (3 * √m) := by
    have := hP.height_mem.1; rwa [div_le_iff₀ (by positivity)] at this
  constructor <;> nlinarith

/-- **`B̄(z, r₀) ⊆ int P`** (screening note, Lemma 4.22). -/
theorem closedBall_subset_openCarrier : closedBall P.centre r ⊆ P.openCarrier := by
  intro y hy
  have hlt := hP.lt_half hr hr'
  have hz : P.coords P.centre = ⟨P.width / 2, P.height / 2⟩ := P.coords_chart _
  have hc : P.coords y - ⟨P.width / 2, P.height / 2⟩ = P.frame.symm (y - P.centre) := by
    rw [← hz, Rect.coords, Rect.coords, ← map_sub]
    congr 1; abel
  have hn : ‖P.coords y - ⟨P.width / 2, P.height / 2⟩‖ ≤ r := by
    rw [hc, LinearIsometryEquiv.norm_map, ← dist_eq_norm]; exact hy
  have h1 := (Complex.abs_re_le_norm _).trans hn
  have h2 := (Complex.abs_im_le_norm _).trans hn
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  rw [abs_le] at h1 h2
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, by linarith [h2.1], by linarith [h2.2]⟩

theorem radialU_eq_zero_of_notMem {x : ℂ} (hx : x ∉ P.carrier) :
    radialU r (x - P.centre) = 0 := by
  refine radialU_of_notMem fun hb => hx (P.openCarrier_subset_carrier
    (hP.closedBall_subset_openCarrier hr hr' ?_))
  rw [mem_ball, dist_zero_right] at hb
  rw [mem_closedBall, dist_eq_norm]; exact hb.le

/-- `∫_P u_z = 1`. -/
theorem setIntegral_radialU : ∫ x in P.carrier, radialU r (x - P.centre) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hP.radialU_eq_zero_of_notMem hr hr' hx,
    integral_sub_right_eq_self (fun y => radialU r y), integral_radialU hr]

theorem setIntegral_pieceSrc : ∫ x in P.carrier, P.pieceSrc r μ x = 0 := by
  have hu : IntegrableOn (fun x => radialU r (x - P.centre)) P.carrier :=
    ((integrable_radialU r).comp_sub_right _).integrableOn
  simp only [Rect.pieceSrc]
  rw [integral_const_mul, integral_sub hP.integrableOn hu, hP.mass, hP.setIntegral_radialU hr hr',
    sub_self, mul_zero]

omit hP hr hr' in
theorem integrableOn_pieceSrc_of (hμ : IntegrableOn μ P.carrier) :
    IntegrableOn (P.pieceSrc r μ) P.carrier :=
  (hμ.sub ((integrable_radialU r).comp_sub_right _).integrableOn).const_mul _

/-- **The screening note's Lemma 4.22, the identity**: `∫ ⟪Ψ_P, ∇φ⟫ = 2π(φ(z) - ∫_P μ φ)` for every Lipschitz `φ`. -/
theorem integral_inner_pieceField {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (P.pieceField r μ x) (gradient φ x) =
      2 * π * (φ P.centre - ∫ x in P.carrier, μ x * φ x) := by
  have hint := integrableOn_pieceSrc_of (r := r) hP.integrableOn
  have hb : ∀ x, ‖gradient φ x‖ ≤ K := fun x => norm_gradient_le_of_lipschitz hφ x
  have hi1 : Integrable fun x => inner ℝ (radialK r (x - P.centre)) (gradient φ x) :=
    integrable_inner_of_integrableOn MeasurableSet.univ
      ((integrable_radialK hr).comp_sub_right _).integrableOn (aestronglyMeasurable_gradient _) hb
      (fun x hx => absurd (mem_univ x) hx)
  have hi2 : Integrable fun x => inner ℝ (t2Field P (P.pieceSrc r μ) x) (gradient φ x) :=
    integrable_inner_of_integrableOn MeasurableSet.univ
      (integrable_t2Field P hP.width_pos.le hP.height_pos hint).integrableOn
      (aestronglyMeasurable_gradient _) hb (fun x hx => absurd (mem_univ x) hx)
  simp only [Rect.pieceField, inner_add_left]
  rw [integral_add hi1 hi2, integral_inner_radialK hr _ hφ,
    integral_inner_t2Field P hP.width_pos hP.height_pos hint (hP.setIntegral_pieceSrc hr hr') hφ]
  -- the two integrals against `φ`
  have hφc : ContinuousOn φ P.carrier := hφ.continuous.continuousOn
  have hμφ : IntegrableOn (fun x => μ x * φ x) P.carrier :=
    hP.integrableOn.mul_continuousOn hφc P.isCompact_carrier
  have huφ : IntegrableOn (fun x => radialU r (x - P.centre) * φ x) P.carrier :=
    ((integrable_radialU r).comp_sub_right _).integrableOn.mul_continuousOn hφc P.isCompact_carrier
  have hu : ∫ x, radialU r (x - P.centre) * φ x =
      ∫ x in P.carrier, radialU r (x - P.centre) * φ x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hP.radialU_eq_zero_of_notMem hr hr' hx, zero_mul]).symm
  have hsrc : ∫ x in P.carrier, P.pieceSrc r μ x * φ x =
      2 * π * ((∫ x in P.carrier, μ x * φ x) - ∫ x in P.carrier, radialU r (x - P.centre) * φ x) := by
    rw [← integral_sub hμφ huφ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Rect.pieceSrc]; ring
  rw [hu, hsrc]; ring

/-- `Ψ_P` is a field piece with charge `z` and source `2π μ 1_P`. -/
theorem isFieldPiece_pieceField :
    IsFieldPiece (P.pieceField r μ) {P.centre} (P.carrier.indicator fun x => 2 * π * μ x) := by
  have hint := integrableOn_pieceSrc_of (r := r) hP.integrableOn
  have h := (isFieldPiece_radialK hr P.centre).add
    (isFieldPiece_t2Field P hP.width_pos hP.height_pos hint (hP.setIntegral_pieceSrc hr hr'))
    (Finset.disjoint_empty_right _)
  rw [Finset.union_empty] at h
  convert h using 1
  · funext x; rfl
  ext x
  simp only [Pi.add_apply]
  by_cases hx : x ∈ P.carrier
  · rw [indicator_of_mem hx, indicator_of_mem hx, Rect.pieceSrc]; ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, hP.radialU_eq_zero_of_notMem hr hr' hx]
    ring

/-! ### The energy -/

omit hP hr' in
theorem integrable_norm_sq_radialW : Integrable fun y => ‖radialW r y‖ ^ 2 := by
  refine Integrable.mono' ((integrable_radialW hr).norm.const_mul r⁻¹)
    ((measurable_radialW r).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (norm_radialW_le hr y) (norm_nonneg _)

omit hr' in
/-- The a.e. bound on the line integrals: `G(s) ≤ 3πm b' + 4/r₀` for a.e. `s ∈ [0, a']`. -/
theorem ae_lineAbs_le :
    ∀ᵐ s ∂(volume.restrict (Icc 0 P.width)),
      T2.lineAbs P.height (P.src (P.pieceSrc r μ)) s ≤ 3 * π * m * P.height + 4 / r := by
  have hb := hP.height_pos
  have hm := hP.m_pos
  have hπ := Real.pi_pos
  -- the bound on `μ` in coordinates
  have hmp : MeasurePreserving (fun p : ℝ × ℝ => P.chart ⟨p.1, p.2⟩) volume volume := by
    have := P.measurePreserving_chart.comp (Complex.volume_preserving_equiv_real_prod.symm _)
    convert this using 1
    ext p
    simp only [Function.comp_apply]
    congr 1
  have h1 := hmp.quasiMeasurePreserving.ae hP.bound
  have h2 : ∀ᵐ p ∂(volume.restrict (Icc 0 P.width ×ˢ Icc 0 P.height)),
      μ (P.chart ⟨p.1, p.2⟩) ∈ Icc (m / 2) (3 * m / 2) :=
    (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2
      (h1.mono fun p hp hpI => hp (P.chart_mem_carrier_iff.2 ⟨hpI.1, hpI.2⟩))
  rw [T2.restrict_rect] at h2
  filter_upwards [Measure.ae_ae_of_ae_prod h2] with s hs
  unfold T2.lineAbs
  set u : ℝ → ℝ := fun ρ => radialU r (P.chart ⟨s, ρ⟩ - P.centre)
  have hu_meas : Measurable u :=
    (measurable_radialU r).comp ((P.continuous_chart.comp (T2.continuous_mk.comp
      (continuous_const.prodMk continuous_id))).sub continuous_const).measurable
  have hu_int : IntervalIntegrable u volume 0 P.height := by
    refine (intervalIntegrable_const (c := (π * r ^ 2)⁻¹)).mono_fun hu_meas.aestronglyMeasurable
      (Eventually.of_forall fun ρ => ?_)
    simp only [u, Real.norm_eq_abs]
    rw [abs_of_nonneg (radialU_nonneg _ _), abs_of_nonneg (show (0 : ℝ) ≤ (π * r ^ 2)⁻¹ by positivity)]
    exact radialU_le r _
  -- `∫₀^{b'} u_z ≤ 2/(π r₀)`
  have hu_le : ∫ ρ in (0 : ℝ)..P.height, u ρ ≤ 2 * r * (π * r ^ 2)⁻¹ := by
    have hpt : ∀ ρ, u ρ ≤
        (Icc (P.height / 2 - r) (P.height / 2 + r)).indicator (fun _ => (π * r ^ 2)⁻¹) ρ := by
      intro ρ
      by_cases hρ : ρ ∈ Icc (P.height / 2 - r) (P.height / 2 + r)
      · rw [indicator_of_mem hρ]; exact radialU_le r _
      · rw [indicator_of_notMem hρ]
        refine (radialU_of_notMem fun hb' => hρ ?_).le
        rw [mem_ball, dist_zero_right] at hb'
        have e : P.chart ⟨s, ρ⟩ - P.centre = P.frame (⟨s - P.width / 2, ρ - P.height / 2⟩) := by
          rw [Rect.centre, Rect.chart, Rect.chart, add_sub_add_left_eq_sub, ← map_sub]
          congr 1
        rw [e, LinearIsometryEquiv.norm_map] at hb'
        have := (Complex.abs_im_le_norm _).trans hb'.le
        rw [abs_le] at this
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hind : IntervalIntegrable
        ((Icc (P.height / 2 - r) (P.height / 2 + r)).indicator fun _ => (π * r ^ 2)⁻¹)
        volume 0 P.height := by
      refine (intervalIntegrable_const (c := (π * r ^ 2)⁻¹)).mono_fun
        ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)
        (Eventually.of_forall fun ρ => ?_)
      dsimp only
      by_cases hρ : ρ ∈ Icc (P.height / 2 - r) (P.height / 2 + r)
      · rw [indicator_of_mem hρ]
      · rw [indicator_of_notMem hρ, norm_zero]; exact norm_nonneg _
    calc ∫ ρ in (0 : ℝ)..P.height, u ρ
        ≤ ∫ ρ in (0 : ℝ)..P.height,
            (Icc (P.height / 2 - r) (P.height / 2 + r)).indicator (fun _ => (π * r ^ 2)⁻¹) ρ :=
          intervalIntegral.integral_mono_on hb.le hu_int hind fun ρ _ => hpt ρ
      _ = (π * r ^ 2)⁻¹ *
            volume.real (Icc (P.height / 2 - r) (P.height / 2 + r) ∩ Ioc 0 P.height) := by
          rw [intervalIntegral.integral_of_le hb.le, integral_indicator measurableSet_Icc,
            setIntegral_const, measureReal_restrict_apply measurableSet_Icc, smul_eq_mul, mul_comm]
      _ ≤ (π * r ^ 2)⁻¹ * volume.real (Icc (P.height / 2 - r) (P.height / 2 + r)) := by
          refine mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_left ?_) (by positivity)
          rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      _ = 2 * r * (π * r ^ 2)⁻¹ := by
          rw [Real.volume_real_Icc, max_eq_left (by linarith)]; ring
  by_cases hi : IntervalIntegrable (fun ρ => |P.src (P.pieceSrc r μ) (s, ρ)|) volume 0 P.height
  swap
  · rw [intervalIntegral.integral_undef hi]; positivity
  have hpt : ∀ᵐ ρ ∂(volume.restrict (Icc 0 P.height)),
      |P.src (P.pieceSrc r μ) (s, ρ)| ≤ 3 * π * m + 2 * π * u ρ := by
    filter_upwards [hs] with ρ hρ
    simp only [Rect.src, Rect.pieceSrc]
    have hu0 := radialU_nonneg r (P.chart ⟨s, ρ⟩ - P.centre)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have : |μ (P.chart ⟨s, ρ⟩) - radialU r (P.chart ⟨s, ρ⟩ - P.centre)| ≤
        3 * m / 2 + u ρ := by
      rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2]
    nlinarith
  calc ∫ ρ in (0 : ℝ)..P.height, |P.src (P.pieceSrc r μ) (s, ρ)|
      ≤ ∫ ρ in (0 : ℝ)..P.height, (3 * π * m + 2 * π * u ρ) :=
        intervalIntegral.integral_mono_ae_restrict hb.le hi
          (intervalIntegrable_const.add (hu_int.const_mul _)) hpt
    _ = 3 * π * m * P.height + 2 * π * ∫ ρ in (0 : ℝ)..P.height, u ρ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hu_int.const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
        ring
    _ ≤ 3 * π * m * P.height + 2 * π * (2 * r * (π * r ^ 2)⁻¹) := by gcongr
    _ = 3 * π * m * P.height + 4 / r := by field_simp; ring

/-- `∫₀^{a'} G = ∫_P |2π(μ - u_z)| ≤ 4π`. -/
theorem integral_lineAbs_le :
    ∫ s in (0 : ℝ)..P.width, T2.lineAbs P.height (P.src (P.pieceSrc r μ)) s ≤ 4 * π := by
  have hint := integrableOn_pieceSrc_of (r := r) hP.integrableOn
  have hu : IntegrableOn (fun x => radialU r (x - P.centre)) P.carrier :=
    ((integrable_radialU r).comp_sub_right _).integrableOn
  have e := T2.integral_line hP.width_pos.le hP.height_pos.le (P.integrableOn_src hint).abs
  have e2 : ∫ p in Icc 0 P.width ×ˢ Icc 0 P.height, |P.src (P.pieceSrc r μ) p| =
      ∫ x in P.carrier, |P.pieceSrc r μ x| := P.integral_src (fun x => |P.pieceSrc r μ x|)
  change ∫ s in (0 : ℝ)..P.width, T2.line P.height (fun p => |P.src (P.pieceSrc r μ) p|) s ≤ _
  rw [e, e2]
  have hπ := Real.pi_pos
  have hpt : ∀ᵐ x ∂(volume.restrict P.carrier),
      |P.pieceSrc r μ x| ≤ 2 * π * μ x + 2 * π * radialU r (x - P.centre) := by
    refine (ae_restrict_iff' P.measurableSet_carrier).2 (hP.bound.mono fun x hx hxP => ?_)
    have h1 := hx hxP
    have hu0 := radialU_nonneg r (x - P.centre)
    have hm := hP.m_pos
    simp only [Rect.pieceSrc]
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have : |μ x - radialU r (x - P.centre)| ≤ μ x + radialU r (x - P.centre) := by
      rw [abs_le]; constructor <;> linarith [h1.1]
    nlinarith
  calc ∫ x in P.carrier, |P.pieceSrc r μ x|
      ≤ ∫ x in P.carrier, (2 * π * μ x + 2 * π * radialU r (x - P.centre)) :=
        integral_mono_ae hint.abs ((hP.integrableOn.const_mul _).add (hu.const_mul _)) hpt
    _ = 4 * π := by
        rw [integral_add (hP.integrableOn.const_mul _) (hu.const_mul _), integral_const_mul,
          integral_const_mul, hP.mass, hP.setIntegral_radialU hr hr']
        ring

/-- **The T2 part**: `∫ |T2_P[2π(μ - u_z)]|² ≤ e_T(m) = 1056π² + 256π/(r₀√m)`. -/
theorem lintegral_norm_sq_t2_le :
    ∫⁻ x, ENNReal.ofReal (‖t2Field P (P.pieceSrc r μ) x‖ ^ 2) ≤
      ENNReal.ofReal (1056 * π ^ 2 + 256 * π / (r * √m)) := by
  have hint := integrableOn_pieceSrc_of (r := r) hP.integrableOn
  have ha := hP.width_pos
  have hb := hP.height_pos
  have hs := hP.sqrt_pos
  have hm := hP.m_pos
  have hπ := Real.pi_pos
  have hss : √m ^ 2 = m := Real.sq_sqrt hm.le
  set G := T2.lineAbs P.height (P.src (P.pieceSrc r μ))
  have hG0 : ∀ s, 0 ≤ G s := T2.lineAbs_nonneg hb.le _
  have hGint : IntegrableOn G (Icc 0 P.width) :=
    T2.integrableOn_lineAbs hb.le (P.integrableOn_src hint)
  have hIG := hP.integral_lineAbs_le hr hr'
  have hIG0 : 0 ≤ ∫ s in (0 : ℝ)..P.width, G s := intervalIntegral.integral_nonneg ha.le fun s _ => hG0 s
  set Gm := 3 * π * m * P.height + 4 / r
  have hGm0 : 0 ≤ Gm := by positivity
  -- the side ratio and the size of `b'`
  have hab : P.width / P.height ≤ 18 := by
    rw [div_le_iff₀ hb]
    have h1 := hP.width_mem.2
    have h2 := hP.height_mem.1
    rw [le_div_iff₀ hs] at h1
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  have hbs : P.height * √m ≤ 4 := by
    have := hP.height_mem.2; rwa [le_div_iff₀ hs] at this
  -- the first term
  have hT1 : P.width / P.height * (∫ s in (0 : ℝ)..P.width, G s) ^ 2 ≤ 288 * π ^ 2 := by
    have : (∫ s in (0 : ℝ)..P.width, G s) ^ 2 ≤ (4 * π) ^ 2 := pow_le_pow_left₀ hIG0 hIG 2
    calc _ ≤ 18 * (4 * π) ^ 2 := by gcongr
      _ = 288 * π ^ 2 := by ring
  -- the second term
  have hT2 : ∫⁻ s in Icc 0 P.width, ENNReal.ofReal (G s ^ 2) ≤ ENNReal.ofReal (Gm * (4 * π)) := by
    calc ∫⁻ s in Icc 0 P.width, ENNReal.ofReal (G s ^ 2)
        ≤ ∫⁻ s in Icc 0 P.width, ENNReal.ofReal Gm * ENNReal.ofReal (G s) := by
          refine lintegral_mono_ae ((hP.ae_lineAbs_le hr).mono fun s hs' => ?_)
          rw [← ENNReal.ofReal_mul hGm0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [sq]; exact mul_le_mul_of_nonneg_right hs' (hG0 s)
      _ = ENNReal.ofReal Gm * ENNReal.ofReal (∫ s in Icc 0 P.width, G s) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ofReal_integral_eq_lintegral_ofReal hGint (Eventually.of_forall hG0)]
      _ ≤ ENNReal.ofReal (Gm * (4 * π)) := by
          rw [← ENNReal.ofReal_mul hGm0]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hGm0)
          rw [← T2.intervalIntegral_eq_Icc ha.le]; exact hIG
  refine (lintegral_norm_sq_t2Field P ha.le hb hint).trans ?_
  calc ENNReal.ofReal (P.width / P.height * (∫ s in (0 : ℝ)..P.width, G s) ^ 2) +
        ENNReal.ofReal (4 * P.height) * ∫⁻ s in Icc 0 P.width, ENNReal.ofReal (G s ^ 2)
      ≤ ENNReal.ofReal (288 * π ^ 2) + ENNReal.ofReal (4 * P.height) *
          ENNReal.ofReal (Gm * (4 * π)) := by gcongr
    _ = ENNReal.ofReal (288 * π ^ 2 + 4 * P.height * (Gm * (4 * π))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (1056 * π ^ 2 + 256 * π / (r * √m)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : 4 * P.height * (Gm * (4 * π)) =
            48 * π ^ 2 * (P.height * √m) ^ 2 + 64 * π * (P.height * √m) / (r * √m) := by
          simp only [Gm]
          field_simp
          rw [hss]; ring
        rw [e]
        have h1 : 48 * π ^ 2 * (P.height * √m) ^ 2 ≤ 768 * π ^ 2 := by
          have : (P.height * √m) ^ 2 ≤ 16 := by
            have := pow_le_pow_left₀ (mul_pos hb hs).le hbs 2; linarith
          linarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 48 * π ^ 2)]
        have h2 : 64 * π * (P.height * √m) / (r * √m) ≤ 256 * π / (r * √m) := by
          rw [div_le_div_iff_of_pos_right (by positivity)]
          have := mul_le_mul_of_nonneg_left hbs (by positivity : (0 : ℝ) ≤ 64 * π)
          linarith
        linarith

/-- **The screening note's Lemma 4.22, the energy**: `∫ |Ψ_P - ∇f_{r₀}(· - z)|² ≤ 2(π/2 + e_T(m))`. -/
theorem lintegral_norm_sq_pieceField_sub_le :
    ∫⁻ x, ENNReal.ofReal (‖P.pieceField r μ x - gradient (truncLog r) (x - P.centre)‖ ^ 2) ≤
      ENNReal.ofReal (2 * (π / 2 + (1056 * π ^ 2 + 256 * π / (r * √m)))) := by
  have hint := integrableOn_pieceSrc_of (r := r) hP.integrableOn
  have hπ := Real.pi_pos
  have hs := hP.sqrt_pos
  have e : ∀ x, P.pieceField r μ x - gradient (truncLog r) (x - P.centre) =
      radialW r (x - P.centre) + t2Field P (P.pieceSrc r μ) x := by
    intro x
    rw [Rect.pieceField, ← radialK_sub_gradient]; abel
  have hW : ∫⁻ x, ENNReal.ofReal (‖radialW r (x - P.centre)‖ ^ 2) = ENNReal.ofReal (π / 2) := by
    rw [lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (‖radialW r y‖ ^ 2)),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_radialW hr)
        (Eventually.of_forall fun y => by positivity), integral_norm_sq_radialW hr]
  have hWm : Measurable fun x => ENNReal.ofReal (‖radialW r (x - P.centre)‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((measurable_radialW r).comp
      (measurable_id.sub_const _)).norm.pow_const 2)
  calc ∫⁻ x, ENNReal.ofReal (‖P.pieceField r μ x - gradient (truncLog r) (x - P.centre)‖ ^ 2)
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖radialW r (x - P.centre)‖ ^ 2) +
          2 * ENNReal.ofReal (‖t2Field P (P.pieceSrc r μ) x‖ ^ 2)) := by
        refine lintegral_mono fun x => ?_
        rw [e, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := norm_add_le (radialW r (x - P.centre)) (t2Field P (P.pieceSrc r μ) x)
        nlinarith [sq_nonneg (‖radialW r (x - P.centre)‖ - ‖t2Field P (P.pieceSrc r μ) x‖),
          norm_nonneg (radialW r (x - P.centre) + t2Field P (P.pieceSrc r μ) x)]
    _ = 2 * ENNReal.ofReal (π / 2) +
          2 * ∫⁻ x, ENNReal.ofReal (‖t2Field P (P.pieceSrc r μ) x‖ ^ 2) := by
        rw [lintegral_add_left (hWm.const_mul _), lintegral_const_mul _ hWm,
          lintegral_const_mul' _ _ (by simp), hW]
    _ ≤ 2 * ENNReal.ofReal (π / 2) +
          2 * ENNReal.ofReal (1056 * π ^ 2 + 256 * π / (r * √m)) := by
        gcongr; exact hP.lintegral_norm_sq_t2_le hr hr'
    _ = ENNReal.ofReal (2 * (π / 2 + (1056 * π ^ 2 + 256 * π / (r * √m)))) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end Rect.IsFillerPiece

/-- **The pieces of the filler partition are filler pieces** (Lemma 4.21 ⟹ hypotheses of 4.22). -/
theorem IsFillerPartition.isFillerPiece {P : Rect} {μ : ℂ → ℝ} {m : ℝ} {n : ℕ}
    {I : Finset (ℕ × ℕ)} {piece : ℕ × ℕ → Rect} (hF : IsFillerPartition P μ m n I piece)
    (hm : 0 < m) (hμm : AEStronglyMeasurable μ (volume.restrict P.carrier))
    (hμ : ∀ᵐ x, x ∈ P.carrier → μ x ∈ Icc (m / 2) (3 * m / 2)) {p : ℕ × ℕ} (hp : p ∈ I) :
    (piece p).IsFillerPiece m μ := by
  have hsub : (piece p).carrier ⊆ P.carrier := by
    obtain ⟨a, b, he, ha, haw, hb, hbh⟩ := hF.sub p hp
    rw [he, Rect.carrier_sub, Rect.carrier_eq_box]
    exact Rect.box_mono (Icc_subset_Icc ha haw) (Icc_subset_Icc hb hbh)
  exact ⟨hm, hF.width_mem p hp, hF.height_mem p hp, hμm.mono_set hsub,
    hμ.mono fun x hx hxp => hx (hsub hxp), hF.mass p hp⟩

end SandierSerfaty.Screening

end
