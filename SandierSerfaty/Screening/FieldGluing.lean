/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.RectangleSolver
public import SandierSerfaty.Screening.RadialFields

/-!
# Gluing explicit fields (screening note, §4.1, "gluing")

The screened field of the screening note Def. 4.24 is a finite sum of explicit pieces (the soft-cut field, the flux
cells and the carries, which are T2 fields on rectangles glued across shared sides, and the piece
fields `K^{r₀}(· - z) + T2`), and its Neumann identity (Lemma 4.25) is the sum of the pieces'
identities. This file packages that bookkeeping.

* `IsFieldPiece V Y ρ`: `V` and `ρ` are integrable and `-div V = 2π ∑_{y ∈ Y} δ_y - ρ` against smooth
  compactly supported test functions: `∫ ⟪V, ∇φ⟫ = 2π ∑_{y ∈ Y} φ(y) - ∫ ρ φ`;
* `isFieldPiece_t2Field`: T2 on a rectangle (any orthogonal frame), `Y = ∅`, `ρ = f 1_H`
  (screening note, Lemma 4.4(b));
* `isFieldPiece_radialK`: `K^r(· - q)`, `Y = {q}`, `ρ = 2π u^r(· - q)` (screening note, Lemma 4.5(b));
* `IsFieldPiece.add`, `isFieldPiece_finsetSum`: sums of pieces with pairwise disjoint charge sets;
* `IsFieldPiece.isNeumannChargeField`: a piece vanishing a.e. off a measurable set `Q` with
  `ρ = 2π m 1_Q` a.e. is a Neumann charge field on `Q` with density `m` and charges `Y`;
  `isNeumannChargeField_finsetSum` combines the two.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal ContDiff Real

public section

namespace SandierSerfaty.Screening

/-- `V` is an **explicit field piece** with point charges `Y` and absolutely continuous source `ρ`:
`V`, `ρ` integrable and `-div V = 2π ∑_{y ∈ Y} δ_y - ρ` against smooth compactly supported tests. -/
@[expose] def IsFieldPiece (V : ℂ → ℂ) (Y : Finset ℂ) (ρ : ℂ → ℝ) : Prop :=
  Integrable V ∧ Integrable ρ ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, inner ℝ (V x) (gradient φ x) = 2 * π * (∑ y ∈ Y, φ y) - ∫ x, ρ x * φ x

theorem exists_lipschitzWith_of_contDiff {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : ∃ K : ℝ≥0, LipschitzWith K φ :=
  ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)

theorem integrable_inner_gradient_of_contDiff {V : ℂ → ℂ} (hV : Integrable V) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable fun x => inner ℝ (V x) (gradient φ x) := by
  obtain ⟨B, hB⟩ := exists_norm_gradient_le (hφ.of_le (by simp)) hc
  exact integrable_inner_of_integrableOn MeasurableSet.univ hV.integrableOn
    (aestronglyMeasurable_gradient _) hB (fun x hx => absurd (mem_univ x) hx)

theorem integrable_mul_of_contDiff {ρ : ℂ → ℝ} (hρ : Integrable ρ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) : Integrable fun x => ρ x * φ x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  refine (hρ.norm.mul_const C).mono' (hρ.aestronglyMeasurable.mul
    hφ.continuous.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

/-- **T2 is a field piece** (screening note, Lemma 4.4(b)): `Y = ∅`, `ρ = f 1_H`. -/
theorem isFieldPiece_t2Field (H : Rect) (ha : 0 < H.width) (hb : 0 < H.height) {f : ℂ → ℝ}
    (hf : IntegrableOn f H.carrier) (h0 : ∫ x in H.carrier, f x = 0) :
    IsFieldPiece (t2Field H f) ∅ (H.carrier.indicator f) := by
  refine ⟨integrable_t2Field H ha.le hb hf,
    (integrable_indicator_iff H.measurableSet_carrier).2 hf, fun φ hφ hc => ?_⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiff hφ hc
  rw [integral_inner_t2Field H ha hb hf h0 hK, Finset.sum_empty, mul_zero, zero_sub]
  congr 1
  have : (fun x => H.carrier.indicator f x * φ x) = H.carrier.indicator fun x => f x * φ x := by
    ext x; by_cases hx : x ∈ H.carrier <;> simp [hx]
  rw [this, integral_indicator H.measurableSet_carrier]

/-- **`K^r(· - q)` is a field piece** (screening note, Lemma 4.5(b)): `Y = {q}`, `ρ = 2π u^r(· - q)`. -/
theorem isFieldPiece_radialK {r : ℝ} (hr : 0 < r) (q : ℂ) :
    IsFieldPiece (fun x => radialK r (x - q)) {q} (fun x => 2 * π * radialU r (x - q)) := by
  refine ⟨(integrable_radialK hr).comp_sub_right q,
    ((integrable_radialU r).comp_sub_right q).const_mul _, fun φ hφ hc => ?_⟩
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiff hφ hc
  rw [integral_inner_radialK hr q hK, Finset.sum_singleton]
  have : ∫ x, 2 * π * radialU r (x - q) * φ x = 2 * π * ∫ x, radialU r (x - q) * φ x := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [this]; ring

theorem IsFieldPiece.add {V₁ V₂ : ℂ → ℂ} {Y₁ Y₂ : Finset ℂ} {ρ₁ ρ₂ : ℂ → ℝ}
    (h₁ : IsFieldPiece V₁ Y₁ ρ₁) (h₂ : IsFieldPiece V₂ Y₂ ρ₂) (hY : Disjoint Y₁ Y₂) :
    IsFieldPiece (V₁ + V₂) (Y₁ ∪ Y₂) (ρ₁ + ρ₂) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun φ hφ hc => ?_⟩
  have e1 : (fun x => inner ℝ ((V₁ + V₂) x) (gradient φ x)) =
      fun x => inner ℝ (V₁ x) (gradient φ x) + inner ℝ (V₂ x) (gradient φ x) := by
    ext x; simp
  have e2 : (fun x => (ρ₁ + ρ₂) x * φ x) = fun x => ρ₁ x * φ x + ρ₂ x * φ x := by
    ext x; simp [add_mul]
  rw [e1, e2, integral_add (integrable_inner_gradient_of_contDiff h₁.1 hφ hc)
      (integrable_inner_gradient_of_contDiff h₂.1 hφ hc),
    integral_add (integrable_mul_of_contDiff h₁.2.1 hφ hc) (integrable_mul_of_contDiff h₂.2.1 hφ hc),
    h₁.2.2 φ hφ hc, h₂.2.2 φ hφ hc, Finset.sum_union hY]
  ring

theorem isFieldPiece_zero : IsFieldPiece 0 ∅ 0 :=
  ⟨integrable_zero _ _ _, integrable_zero _ _ _, fun φ _ _ => by simp⟩

/-- **Finite sums of field pieces** with pairwise disjoint charge sets. -/
theorem isFieldPiece_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι) {V : ι → ℂ → ℂ}
    {Y : ι → Finset ℂ} {ρ : ι → ℂ → ℝ} (h : ∀ i ∈ s, IsFieldPiece (V i) (Y i) (ρ i))
    (hY : (s : Set ι).PairwiseDisjoint Y) :
    IsFieldPiece (∑ i ∈ s, V i) (s.biUnion Y) (∑ i ∈ s, ρ i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isFieldPiece_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.biUnion_insert]
    refine (h j (Finset.mem_insert_self j s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
        (hY.subset (by simp [Set.subset_insert]))) ?_
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hY (by simp) (by simp [hi]) (fun hij => hj (hij ▸ hi))

/-- **Gluing**: a field piece vanishing a.e. off `Q` whose source is `2π m 1_Q` a.e. is a Neumann
charge field on `Q` with density `m` and charges `Y` (screening note, Lemma 4.25 pattern). -/
theorem IsFieldPiece.isNeumannChargeField {V : ℂ → ℂ} {Y : Finset ℂ} {ρ : ℂ → ℝ}
    (h : IsFieldPiece V Y ρ) {Q : Set ℂ} (hQ : MeasurableSet Q) {m : ℝ}
    (hVQ : ∀ᵐ x, x ∉ Q → V x = 0) (hρ : ρ =ᵐ[volume] Q.indicator fun _ => 2 * π * m) :
    IsNeumannChargeField Q m Y V := by
  refine ⟨h.1.integrableOn, fun φ hφ hc => ?_⟩
  have hQc : ∀ᵐ x, x ∈ Qᶜ → inner ℝ (V x) (gradient φ x) = 0 := by
    filter_upwards [hVQ] with x hx hxQ
    rw [hx hxQ, inner_zero_left]
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero hQc, h.2.2 φ hφ hc]
  have hρφ : (fun x => ρ x * φ x) =ᵐ[volume] Q.indicator fun x => 2 * π * m * φ x := by
    filter_upwards [hρ] with x hx
    rw [hx]
    by_cases hxQ : x ∈ Q <;> simp [hxQ]
  rw [integral_congr_ae hρφ, integral_indicator hQ, integral_const_mul]
  ring

/-- **Gluing a finite family of pieces** into a Neumann charge field on `Q`. -/
theorem isNeumannChargeField_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι) {V : ι → ℂ → ℂ}
    {Y : ι → Finset ℂ} {ρ : ι → ℂ → ℝ} (h : ∀ i ∈ s, IsFieldPiece (V i) (Y i) (ρ i))
    (hY : (s : Set ι).PairwiseDisjoint Y) {Q : Set ℂ} (hQ : MeasurableSet Q) {m : ℝ}
    (hVQ : ∀ i ∈ s, ∀ᵐ x, x ∉ Q → V i x = 0)
    (hρ : (∑ i ∈ s, ρ i) =ᵐ[volume] Q.indicator fun _ => 2 * π * m) :
    IsNeumannChargeField Q m (s.biUnion Y) (∑ i ∈ s, V i) := by
  refine (isFieldPiece_finsetSum s h hY).isNeumannChargeField hQ ?_ hρ
  have hall : ∀ᵐ x, ∀ i ∈ s, x ∉ Q → V i x = 0 := (ae_ball_iff s.countable_toSet).2 hVQ
  filter_upwards [hall] with x hx hxQ
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi => hx i hi hxQ

end SandierSerfaty.Screening

end
