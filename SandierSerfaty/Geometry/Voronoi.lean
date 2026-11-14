/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Euclidean.PerpBisector
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Voronoi cells in the plane: general facts

For a set `P ⊆ ℂ` of sites and `p : ℂ`, the Voronoi cell is
`voronoiCell P p = {x | ∀ q ∈ P, ‖x - p‖ ≤ ‖x - q‖}` (Euclidean norm of `ℂ`).

* `voronoiCell P p` is closed and convex, equals the intersection of the closed half-planes
  `bisectorHalfPlane p q` (`q ∈ P`), and contains `p` when `p ∈ P`;
* if the sites are locally finite (`LocallyFiniteSites`) and nonempty, every point lies in the cell
  of a nearest site (`exists_mem_voronoiCell`);
* the cells of two distinct sites meet in a subset of the perpendicular bisector, a Lebesgue null
  set (`volume_voronoiCell_inter_eq_zero`);
* a translation of the sites carries cells to cells (`mem_voronoiCell_add_iff`).

Source: paper §4, Lemma `geo:voronoi`; the periodic statements are in `SandierSerfaty.Geometry.VoronoiPeriodic`.
-/

open MeasureTheory Metric Set

public section

namespace SandierSerfaty

/-- The set `P ⊆ ℂ` is *locally finite*: every closed ball meets `P` in a finite set. -/
@[expose] def LocallyFiniteSites (P : Set ℂ) : Prop :=
  ∀ (x : ℂ) (r : ℝ), (P ∩ closedBall x r).Finite

/-- The closed half-plane of points at least as close to `p` as to `q`; its boundary is the
perpendicular bisector of `p` and `q` (when `p ≠ q`). -/
@[expose] def bisectorHalfPlane (p q : ℂ) : Set ℂ := {x | ‖x - p‖ ≤ ‖x - q‖}

/-- The **Voronoi cell** of `p` with respect to the sites `P`: the points at least as close to
`p` as to every site. -/
@[expose] def voronoiCell (P : Set ℂ) (p : ℂ) : Set ℂ := {x | ∀ q ∈ P, ‖x - p‖ ≤ ‖x - q‖}

variable {P : Set ℂ} {p q x : ℂ}

theorem mem_bisectorHalfPlane : x ∈ bisectorHalfPlane p q ↔ ‖x - p‖ ≤ ‖x - q‖ := Iff.rfl

theorem mem_voronoiCell : x ∈ voronoiCell P p ↔ ∀ q ∈ P, ‖x - p‖ ≤ ‖x - q‖ := Iff.rfl

/-- A Voronoi cell is the intersection of the half-planes bounded by the bisectors. -/
theorem voronoiCell_eq_biInter (P : Set ℂ) (p : ℂ) :
    voronoiCell P p = ⋂ q ∈ P, bisectorHalfPlane p q := by
  ext x
  simp [mem_voronoiCell, mem_bisectorHalfPlane]

theorem mem_bisectorHalfPlane_self (p q : ℂ) : p ∈ bisectorHalfPlane p q := by
  simp [mem_bisectorHalfPlane]

/-- A cell contains its own site (when the site belongs to the sites). -/
theorem mem_voronoiCell_self (P : Set ℂ) (p : ℂ) : p ∈ voronoiCell P p := by
  intro q _
  simp

/-- The half-plane `{‖x - p‖ ≤ ‖x - q‖}` in terms of the inner product. -/
theorem bisectorHalfPlane_eq_inner (p q : ℂ) :
    bisectorHalfPlane p q = {x | inner ℝ x (q - p) ≤ (‖q‖ ^ 2 - ‖p‖ ^ 2) / 2} := by
  ext x
  simp only [mem_bisectorHalfPlane, Set.mem_ofPred_eq]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, norm_sub_sq_real,
    inner_sub_right]
  constructor <;> intro h <;> linarith

theorem isClosed_bisectorHalfPlane (p q : ℂ) : IsClosed (bisectorHalfPlane p q) :=
  isClosed_le (by fun_prop) (by fun_prop)

theorem convex_bisectorHalfPlane (p q : ℂ) : Convex ℝ (bisectorHalfPlane p q) := by
  rw [bisectorHalfPlane_eq_inner]
  exact convex_halfSpace_le
    ⟨fun _ _ => inner_add_left _ _ _, fun c x => real_inner_smul_left _ _ _⟩ _

theorem isClosed_voronoiCell (P : Set ℂ) (p : ℂ) : IsClosed (voronoiCell P p) := by
  rw [voronoiCell_eq_biInter]
  exact isClosed_biInter fun q _ => isClosed_bisectorHalfPlane p q

theorem convex_voronoiCell (P : Set ℂ) (p : ℂ) : Convex ℝ (voronoiCell P p) := by
  rw [voronoiCell_eq_biInter]
  exact convex_iInter fun q => convex_iInter fun _ => convex_bisectorHalfPlane p q

theorem measurableSet_voronoiCell (P : Set ℂ) (p : ℂ) : MeasurableSet (voronoiCell P p) :=
  (isClosed_voronoiCell P p).measurableSet

/-- **Existence of a nearest site.** If `P` is nonempty and locally finite, every `x` lies in the
cell of some site. -/
theorem exists_mem_voronoiCell (hne : P.Nonempty) (hfin : LocallyFiniteSites P) (x : ℂ) :
    ∃ p ∈ P, x ∈ voronoiCell P p := by
  obtain ⟨q₀, hq₀⟩ := hne
  set S : Set ℂ := {q | q ∈ P ∧ ‖x - q‖ ≤ ‖x - q₀‖} with hS
  have hSfin : S.Finite := (hfin x ‖x - q₀‖).subset fun q hq => by
    refine ⟨hq.1, ?_⟩
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hq.2
  obtain ⟨a, haS, ha⟩ := Set.exists_min_image S (fun q => ‖x - q‖) hSfin ⟨q₀, hq₀, le_rfl⟩
  refine ⟨a, haS.1, fun q hq => ?_⟩
  have h1 : ‖x - a‖ ≤ ‖x - q‖ := by
    by_cases hqS : ‖x - q‖ ≤ ‖x - q₀‖
    · exact ha q ⟨hq, hqS⟩
    · exact le_trans haS.2 (not_le.1 hqS).le
  rw [norm_sub_rev x a, norm_sub_rev x q] at h1
  rwa [norm_sub_rev, norm_sub_rev x q]

/-- Two cells of distinct sites meet only on the perpendicular bisector. -/
theorem voronoiCell_inter_subset_perpBisector (hp : p ∈ P) (hq : q ∈ P) :
    voronoiCell P p ∩ voronoiCell P q ⊆ (AffineSubspace.perpBisector p q : Set ℂ) := by
  rintro x ⟨hxp, hxq⟩
  have h1 := hxp q hq
  have h2 := hxq p hp
  rw [SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq, dist_eq_norm, dist_eq_norm]
  exact le_antisymm h1 h2

/-- The perpendicular bisector of two distinct points of the plane is Lebesgue-null. -/
theorem volume_perpBisector_eq_zero (hpq : p ≠ q) :
    volume (AffineSubspace.perpBisector p q : Set ℂ) = 0 :=
  Measure.addHaar_affineSubspace volume _ (by simpa using hpq)

/-- **Distinct cells meet in a null set.** -/
theorem volume_voronoiCell_inter_eq_zero (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    volume (voronoiCell P p ∩ voronoiCell P q) = 0 :=
  measure_mono_null (voronoiCell_inter_subset_perpBisector hp hq) (volume_perpBisector_eq_zero hpq)

/-- The cells of distinct sites are almost everywhere disjoint. -/
theorem aedisjoint_voronoiCell (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    AEDisjoint volume (voronoiCell P p) (voronoiCell P q) :=
  volume_voronoiCell_inter_eq_zero hp hq hpq

/-- **Translation.** If `P + v = P`, the cell of `p + v` is the translate of the cell of `p`. -/
theorem mem_voronoiCell_add_iff {v : ℂ} (hP : ∀ q, q + v ∈ P ↔ q ∈ P) :
    x ∈ voronoiCell P (p + v) ↔ x - v ∈ voronoiCell P p := by
  simp only [mem_voronoiCell]
  constructor
  · intro h q hq
    have := h (q + v) ((hP q).2 hq)
    convert this using 2 <;> abel_nf
  · intro h q hq
    have hq' : q - v ∈ P := by
      rw [← hP]; simpa using hq
    have := h (q - v) hq'
    convert this using 2 <;> abel_nf

end SandierSerfaty

end
