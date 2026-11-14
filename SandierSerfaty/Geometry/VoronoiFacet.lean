/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiLocal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Facets of Voronoi cells and their frames

For two sites `p ≠ q` we use the frame of the pair: the unit axis `pairAxis p q` toward `q`, the half
distance `d = pairHalfDist p q`, and the points `bisectorPoint p q s = p + u (d + s i)` of the
perpendicular bisector (ordinate `s`). The *facet* of `p` toward `q` is `C_p ∩ C_q`, recorded by its
set of ordinates `facetOrdinates P p q = {s | bisectorPoint p q s ∈ C_p}`; `q` is a *Voronoi
neighbour* of `p` when that set is nontrivial (the facet has positive length). Its endpoints
`facetEnd P p q true` (ordinate `facetHi`, counterclockwise) and `facetEnd P p q false` (ordinate
`facetLo`) define the sector angles `sectorBeta = arctan (facetHi / d)` and
`sectorAlpha = arctan (-facetLo / d)` of the paper's sector `S(d, α, β)`.

* frame algebra (`norm_pairAxis`, `eq_bisectorPoint_of_norm_eq`, `norm_bisectorPoint_sub`, ...);
* the ordinates form a closed bounded interval `[facetLo, facetHi]` (`Icc_subset_facetOrdinates`,
  `facetOrdinates_subset_Icc`) when the cell is bounded;
* `abs_sectorAlpha_lt`, `abs_sectorBeta_lt`, `sectorAlpha_add_sectorBeta_pos`;
* invariance under a symmetry `P + γ = P` (`facetEnd_add_add`, ...).

Source: paper §4 (`geo:voronoi`).
-/

open Metric Set Real

public section

namespace SandierSerfaty

/-! ### Definitions -/

/-- Unit axis of the pair `(p, q)`, pointing toward `q`. -/
@[expose] noncomputable def pairAxis (p q : ℂ) : ℂ := (q - p) / (‖q - p‖ : ℂ)

/-- Half the distance between `p` and `q`: the distance from `p` to the bisector. -/
@[expose] noncomputable def pairHalfDist (p q : ℂ) : ℝ := ‖q - p‖ / 2

/-- The point of ordinate `s` of the bisector of `p` and `q`. -/
@[expose] noncomputable def bisectorPoint (p q : ℂ) (s : ℝ) : ℂ :=
  p + pairAxis p q * ((pairHalfDist p q : ℂ) + (s : ℂ) * Complex.I)

/-- Ordinates of the facet `C_p ∩ C_q` along the bisector (a compact interval). -/
@[expose] def facetOrdinates (P : Set ℂ) (p q : ℂ) : Set ℝ :=
  {s | bisectorPoint p q s ∈ voronoiCell P p}

/-- `q` is a Voronoi neighbour of `p`: the common facet has positive length. -/
@[expose] def IsVoronoiNeighbor (P : Set ℂ) (p q : ℂ) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p ≠ q ∧ (facetOrdinates P p q).Nontrivial

/-- Lower ordinate of the facet. -/
@[expose] noncomputable def facetLo (P : Set ℂ) (p q : ℂ) : ℝ := sInf (facetOrdinates P p q)

/-- Upper ordinate of the facet. -/
@[expose] noncomputable def facetHi (P : Set ℂ) (p q : ℂ) : ℝ := sSup (facetOrdinates P p q)

/-- Facet endpoints: `true` is the `β` end (counterclockwise), `false` the `α` end. -/
@[expose] noncomputable def facetEnd (P : Set ℂ) (p q : ℂ) : Bool → ℂ
  | true => bisectorPoint p q (facetHi P p q)
  | false => bisectorPoint p q (facetLo P p q)

/-- The angle `α` of the sector of `(p, q)` (clockwise from the axis). -/
@[expose] noncomputable def sectorAlpha (P : Set ℂ) (p q : ℂ) : ℝ :=
  Real.arctan (-facetLo P p q / pairHalfDist p q)

/-- The angle `β` of the sector of `(p, q)` (counterclockwise from the axis). -/
@[expose] noncomputable def sectorBeta (P : Set ℂ) (p q : ℂ) : ℝ :=
  Real.arctan (facetHi P p q / pairHalfDist p q)

/-- The base angles of the triangle `(p, v₋, v₊)` at its facet endpoints. -/
@[expose] noncomputable def sectorBaseAngle (P : Set ℂ) (p q : ℂ) : Bool → ℝ
  | true => π / 2 - sectorBeta P p q
  | false => π / 2 - sectorAlpha P p q

/-! ### Norm comparisons in coordinates -/

theorem norm_le_norm_iff_re_im (a b : ℂ) :
    ‖a‖ ≤ ‖b‖ ↔ a.re * a.re + a.im * a.im ≤ b.re * b.re + b.im * b.im := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]

theorem norm_lt_norm_iff_re_im (a b : ℂ) :
    ‖a‖ < ‖b‖ ↔ a.re * a.re + a.im * a.im < b.re * b.re + b.im * b.im := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]

theorem norm_eq_norm_iff_re_im (a b : ℂ) :
    ‖a‖ = ‖b‖ ↔ a.re * a.re + a.im * a.im = b.re * b.re + b.im * b.im := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]

/-! ### Frame algebra -/

section Frame

variable {p q : ℂ}

theorem pairHalfDist_pos (h : p ≠ q) : 0 < pairHalfDist p q := by
  have := norm_pos_iff.2 (sub_ne_zero.2 h.symm)
  unfold pairHalfDist; positivity

theorem norm_pairAxis (h : p ≠ q) : ‖pairAxis p q‖ = 1 := by
  have := norm_pos_iff.2 (sub_ne_zero.2 h.symm)
  rw [pairAxis, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self this.ne']

theorem pairAxis_ne_zero (h : p ≠ q) : pairAxis p q ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_pairAxis h]; exact one_ne_zero

/-- `q = p + u · 2d`. -/
theorem add_pairAxis_mul (h : p ≠ q) :
    p + pairAxis p q * ((2 * pairHalfDist p q : ℝ) : ℂ) = q := by
  have h0 : (‖q - p‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, norm_ne_zero_iff]; exact sub_ne_zero.2 h.symm
  rw [pairAxis, pairHalfDist]
  push_cast
  field_simp
  ring

/-- Unit complex numbers act isometrically. -/
theorem norm_add_mul_sub_add_mul {u : ℂ} (hu : ‖u‖ = 1) (c W E : ℂ) :
    ‖(c + u * W) - (c + u * E)‖ = ‖W - E‖ := by
  rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, hu, one_mul]

theorem eq_add_mul_conj_mul {u : ℂ} (hu : ‖u‖ = 1) (c z : ℂ) :
    z = c + u * ((starRingEnd ℂ) u * (z - c)) := by
  have : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
  rw [← mul_assoc, this, one_mul]; ring

theorem bisectorPoint_add (p q : ℂ) (s τ : ℝ) :
    bisectorPoint p q (s + τ) = bisectorPoint p q s + τ * (Complex.I * pairAxis p q) := by
  simp only [bisectorPoint]; push_cast; ring

theorem norm_bisectorPoint_sub (h : p ≠ q) (s s' : ℝ) :
    ‖bisectorPoint p q s - bisectorPoint p q s'‖ = |s - s'| := by
  have : bisectorPoint p q s = bisectorPoint p q s' + (s - s' : ℝ) * (Complex.I * pairAxis p q) := by
    rw [← bisectorPoint_add]; ring_nf
  rw [this, add_sub_cancel_left, norm_mul, norm_mul, norm_pairAxis h, Complex.norm_real,
    Complex.norm_I, Real.norm_eq_abs]
  ring

theorem bisectorPoint_injective (h : p ≠ q) : Function.Injective (bisectorPoint p q) := by
  intro s s' hs
  have := norm_bisectorPoint_sub h s s'
  rw [hs, sub_self, norm_zero] at this
  linarith [abs_eq_zero.1 this.symm]

/-- The frame coordinates of the sites: `p ↦ 0`, `q ↦ 2d`. -/
theorem norm_sub_eq_norm_frame (h : p ≠ q) (z : ℂ) :
    ‖z - p‖ = ‖(starRingEnd ℂ) (pairAxis p q) * (z - p)‖ ∧
      ‖z - q‖ = ‖(starRingEnd ℂ) (pairAxis p q) * (z - p) - ((2 * pairHalfDist p q : ℝ) : ℂ)‖ := by
  have hu := norm_pairAxis h
  constructor
  · rw [norm_mul, Complex.norm_conj, hu, one_mul]
  · have e1 := eq_add_mul_conj_mul hu p z
    have e2 := add_pairAxis_mul h
    calc ‖z - q‖ = ‖(p + pairAxis p q * ((starRingEnd ℂ) (pairAxis p q) * (z - p))) -
          (p + pairAxis p q * ((2 * pairHalfDist p q : ℝ) : ℂ))‖ := by rw [← e1, e2]
      _ = _ := norm_add_mul_sub_add_mul hu p _ _

/-- Points of the bisector are equidistant from `p` and `q`. -/
theorem norm_bisectorPoint_sub_eq (h : p ≠ q) (s : ℝ) :
    ‖bisectorPoint p q s - p‖ = ‖bisectorPoint p q s - q‖ := by
  have hu := norm_pairAxis h
  have e2 := add_pairAxis_mul h
  set u := pairAxis p q
  set d := pairHalfDist p q
  calc ‖bisectorPoint p q s - p‖ = ‖(p + u * ((d : ℂ) + (s : ℂ) * Complex.I)) - (p + u * 0)‖ := by
        rw [mul_zero, add_zero]; rfl
    _ = ‖((d : ℂ) + (s : ℂ) * Complex.I) - 0‖ := norm_add_mul_sub_add_mul hu _ _ _
    _ = ‖((d : ℂ) + (s : ℂ) * Complex.I) - ((2 * d : ℝ) : ℂ)‖ := by
        rw [norm_eq_norm_iff_re_im]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.mul_im, Complex.I_im, Complex.add_im, Complex.ofReal_im, Complex.sub_re,
          Complex.sub_im, Complex.zero_re, Complex.zero_im]
        ring
    _ = ‖(p + u * ((d : ℂ) + (s : ℂ) * Complex.I)) - (p + u * ((2 * d : ℝ) : ℂ))‖ :=
        (norm_add_mul_sub_add_mul hu _ _ _).symm
    _ = ‖bisectorPoint p q s - q‖ := by rw [e2]; rfl

/-- A point equidistant from `p` and `q` is the bisector point of ordinate `cross u (x - p)`. -/
theorem eq_bisectorPoint_of_norm_eq (h : p ≠ q) {x : ℂ} (hx : ‖x - p‖ = ‖x - q‖) :
    x = bisectorPoint p q (cross (pairAxis p q) (x - p)) := by
  have hu := norm_pairAxis h
  have hd := pairHalfDist_pos h
  obtain ⟨h1, h2⟩ := norm_sub_eq_norm_frame h x
  set W := (starRingEnd ℂ) (pairAxis p q) * (x - p) with hW
  rw [h1, h2, norm_eq_norm_iff_re_im] at hx
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hx
  have hre : W.re = pairHalfDist p q := by
    have : 4 * pairHalfDist p q * (W.re - pairHalfDist p q) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  have him : W.im = cross (pairAxis p q) (x - p) := by
    simp only [hW, Complex.mul_im, Complex.conj_re, Complex.conj_im, cross]; ring
  conv_lhs => rw [eq_add_mul_conj_mul hu p x]
  rw [bisectorPoint, ← hW]
  congr 1
  apply Complex.ext <;> simp [hre, him]

end Frame

/-! ### Facet ordinates -/

section Ordinates

variable {P : Set ℂ} {p q : ℂ}

theorem isClosed_facetOrdinates (P : Set ℂ) (p q : ℂ) : IsClosed (facetOrdinates P p q) :=
  (isClosed_voronoiCell P p).preimage (by unfold bisectorPoint; fun_prop)

theorem convex_facetOrdinates (P : Set ℂ) (p q : ℂ) : Convex ℝ (facetOrdinates P p q) := by
  intro s hs s' hs' a b ha hb hab
  have hc := convex_voronoiCell P p hs hs' ha hb hab
  have : bisectorPoint p q (a • s + b • s') =
      a • bisectorPoint p q s + b • bisectorPoint p q s' := by
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    simp only [bisectorPoint, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (p + pairAxis p q * (pairHalfDist p q : ℂ)) * hab'.symm
  show bisectorPoint p q (a • s + b • s') ∈ voronoiCell P p
  rw [this]; exact hc

theorem ordConnected_facetOrdinates (P : Set ℂ) (p q : ℂ) : (facetOrdinates P p q).OrdConnected :=
  (convex_facetOrdinates P p q).ordConnected

theorem isBounded_facetOrdinates (hpq : p ≠ q) (hb : Bornology.IsBounded (voronoiCell P p)) :
    Bornology.IsBounded (facetOrdinates P p q) := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  refine (isBounded_iff_subset_closedBall (0 : ℝ)).2 ⟨R + ‖bisectorPoint p q 0‖, fun s hs => ?_⟩
  have h1 := hR hs
  rw [mem_closedBall, dist_zero_right] at h1
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  have h2 := norm_bisectorPoint_sub hpq s 0
  rw [sub_zero] at h2
  have := norm_sub_le (bisectorPoint p q s) (bisectorPoint p q 0)
  linarith

end Ordinates

/-! ### Neighbours -/

section Neighbor

variable {P : Set ℂ} {p q : ℂ}

theorem IsVoronoiNeighbor.ne (h : IsVoronoiNeighbor P p q) : p ≠ q := h.2.2.1

theorem IsVoronoiNeighbor.isBounded (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    Bornology.IsBounded (facetOrdinates P p q) :=
  isBounded_facetOrdinates h.ne (hP.isBounded_cell p h.1)

theorem facetLo_mem (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    facetLo P p q ∈ facetOrdinates P p q :=
  (isClosed_facetOrdinates P p q).csInf_mem h.2.2.2.nonempty (h.isBounded hP).bddBelow

theorem facetHi_mem (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    facetHi P p q ∈ facetOrdinates P p q :=
  (isClosed_facetOrdinates P p q).csSup_mem h.2.2.2.nonempty (h.isBounded hP).bddAbove

theorem facetOrdinates_subset_Icc (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    facetOrdinates P p q ⊆ Icc (facetLo P p q) (facetHi P p q) := fun _ hs =>
  ⟨csInf_le (h.isBounded hP).bddBelow hs, le_csSup (h.isBounded hP).bddAbove hs⟩

theorem Icc_subset_facetOrdinates (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    Icc (facetLo P p q) (facetHi P p q) ⊆ facetOrdinates P p q :=
  (ordConnected_facetOrdinates P p q).out (facetLo_mem hP h) (facetHi_mem hP h)

theorem facetLo_lt_facetHi (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    facetLo P p q < facetHi P p q := by
  obtain ⟨s, hs, s', hs', hne⟩ := h.2.2.2
  have h1 := facetOrdinates_subset_Icc hP h hs
  have h2 := facetOrdinates_subset_Icc hP h hs'
  rcases lt_or_gt_of_ne hne with h3 | h3
  · exact lt_of_le_of_lt h1.1 (lt_of_lt_of_le h3 h2.2)
  · exact lt_of_le_of_lt h2.1 (lt_of_lt_of_le h3 h1.2)

theorem facetEnd_mem_voronoiCell (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q)
    (b : Bool) : facetEnd P p q b ∈ voronoiCell P p := by
  cases b
  · exact facetLo_mem hP h
  · exact facetHi_mem hP h

theorem norm_facetEnd_sub_eq (h : IsVoronoiNeighbor P p q) (b : Bool) :
    ‖facetEnd P p q b - p‖ = ‖facetEnd P p q b - q‖ := by
  cases b <;> exact norm_bisectorPoint_sub_eq h.ne _

/-- The two ends of a facet are distinct. -/
theorem facetEnd_true_ne_false (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    facetEnd P p q true ≠ facetEnd P p q false := fun he =>
  (facetLo_lt_facetHi hP h).ne' (bisectorPoint_injective h.ne he)

theorem tan_sectorAlpha (P : Set ℂ) (p q : ℂ) :
    Real.tan (sectorAlpha P p q) = -facetLo P p q / pairHalfDist p q :=
  Real.tan_arctan _

theorem tan_sectorBeta (P : Set ℂ) (p q : ℂ) :
    Real.tan (sectorBeta P p q) = facetHi P p q / pairHalfDist p q :=
  Real.tan_arctan _

theorem abs_sectorAlpha_lt (P : Set ℂ) (p q : ℂ) : |sectorAlpha P p q| < π / 2 :=
  abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

theorem abs_sectorBeta_lt (P : Set ℂ) (p q : ℂ) : |sectorBeta P p q| < π / 2 :=
  abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

theorem sectorAlpha_add_sectorBeta_pos (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    0 < sectorAlpha P p q + sectorBeta P p q := by
  have hd := pairHalfDist_pos h.ne
  have hlt := facetLo_lt_facetHi hP h
  have : facetLo P p q / pairHalfDist p q < facetHi P p q / pairHalfDist p q :=
    div_lt_div_of_pos_right hlt hd
  have h2 := Real.arctan_strictMono this
  rw [sectorAlpha, sectorBeta, neg_div, Real.arctan_neg]
  linarith

/-- The angle sum of the sector triangle. -/
theorem sectorAngle_add_sectorBaseAngle (P : Set ℂ) (p q : ℂ) :
    sectorAlpha P p q + sectorBeta P p q + sectorBaseAngle P p q true +
      sectorBaseAngle P p q false = π := by
  simp only [sectorBaseAngle]; ring

end Neighbor

/-! ### Translations -/

section Translate

variable {P : Set ℂ} {γ : ℂ} (hP : ∀ q, q + γ ∈ P ↔ q ∈ P) (p q : ℂ)

theorem pairAxis_add_add : pairAxis (p + γ) (q + γ) = pairAxis p q := by
  simp [pairAxis]

theorem pairHalfDist_add_add : pairHalfDist (p + γ) (q + γ) = pairHalfDist p q := by
  simp [pairHalfDist]

theorem bisectorPoint_add_add (s : ℝ) :
    bisectorPoint (p + γ) (q + γ) s = bisectorPoint p q s + γ := by
  rw [bisectorPoint, bisectorPoint, pairAxis_add_add, pairHalfDist_add_add]; ring

include hP in
theorem facetOrdinates_add_add : facetOrdinates P (p + γ) (q + γ) = facetOrdinates P p q := by
  ext s
  simp only [facetOrdinates, mem_ofPred_eq, bisectorPoint_add_add, mem_voronoiCell_add_iff hP,
    add_sub_cancel_right]

include hP in
theorem isVoronoiNeighbor_add_add_iff :
    IsVoronoiNeighbor P (p + γ) (q + γ) ↔ IsVoronoiNeighbor P p q := by
  simp only [IsVoronoiNeighbor, facetOrdinates_add_add hP, hP, ne_eq, add_left_inj]

include hP in
theorem facetLo_add_add : facetLo P (p + γ) (q + γ) = facetLo P p q := by
  rw [facetLo, facetLo, facetOrdinates_add_add hP]

include hP in
theorem facetHi_add_add : facetHi P (p + γ) (q + γ) = facetHi P p q := by
  rw [facetHi, facetHi, facetOrdinates_add_add hP]

include hP in
theorem facetEnd_add_add (b : Bool) : facetEnd P (p + γ) (q + γ) b = facetEnd P p q b + γ := by
  cases b
  · simp only [facetEnd, facetLo_add_add hP, bisectorPoint_add_add]
  · simp only [facetEnd, facetHi_add_add hP, bisectorPoint_add_add]

include hP in
theorem sectorAlpha_add_add : sectorAlpha P (p + γ) (q + γ) = sectorAlpha P p q := by
  rw [sectorAlpha, sectorAlpha, facetLo_add_add hP, pairHalfDist_add_add]

include hP in
theorem sectorBeta_add_add : sectorBeta P (p + γ) (q + γ) = sectorBeta P p q := by
  rw [sectorBeta, sectorBeta, facetHi_add_add hP, pairHalfDist_add_add]

include hP in
theorem sectorBaseAngle_add_add (b : Bool) :
    sectorBaseAngle P (p + γ) (q + γ) b = sectorBaseAngle P p q b := by
  cases b
  · simp only [sectorBaseAngle, sectorAlpha_add_add hP]
  · simp only [sectorBaseAngle, sectorBeta_add_add hP]

end Translate

/-! ### The partner incidence `(q, p)` -/

section Swap

variable {P : Set ℂ} {p q : ℂ}

/-- On the bisector, the cells of `p` and of `q` agree. -/
theorem mem_voronoiCell_iff_of_norm_eq {x : ℂ} (hx : ‖x - p‖ = ‖x - q‖) :
    x ∈ voronoiCell P q ↔ x ∈ voronoiCell P p := by
  simp only [mem_voronoiCell, hx]

end Swap

end SandierSerfaty

end
