/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiSector

/-!
# Angle packing at sites and at vertices; six sector ends at every vertex

The local inequalities behind the incidence count `M₀ ≤ 6n` (sector fan and
packing; no Euler characteristic):

* `sum_sectorAngle_le` (**site packing**, (S)): the sectors of one site are pairwise disjoint and
  each contains a polar sector of angle `α + β` about the site, so `∑_q (α + β) ≤ 2π`;
* `sum_sectorBaseAngle_le` (**vertex packing**, (V-a)): the sectors with an end at a point `x` are
  pairwise disjoint and each contains a cone of angle `sectorBaseAngle` at `x`, so the base angles
  at `x` add up to at most `2π`;
* `exists_six_endpoints` (**six ends**, (V-b)): if a facet ends at `x`, then `x` has at least three
  nearest sites, and each nearest site `r` has two facets ending at `x` (toward its two extremal
  neighbours on the circle of nearest sites), so at least six sector ends sit at `x`.

Source: paper §4, proof of Lemma `geo:voronoi` ("each vertex has
degree at least three").
-/

open Metric Set Real

public section

namespace SandierSerfaty

variable {P : Set ℂ}

/-! ### Packing -/

/-- **Site packing.** The sector angles of finitely many neighbours of a site add up to at most
`2π`. -/
theorem sum_sectorAngle_le (hP : IsVoronoiSiteSet P) (p : ℂ) (Q : Finset ℂ)
    (hQ : ∀ q ∈ Q, IsVoronoiNeighbor P p q) :
    ∑ q ∈ Q, (sectorAlpha P p q + sectorBeta P p q) ≤ 2 * π := by
  rcases Q.eq_empty_or_nonempty with hQe | hne
  · rw [hQe, Finset.sum_empty]; positivity
  set ε := Q.inf' hne (fun q => pairHalfDist p q) with hε
  have hε0 : 0 < ε := (Finset.lt_inf'_iff hne).2 fun q hq => pairHalfDist_pos (hQ q hq).ne
  have hεq : ∀ q ∈ Q, ε ≤ pairHalfDist p q := fun q hq => Finset.inf'_le _ hq
  have key := sum_angle_le_two_pi Q p (fun q => pairAxis p q) (fun q => -sectorAlpha P p q)
    (fun q => sectorBeta P p q) hε0 (fun q hq => norm_pairAxis (hQ q hq).ne)
    (fun q _ => by have := abs_lt.1 (abs_sectorAlpha_lt P p q); linarith)
    (fun q _ => by have := abs_lt.1 (abs_sectorBeta_lt P p q); linarith)
    (fun q hq => by have := sectorAlpha_add_sectorBeta_pos hP (hQ q hq); linarith)
    (fun q hq q' hq' hqq' =>
      (disjoint_voronoiSector hP (hQ q hq) (hQ q' hq') (by simpa using hqq')).mono
        (image_polarSector_subset_voronoiSector (hεq q hq))
        (image_polarSector_subset_voronoiSector (hεq q' hq')))
  simpa [sub_neg_eq_add, add_comm] using key

/-- **Vertex packing.** The base angles of finitely many sector ends at a point `x` add up to at
most `2π`. -/
theorem sum_sectorBaseAngle_le (hP : IsVoronoiSiteSet P) (x : ℂ) (S : Finset (ℂ × ℂ × Bool))
    (hS : ∀ e ∈ S, IsVoronoiNeighbor P e.1 e.2.1 ∧ facetEnd P e.1 e.2.1 e.2.2 = x) :
    ∑ e ∈ S, sectorBaseAngle P e.1 e.2.1 e.2.2 ≤ 2 * π := by
  rcases S.eq_empty_or_nonempty with hSe | hne
  · rw [hSe, Finset.sum_empty]; positivity
  have hcone : ∀ e : ℂ × ℂ × Bool, ∃ ε > 0, e ∈ S → ∀ ε' ≤ ε,
      (fun z => facetEnd P e.1 e.2.1 e.2.2 + (-pairAxis e.1 e.2.1) * z) ''
        polarSector (endConeLo P e.1 e.2.1 e.2.2) (endConeHi P e.1 e.2.1 e.2.2) ε' ⊆
          voronoiSector P e.1 e.2.1 := by
    intro e
    by_cases he : e ∈ S
    · obtain ⟨ε, hε0, hε⟩ := exists_endCone_subset_voronoiSector hP (hS e he).1 e.2.2
      exact ⟨ε, hε0, fun _ => hε⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose ε hε0 hε using hcone
  set ε₀ := S.inf' hne ε with hε₀
  have hε₀0 : 0 < ε₀ := (Finset.lt_inf'_iff hne).2 fun e _ => hε0 e
  have hsub : ∀ e ∈ S, (fun z => x + (-pairAxis e.1 e.2.1) * z) ''
      polarSector (endConeLo P e.1 e.2.1 e.2.2) (endConeHi P e.1 e.2.1 e.2.2) ε₀ ⊆
        voronoiSector P e.1 e.2.1 := by
    intro e he
    have := hε e he ε₀ (Finset.inf'_le _ he)
    rwa [(hS e he).2] at this
  have hpair : ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → (e.1, e.2.1) ≠ (e'.1, e'.2.1) := by
    rintro ⟨p, q, b⟩ he ⟨p', q', b'⟩ he' hee' hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    have hb : b ≠ b' := fun hb => hee' (by rw [hb])
    have h1 := (hS _ he).2
    have h2 := (hS _ he').2
    simp only at h1 h2
    have hn := (hS _ he).1
    simp only at hn
    cases b <;> cases b'
    · exact hb rfl
    · exact facetEnd_true_ne_false hP hn (h2.trans h1.symm)
    · exact facetEnd_true_ne_false hP hn (h1.trans h2.symm)
    · exact hb rfl
  have key := sum_angle_le_two_pi S x (fun e => -pairAxis e.1 e.2.1)
    (fun e => endConeLo P e.1 e.2.1 e.2.2) (fun e => endConeHi P e.1 e.2.1 e.2.2) hε₀0
    (fun e he => by rw [norm_neg]; exact norm_pairAxis (hS e he).1.ne)
    (fun e _ => by
      have := abs_lt.1 (abs_sectorBeta_lt P e.1 e.2.1)
      cases e.2.2 <;> simp only [endConeLo] <;> linarith [Real.pi_pos])
    (fun e _ => by
      have := abs_lt.1 (abs_sectorAlpha_lt P e.1 e.2.1)
      cases e.2.2 <;> simp only [endConeHi] <;> linarith [Real.pi_pos])
    (fun e _ => by
      have := abs_lt.1 (abs_sectorAlpha_lt P e.1 e.2.1)
      have := abs_lt.1 (abs_sectorBeta_lt P e.1 e.2.1)
      cases e.2.2 <;> simp only [endConeHi, endConeLo] <;> linarith)
    (fun e he e' he' hee' =>
      (disjoint_voronoiSector hP (hS e he).1 (hS e' he').1 (hpair e he e' he' hee')).mono
        (hsub e he) (hsub e' he'))
  simpa only [endConeHi_sub_endConeLo] using key

/-! ### Facet ends seen from the local cone -/

theorem cross_pairAxis {r q : ℂ} (v : ℂ) :
    cross (pairAxis r q) v = cross (q - r) v / ‖q - r‖ := by
  simp only [cross, pairAxis, Complex.div_ofReal_re, Complex.div_ofReal_im]
  ring

/-- Moving along `i u` from a point equidistant to `r` and `q`. -/
theorem norm_add_le_iff_cross {x r q u : ℂ} (hx : ‖x - r‖ = ‖x - q‖) (τ : ℝ) :
    ‖x + τ * (Complex.I * u) - r‖ ≤ ‖x + τ * (Complex.I * u) - q‖ ↔
      τ * cross u (q - r) ≤ 0 := by
  rw [norm_eq_norm_iff_re_im] at hx
  have key : ((x + τ * (Complex.I * u) - r).re * (x + τ * (Complex.I * u) - r).re +
      (x + τ * (Complex.I * u) - r).im * (x + τ * (Complex.I * u) - r).im) -
      ((x + τ * (Complex.I * u) - q).re * (x + τ * (Complex.I * u) - q).re +
      (x + τ * (Complex.I * u) - q).im * (x + τ * (Complex.I * u) - q).im) =
      2 * (τ * cross u (q - r)) := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im,
      Complex.mul_im, cross] at hx ⊢
    linear_combination hx
  rw [norm_le_norm_iff_re_im]
  constructor <;> intro h <;> linarith

section Local

variable {x : ℂ} {δ : ℝ}
  (hδ : ∀ y, ‖y - x‖ < δ → ∀ r ∈ nearestSites P x,
    (y ∈ voronoiCell P r ↔ ∀ q ∈ nearestSites P x, ‖y - r‖ ≤ ‖y - q‖))

include hδ in
/-- Near `x`, the facet ordinates of two nearest sites are cut out by cross products. -/
theorem mem_facetOrdinates_iff_of_local {r q' : ℂ} (hr : r ∈ nearestSites P x)
    (hq' : q' ∈ nearestSites P x) (hne : r ≠ q') {τ : ℝ} (hτ : |τ| < δ) :
    cross (pairAxis r q') (x - r) + τ ∈ facetOrdinates P r q' ↔
      ∀ q ∈ nearestSites P x, τ * cross (q' - r) (q - r) ≤ 0 := by
  have hx : x = bisectorPoint r q' (cross (pairAxis r q') (x - r)) :=
    eq_bisectorPoint_of_norm_eq hne (norm_sub_eq_of_mem_nearestSites hr hq')
  have hy : bisectorPoint r q' (cross (pairAxis r q') (x - r) + τ) =
      x + τ * (Complex.I * pairAxis r q') := by
    rw [bisectorPoint_add, ← hx]
  have hyx : ‖bisectorPoint r q' (cross (pairAxis r q') (x - r) + τ) - x‖ < δ := by
    rw [hy, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
      norm_pairAxis hne, Real.norm_eq_abs, one_mul, mul_one]
    exact hτ
  have hpos : 0 < ‖q' - r‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  show bisectorPoint r q' _ ∈ voronoiCell P r ↔ _
  rw [hδ _ hyx r hr, hy]
  refine forall₂_congr fun q hq => ?_
  rw [norm_add_le_iff_cross (norm_sub_eq_of_mem_nearestSites hr hq), cross_pairAxis,
    mul_div_assoc', div_nonpos_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (not_le.2 hpos)
    · exact h
  · intro h; exact Or.inr ⟨h, hpos.le⟩

include hδ in
/-- **The counterclockwise extremal neighbour.** -/
theorem facetEnd_true_eq_of_extremal (hP : IsVoronoiSiteSet P) (hδ0 : 0 < δ) {r q' : ℂ}
    (hr : r ∈ nearestSites P x) (hq' : q' ∈ nearestSites P x) (hne : r ≠ q')
    (hw : ∀ q ∈ nearestSites P x, 0 ≤ cross (q' - r) (q - r))
    (hs : ∃ q ∈ nearestSites P x, 0 < cross (q' - r) (q - r)) :
    IsVoronoiNeighbor P r q' ∧ facetEnd P r q' true = x := by
  set sx := cross (pairAxis r q') (x - r) with hsx
  have hin : ∀ τ, |τ| < δ → τ ≤ 0 → sx + τ ∈ facetOrdinates P r q' := fun τ hτ hτ0 =>
    (mem_facetOrdinates_iff_of_local hδ hr hq' hne hτ).2 fun q hq =>
      mul_nonpos_of_nonpos_of_nonneg hτ0 (hw q hq)
  have hout : ∀ τ, |τ| < δ → 0 < τ → sx + τ ∉ facetOrdinates P r q' := fun τ hτ hτ0 hmem => by
    obtain ⟨q, hq, hpos⟩ := hs
    have := (mem_facetOrdinates_iff_of_local hδ hr hq' hne hτ).1 hmem q hq
    exact absurd this (not_le.2 (mul_pos hτ0 hpos))
  have h0 : sx ∈ facetOrdinates P r q' := by
    simpa using hin 0 (by simpa using hδ0) le_rfl
  have h1 : sx + -(δ / 2) ∈ facetOrdinates P r q' :=
    hin _ (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) (by linarith)
  have hN : IsVoronoiNeighbor P r q' :=
    ⟨hr.1, hq'.1, hne, ⟨sx, h0, sx + -(δ / 2), h1, by intro h; linarith⟩⟩
  refine ⟨hN, ?_⟩
  have hhi : facetHi P r q' = sx := by
    refine le_antisymm ?_ (le_csSup (hN.isBounded hP).bddAbove h0)
    by_contra hlt
    rw [not_le] at hlt
    set τ := min (facetHi P r q' - sx) (δ / 2)
    have hτ0 : 0 < τ := lt_min (by linarith) (by positivity)
    have hτ1 : τ ≤ facetHi P r q' - sx := min_le_left _ _
    have hτ2 : τ ≤ δ / 2 := min_le_right _ _
    refine hout τ (by rw [abs_of_pos hτ0]; linarith) hτ0 (Icc_subset_facetOrdinates hP hN ⟨?_, ?_⟩)
    · linarith [(show facetLo P r q' ≤ sx from csInf_le (hN.isBounded hP).bddBelow h0)]
    · linarith
  show bisectorPoint r q' (facetHi P r q') = x
  rw [hhi, hsx, ← eq_bisectorPoint_of_norm_eq hne (norm_sub_eq_of_mem_nearestSites hr hq')]

include hδ in
/-- **The clockwise extremal neighbour.** -/
theorem facetEnd_false_eq_of_extremal (hP : IsVoronoiSiteSet P) (hδ0 : 0 < δ) {r q' : ℂ}
    (hr : r ∈ nearestSites P x) (hq' : q' ∈ nearestSites P x) (hne : r ≠ q')
    (hw : ∀ q ∈ nearestSites P x, cross (q' - r) (q - r) ≤ 0)
    (hs : ∃ q ∈ nearestSites P x, cross (q' - r) (q - r) < 0) :
    IsVoronoiNeighbor P r q' ∧ facetEnd P r q' false = x := by
  set sx := cross (pairAxis r q') (x - r) with hsx
  have hin : ∀ τ, |τ| < δ → 0 ≤ τ → sx + τ ∈ facetOrdinates P r q' := fun τ hτ hτ0 =>
    (mem_facetOrdinates_iff_of_local hδ hr hq' hne hτ).2 fun q hq =>
      mul_nonpos_of_nonneg_of_nonpos hτ0 (hw q hq)
  have hout : ∀ τ, |τ| < δ → τ < 0 → sx + τ ∉ facetOrdinates P r q' := fun τ hτ hτ0 hmem => by
    obtain ⟨q, hq, hneg⟩ := hs
    have := (mem_facetOrdinates_iff_of_local hδ hr hq' hne hτ).1 hmem q hq
    exact absurd this (not_le.2 (mul_pos_of_neg_of_neg hτ0 hneg))
  have h0 : sx ∈ facetOrdinates P r q' := by
    simpa using hin 0 (by simpa using hδ0) le_rfl
  have h1 : sx + δ / 2 ∈ facetOrdinates P r q' :=
    hin _ (by rw [abs_of_pos (by positivity)]; linarith) (by positivity)
  have hN : IsVoronoiNeighbor P r q' :=
    ⟨hr.1, hq'.1, hne, ⟨sx, h0, sx + δ / 2, h1, by intro h; linarith⟩⟩
  refine ⟨hN, ?_⟩
  have hlo : facetLo P r q' = sx := by
    refine le_antisymm (csInf_le (hN.isBounded hP).bddBelow h0) ?_
    by_contra hlt
    rw [not_le] at hlt
    set τ := min (sx - facetLo P r q') (δ / 2)
    have hτ0 : 0 < τ := lt_min (by linarith) (by positivity)
    have hτ1 : τ ≤ sx - facetLo P r q' := min_le_left _ _
    have hτ2 : τ ≤ δ / 2 := min_le_right _ _
    refine hout (-τ) (by rw [abs_neg, abs_of_pos hτ0]; linarith) (by linarith)
      (Icc_subset_facetOrdinates hP hN ⟨?_, ?_⟩)
    · linarith
    · linarith [(show sx ≤ facetHi P r q' from le_csSup (hN.isBounded hP).bddAbove h0)]
  show bisectorPoint r q' (facetLo P r q') = x
  rw [hlo, hsx, ← eq_bisectorPoint_of_norm_eq hne (norm_sub_eq_of_mem_nearestSites hr hq')]

end Local

/-! ### Six ends -/

/-- The ends of a facet are equidistant from both of its sites, which are nearest sites. -/
theorem mem_nearestSites_facetEnd (hP : IsVoronoiSiteSet P) {p q : ℂ}
    (h : IsVoronoiNeighbor P p q) (b : Bool) :
    p ∈ nearestSites P (facetEnd P p q b) ∧ q ∈ nearestSites P (facetEnd P p q b) := by
  have hc := facetEnd_mem_voronoiCell hP h b
  refine ⟨⟨h.1, hc⟩, ⟨h.2.1, ?_⟩⟩
  exact (mem_voronoiCell_iff_of_norm_eq (norm_facetEnd_sub_eq h b)).2 hc

/-- **A facet end has at least three nearest sites.** -/
theorem three_le_card_nearestSites (hP : IsVoronoiSiteSet P) {p q : ℂ}
    (h : IsVoronoiNeighbor P p q) (b : Bool) :
    3 ≤ (finite_nearestSites hP.locallyFinite (facetEnd P p q b)).toFinset.card := by
  set x := facetEnd P p q b with hx
  set Nf := (finite_nearestSites hP.locallyFinite x).toFinset with hNf
  obtain ⟨hp, hq⟩ := mem_nearestSites_facetEnd hP h b
  by_contra hlt
  rw [not_le] at hlt
  have hsub : ({p, q} : Finset ℂ) ⊆ Nf := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact (Set.Finite.mem_toFinset _).2 hp
    · rw [Finset.mem_singleton.1 hz]; exact (Set.Finite.mem_toFinset _).2 hq
  have hcard : Nf.card ≤ ({p, q} : Finset ℂ).card := by
    rw [Finset.card_pair h.ne]; omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have honly : ∀ z ∈ nearestSites P x, z = p ∨ z = q := by
    intro z hz
    have : z ∈ Nf := (Set.Finite.mem_toFinset _).2 hz
    rw [← heq] at this
    simpa using this
  obtain ⟨δ, hδ0, hδ⟩ := exists_local_cone hP.locallyFinite x
  set sb := (match b with | true => facetHi P p q | false => facetLo P p q) with hsb
  have hxb : x = bisectorPoint p q sb := by cases b <;> rfl
  set τ : ℝ := (match b with | true => δ / 2 | false => -(δ / 2)) with hτ
  have hτabs : |τ| < δ := by
    cases b
    · simp only [hτ, abs_neg, abs_of_pos (half_pos hδ0)]; linarith
    · simp only [hτ, abs_of_pos (half_pos hδ0)]; linarith
  have hmem : sb + τ ∈ facetOrdinates P p q := by
    show bisectorPoint p q (sb + τ) ∈ voronoiCell P p
    have hy : bisectorPoint p q (sb + τ) = x + τ * (Complex.I * pairAxis p q) := by
      rw [bisectorPoint_add, ← hxb]
    have hyx : ‖bisectorPoint p q (sb + τ) - x‖ < δ := by
      rw [hy, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
        norm_pairAxis h.ne, Real.norm_eq_abs, one_mul, mul_one]
      exact hτabs
    rw [hδ _ hyx p hp]
    intro z hz
    rcases honly z hz with rfl | rfl
    · exact le_rfl
    · exact (norm_bisectorPoint_sub_eq h.ne _).le
  cases b
  · have := csInf_le (h.isBounded hP).bddBelow hmem
    simp only [hsb, hτ, facetLo] at this
    linarith
  · have := le_csSup (h.isBounded hP).bddAbove hmem
    simp only [hsb, hτ, facetHi] at this
    linarith

/-- **Six ends at every vertex.** If a facet ends at `x`, at least six sector ends (incidence and
end) sit at `x`. -/
theorem exists_six_endpoints (hP : IsVoronoiSiteSet P) {p q : ℂ} (h : IsVoronoiNeighbor P p q)
    (b : Bool) :
    ∃ S : Finset (ℂ × ℂ × Bool), 6 ≤ S.card ∧
      ∀ e ∈ S, IsVoronoiNeighbor P e.1 e.2.1 ∧ facetEnd P e.1 e.2.1 e.2.2 = facetEnd P p q b := by
  set x := facetEnd P p q b with hx
  have h3 := three_le_card_nearestSites hP h b
  rw [← hx] at h3
  set Nf := (finite_nearestSites hP.locallyFinite x).toFinset with hNf
  have hmemN : ∀ z, z ∈ Nf ↔ z ∈ nearestSites P x := fun z => Set.Finite.mem_toFinset _
  obtain ⟨hp, -⟩ := mem_nearestSites_facetEnd hP h b
  rw [← hx] at hp
  set R := ‖x - p‖
  have hcirc : ∀ z ∈ Nf, ‖z - x‖ = R := fun z hz => by
    rw [norm_sub_rev]; exact norm_sub_eq_of_mem_nearestSites ((hmemN z).1 hz) hp
  obtain ⟨δ, hδ0, hδ⟩ := exists_local_cone hP.locallyFinite x
  have hsel : ∀ (r : ℂ) (c : Bool), ∃ q' : ℂ, r ∈ Nf →
      IsVoronoiNeighbor P r q' ∧ facetEnd P r q' c = x := by
    intro r c
    by_cases hr : r ∈ Nf
    · cases c
      · obtain ⟨qm, hqm, hqmr, hw, q₁, hq₁, hs⟩ := exists_extremal' hcirc hr h3
        refine ⟨qm, fun _ => facetEnd_false_eq_of_extremal hδ hP hδ0 ((hmemN r).1 hr)
          ((hmemN qm).1 hqm) hqmr.symm (fun q hq => hw q ((hmemN q).2 hq))
          ⟨q₁, (hmemN q₁).1 hq₁, hs⟩⟩
      · obtain ⟨qp, hqp, hqpr, hw, q₁, hq₁, hs⟩ := exists_extremal hcirc hr h3
        refine ⟨qp, fun _ => facetEnd_true_eq_of_extremal hδ hP hδ0 ((hmemN r).1 hr)
          ((hmemN qp).1 hqp) hqpr.symm (fun q hq => hw q ((hmemN q).2 hq))
          ⟨q₁, (hmemN q₁).1 hq₁, hs⟩⟩
    · exact ⟨r, fun h' => absurd h' hr⟩
  choose g hg using hsel
  set f : ℂ × Bool → ℂ × ℂ × Bool := fun rc => (rc.1, g rc.1 rc.2, rc.2) with hf
  refine ⟨(Nf ×ˢ (Finset.univ : Finset Bool)).image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (fun a b hab => by
      simp only [hf, Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2), Finset.card_product, Finset.card_univ, Fintype.card_bool]
    omega
  · intro e he
    obtain ⟨⟨r, c⟩, hrc, rfl⟩ := Finset.mem_image.1 he
    exact hg r c (Finset.mem_product.1 hrc).1

end SandierSerfaty

end
