/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiVertex

/-!
# The sectors of a cell cover it up to a null set

For a site `p` of a set of sites with locally finite sites and bounded cells, the sectors
`voronoiSector P p q` over the Voronoi neighbours `q` of `p` cover the cell `C_p` up to a Lebesgue
null set (`volume_voronoiCell_diff_iUnion_voronoiSector`).

Proof. Let `z ∈ C_p` with `z ≠ p`, `z` on no bisector of `p` with another site.
Follow the ray from `p` through `z` to its exit point `y = p + t* (z - p)` from the cell (`t* > 1`).
The exit point has a nearest site `q ≠ p`.

* If `p` and `q` are the only nearest sites of `y`, the local cone lemma puts `y` in the relative
  interior of the facet of `p` toward `q`, so `z` lies in the sector of `(p, q)`.
* Otherwise `y` is equidistant from three distinct sites `p, q, q'`; such a point is unique for
  given `q, q'` (`eq_of_norm_sub_eq_of_norm_sub_eq`), so `z` lies on one of countably many lines
  through `p`.

The exceptional set is therefore contained in `{p}`, the countably many bisectors of `p`, and
countably many lines through `p`; each is null.

The estimate "a finite
union of lines plus a point" is replaced by a countable union, which needs no finiteness of the
near sites beyond countability of the sites.
-/

open MeasureTheory Metric Set Real

public section

namespace SandierSerfaty

variable {P : Set ℂ} {p q : ℂ}

theorem LocallyFiniteSites.countable (hP : LocallyFiniteSites P) : P.Countable := by
  have : P = ⋃ k : ℕ, P ∩ closedBall 0 k := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
    exact ⟨fun hz => ⟨⌈‖z‖⌉₊, hz, Nat.le_ceil _⟩, fun ⟨_, hz, _⟩ => hz⟩
  rw [this]
  exact countable_iUnion fun k => (hP 0 k).countable

/-- Converse to `exists_of_mem_voronoiSector`. -/
theorem mem_voronoiSector_of (h : IsVoronoiNeighbor P p q) {t s : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hs0 : facetLo P p q < s) (hs1 : s < facetHi P p q) :
    p + t * (bisectorPoint p q s - p) ∈ voronoiSector P p q := by
  have hd := pairHalfDist_pos h.ne
  refine ⟨(t : ℂ) * ((pairHalfDist p q : ℂ) + (s : ℂ) * Complex.I), ?_, ?_⟩
  · simp only [modelSector, mem_ofPred_eq, tan_sectorAlpha, tan_sectorBeta, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero, zero_add]
    have e1 : -(-facetLo P p q / pairHalfDist p q) * (t * pairHalfDist p q) =
        t * facetLo P p q := by field_simp
    have e2 : facetHi P p q / pairHalfDist p q * (t * pairHalfDist p q) =
        t * facetHi P p q := by field_simp
    rw [e1, e2]
    refine ⟨by positivity, ?_, mul_lt_mul_of_pos_left hs0 ht0, mul_lt_mul_of_pos_left hs1 ht0⟩
    nlinarith
  · simp only [bisectorPoint]; ring

/-- **Circumcentre uniqueness.** At most one point is equidistant from three distinct points. -/
theorem eq_of_norm_sub_eq_of_norm_sub_eq {q' y₁ y₂ : ℂ} (hqp : q ≠ p) (hq'p : q' ≠ p)
    (hq'q : q' ≠ q) (h₁ : ‖y₁ - p‖ = ‖y₁ - q‖) (h₁' : ‖y₁ - p‖ = ‖y₁ - q'‖)
    (h₂ : ‖y₂ - p‖ = ‖y₂ - q‖) (h₂' : ‖y₂ - p‖ = ‖y₂ - q'‖) : y₁ = y₂ := by
  by_contra hne
  have hw : y₁ - y₂ ≠ 0 := sub_ne_zero.2 hne
  have hc : cross (q - p) (q' - p) = 0 := by
    rw [norm_eq_norm_iff_re_im] at h₁ h₁' h₂ h₂'
    simp only [Complex.sub_re, Complex.sub_im] at h₁ h₁' h₂ h₂'
    have k1 : (y₁.re - y₂.re) * (q.re - p.re) + (y₁.im - y₂.im) * (q.im - p.im) = 0 := by
      linear_combination (h₁ - h₂) / 2
    have k2 : (y₁.re - y₂.re) * (q'.re - p.re) + (y₁.im - y₂.im) * (q'.im - p.im) = 0 := by
      linear_combination (h₁' - h₂') / 2
    have c1 : cross (q - p) (q' - p) * (y₁.re - y₂.re) = 0 := by
      simp only [cross, Complex.sub_re, Complex.sub_im]
      linear_combination (q'.im - p.im) * k1 - (q.im - p.im) * k2
    have c2 : cross (q - p) (q' - p) * (y₁.im - y₂.im) = 0 := by
      simp only [cross, Complex.sub_re, Complex.sub_im]
      linear_combination -(q'.re - p.re) * k1 + (q.re - p.re) * k2
    by_contra hc
    apply hw
    apply Complex.ext
    · have := (mul_eq_zero.1 c1).resolve_left hc
      simp only [Complex.sub_re, Complex.zero_re]; linarith
    · have := (mul_eq_zero.1 c2).resolve_left hc
      simp only [Complex.sub_im, Complex.zero_im]; linarith
  have hr : ‖p - y₁‖ = ‖y₁ - p‖ := norm_sub_rev _ _
  have hq : ‖q - y₁‖ = ‖y₁ - p‖ := by rw [norm_sub_rev, h₁]
  have hq' : ‖q' - y₁‖ = ‖y₁ - p‖ := by rw [norm_sub_rev, h₁']
  exact hq'q (eq_of_cross_eq_zero hr hq hq' hqp hq'p hc)

/-- Points on the line through `p` and `y ≠ p` are equidistant from `p ± i (y - p)`. -/
theorem mem_perpBisector_of_eq_add_mul {y z : ℂ} {t : ℝ} (hz : y - p = t * (z - p)) :
    z ∈ (AffineSubspace.perpBisector (p + Complex.I * (y - p)) (p - Complex.I * (y - p)) :
      Set ℂ) := by
  rw [SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq, dist_eq_norm, dist_eq_norm,
    hz, norm_eq_norm_iff_re_im]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

/-- **The sectors of a cell cover it up to a null set.** -/
theorem volume_voronoiCell_diff_iUnion_voronoiSector (hP : IsVoronoiSiteSet P) (hp : p ∈ P) :
    volume (voronoiCell P p \ ⋃ q ∈ {q | IsVoronoiNeighbor P p q}, voronoiSector P p q) = 0 := by
  have hPc := hP.locallyFinite.countable
  set B : Set ℂ := ⋃ q ∈ P \ {p}, (AffineSubspace.perpBisector p q : Set ℂ) with hB
  set C3 : ℂ × ℂ → Set ℂ := fun e => {y | e.1 ≠ p ∧ e.2 ≠ p ∧ e.2 ≠ e.1 ∧
    ‖y - p‖ = ‖y - e.1‖ ∧ ‖y - p‖ = ‖y - e.2‖} with hC3
  set L : Set ℂ := ⋃ e ∈ P ×ˢ P, ⋃ y ∈ C3 e,
    (AffineSubspace.perpBisector (p + Complex.I * (y - p)) (p - Complex.I * (y - p)) : Set ℂ)
    with hL
  have hBnull : volume B = 0 := by
    refine (measure_biUnion_null_iff (hPc.mono sdiff_subset)).2 fun q hq => ?_
    exact volume_perpBisector_eq_zero (Ne.symm hq.2)
  have hLnull : volume L = 0 := by
    refine (measure_biUnion_null_iff (hPc.prod hPc)).2 fun e _ => ?_
    have hsub : (C3 e).Subsingleton := fun y₁ hy₁ y₂ hy₂ =>
      eq_of_norm_sub_eq_of_norm_sub_eq hy₁.1 hy₁.2.1 hy₁.2.2.1 hy₁.2.2.2.1 hy₁.2.2.2.2
        hy₂.2.2.2.1 hy₂.2.2.2.2
    refine (measure_biUnion_null_iff hsub.countable).2 fun y hy => ?_
    refine volume_perpBisector_eq_zero fun heq => ?_
    have hyp : y - p = 0 := by
      have : (2 : ℂ) * (Complex.I * (y - p)) = 0 := by linear_combination heq
      simpa [Complex.I_ne_zero] using this
    have := hy.2.2.2.1
    rw [hyp, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero.1 hyp, sub_eq_zero] at this
    exact hy.1 this.symm
  refine measure_mono_null ?_ (measure_union_null (measure_union_null
    (Set.Countable.measure_zero (countable_singleton p) _) hBnull) hLnull)
  rintro z ⟨hz, hzT⟩
  by_contra hzE
  simp only [mem_union, mem_singleton_iff, not_or] at hzE
  obtain ⟨⟨hzp, hzB⟩, hzL⟩ := hzE
  -- `z` is strictly closer to `p` than to any other site
  have hstrict : ∀ q ∈ P, q ≠ p → ‖z - p‖ < ‖z - q‖ := by
    intro q hq hqp
    refine lt_of_le_of_ne (hz q hq) fun heq => hzB ?_
    refine mem_biUnion (x := q) ⟨hq, hqp⟩ ?_
    rw [SetLike.mem_coe, AffineSubspace.mem_perpBisector_iff_dist_eq, dist_eq_norm, dist_eq_norm,
      heq]
  have hzp' : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hzp)
  -- the exit parameter
  set K : Set ℝ := Ici 0 ∩ (fun t : ℝ => p + t * (z - p)) ⁻¹' voronoiCell P p with hK
  have hKc : IsClosed K :=
    isClosed_Ici.inter ((isClosed_voronoiCell P p).preimage (by fun_prop))
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall p).1 (hP.isBounded_cell p hp)
  have hKb : BddAbove K := by
    refine ⟨R / ‖z - p‖, fun t ht => ?_⟩
    have h1 := hR ht.2
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht.1] at h1
    rw [le_div_iff₀ hzp']; exact h1
  have h1K : (1 : ℝ) ∈ K := ⟨zero_le_one, by simpa using hz⟩
  set ts := sSup K with hts
  have htsK : ts ∈ K := hKc.csSup_mem ⟨1, h1K⟩ hKb
  have hts1 : 1 ≤ ts := le_csSup hKb h1K
  set y := p + ts * (z - p) with hy
  have hyC : y ∈ voronoiCell P p := htsK.2
  have hpN : p ∈ nearestSites P y := ⟨hp, hyC⟩
  obtain ⟨δ, hδ0, hδ⟩ := exists_local_cone hP.locallyFinite y
  -- the exit point has another nearest site
  obtain ⟨q, hqN, hqp⟩ : ∃ q ∈ nearestSites P y, q ≠ p := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    set τ := δ / (2 * ‖z - p‖) with hτ
    have hτ0 : 0 < τ := by positivity
    have hmem : ts + τ ∈ K := by
      refine ⟨Set.mem_Ici.2 (by linarith), ?_⟩
      show p + ((ts + τ : ℝ) : ℂ) * (z - p) ∈ voronoiCell P p
      have hdist : ‖p + ((ts + τ : ℝ) : ℂ) * (z - p) - y‖ < δ := by
        rw [hy, show p + ((ts + τ : ℝ) : ℂ) * (z - p) - (p + ts * (z - p)) = τ * (z - p) by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
        rw [show τ * ‖z - p‖ = δ / 2 by rw [hτ]; field_simp]
        linarith
      rw [hδ _ hdist p hpN]
      intro q' hq'
      rw [hall q' hq']
    have := le_csSup hKb hmem
    linarith
  have hyeq : ‖y - p‖ = ‖y - q‖ := norm_sub_eq_of_mem_nearestSites hpN hqN
  have hts1' : 1 < ts := by
    refine lt_of_le_of_ne hts1 fun h1 => ?_
    have : y = z := by rw [hy, ← h1]; push_cast; ring
    rw [this] at hyeq
    exact (hstrict q hqN.1 hqp).ne hyeq
  have hts0 : 0 < ts := by linarith
  have hzy : z = p + ((1 / ts : ℝ) : ℂ) * (y - p) := by
    have hts0c : (ts : ℂ) ≠ 0 := by exact_mod_cast hts0.ne'
    rw [hy]; push_cast; field_simp; ring
  by_cases h3 : ∃ q' ∈ nearestSites P y, q' ≠ p ∧ q' ≠ q
  · -- three nearest sites: `z` lies on a line through `p` and a circumcentre
    obtain ⟨q', hq'N, hq'p, hq'q⟩ := h3
    apply hzL
    refine mem_biUnion (x := (q, q')) ⟨hqN.1, hq'N.1⟩ (mem_biUnion (x := y)
      ⟨hqp, hq'p, hq'q, hyeq, norm_sub_eq_of_mem_nearestSites hpN hq'N⟩ ?_)
    exact mem_perpBisector_of_eq_add_mul (t := ts) (by rw [hy]; ring)
  · -- exactly two nearest sites: `z` lies in the sector of `(p, q)`
    simp only [not_exists, not_and, not_not] at h3
    have honly : ∀ q₀ ∈ nearestSites P y, q₀ = p ∨ q₀ = q := fun q₀ hq₀ => by
      by_cases h : q₀ = p
      · exact Or.inl h
      · exact Or.inr (h3 q₀ hq₀ h)
    have hpq : p ≠ q := hqp.symm
    set sy := cross (pairAxis p q) (y - p) with hsy
    have hyb : y = bisectorPoint p q sy := eq_bisectorPoint_of_norm_eq hpq hyeq
    have hin : ∀ τ : ℝ, |τ| < δ → sy + τ ∈ facetOrdinates P p q := by
      intro τ hτ
      show bisectorPoint p q (sy + τ) ∈ voronoiCell P p
      have hb : bisectorPoint p q (sy + τ) = y + τ * (Complex.I * pairAxis p q) := by
        rw [bisectorPoint_add, ← hyb]
      have hdist : ‖bisectorPoint p q (sy + τ) - y‖ < δ := by
        rw [hb, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
          norm_pairAxis hpq, Real.norm_eq_abs, one_mul, mul_one]
        exact hτ
      rw [hδ _ hdist p hpN]
      intro q₀ hq₀
      rcases honly q₀ hq₀ with rfl | rfl
      · exact le_rfl
      · exact (norm_bisectorPoint_sub_eq hpq _).le
    have hδ2 : |δ / 2| < δ := by rw [abs_of_pos (half_pos hδ0)]; linarith
    have hδ2' : |-(δ / 2)| < δ := by rw [abs_neg]; exact hδ2
    have hlo := hin _ hδ2'
    have hhi := hin _ hδ2
    have hN : IsVoronoiNeighbor P p q :=
      ⟨hp, hqN.1, hpq, ⟨_, hlo, _, hhi, by intro h; linarith⟩⟩
    have h1 := (facetOrdinates_subset_Icc hP hN hlo).1
    have h2 := (facetOrdinates_subset_Icc hP hN hhi).2
    apply hzT
    refine mem_biUnion (x := q) hN ?_
    rw [hzy, hyb]
    exact mem_voronoiSector_of hN (by positivity) ((div_lt_one hts0).2 hts1') (by linarith)
      (by linarith)

end SandierSerfaty

end
