/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.RadialData
public import SandierSerfaty.Geometry.VoronoiSectorCover
public import SandierSerfaty.Geometry.VoronoiSectorTotals

/-!
# The gauge of a Voronoi cell and the cell trial function

For a site set `P` and `p ∈ P`, the **gauge** of the cell `C_p = voronoiCell P p` is
`gauge P p w = sup_{q ∈ P} 2 ⟨w, q - p⟩ / ‖q - p‖²` (the term `q = p` contributes `0`). It is
positively homogeneous, `d₀⁻¹`-Lipschitz (if distinct sites are `2 d₀`-separated), and
`gauge P p w ≤ 1 ↔ p + w ∈ C_p` (`gauge_le_one_iff`). For `w ≠ 0` the exit distance of the ray from
`p` through `p + w` is `t = ‖w‖ / gauge P p w ∈ [d₀, R]`.

The trial function of the paper (`dual:trial`) on the cell of `p` is
`cellH R P p z = Fpair R (‖z - p‖, gauge P p (z - p))`, i.e. `B(r) + ∑ᵢ (r/t)^{kᵢ} Dᵢ(t)` with
`t = r / gauge`; on the sector of `(p, q)` the gauge is `Re(conj u (z-p)) / d` (`gauge_eq_of_mem_sector`).
Two cells agree on their common boundary (`cellH_eq_of_mem_voronoiCell`), which is the gluing
in this formulation.
-/

open Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

/-- Standing assumptions on a site set: separation `2 d₀`, local finiteness, uniformly bounded cells. -/
structure SepSites (P : Set ℂ) (d₀ : ℝ) : Prop where
  /-- `d₀ > 0`. -/
  pos : 0 < d₀
  /-- There is a site. -/
  nonempty : P.Nonempty
  /-- Local finiteness. -/
  locallyFinite : LocallyFiniteSites P
  /-- Distinct sites are at distance at least `2 d₀`. -/
  sep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * d₀ ≤ ‖p - q‖
  /-- The cells are uniformly bounded. -/
  bdd : ∃ R : ℝ, ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R

/-- The linear form `w ↦ 2 ⟨w, q - p⟩ / ‖q - p‖²` (zero for `q = p`). -/
@[expose] noncomputable def gaugeLin (p q w : ℂ) : ℝ := 2 * (w * (starRingEnd ℂ) (q - p)).re / ‖q - p‖ ^ 2

/-- The gauge of the Voronoi cell of `p`. -/
@[expose] noncomputable def gauge (P : Set ℂ) (p w : ℂ) : ℝ := ⨆ q : P, gaugeLin p q w

variable {P : Set ℂ} {d₀ : ℝ} {p q : ℂ}

theorem gaugeLin_self (p w : ℂ) : gaugeLin p p w = 0 := by simp [gaugeLin]

theorem gaugeLin_smul (p q w : ℂ) (c : ℝ) : gaugeLin p q ((c : ℂ) * w) = c * gaugeLin p q w := by
  unfold gaugeLin
  rw [mul_assoc, Complex.re_ofReal_mul]
  ring

theorem abs_gaugeLin_le (hq : p ≠ q) (hsep : 2 * d₀ ≤ ‖p - q‖) (hd : 0 < d₀) (w : ℂ) :
    |gaugeLin p q w| ≤ ‖w‖ / d₀ := by
  unfold gaugeLin
  have hv : q - p ≠ 0 := sub_ne_zero.2 hq.symm
  have hn : 2 * d₀ ≤ ‖q - p‖ := by rwa [norm_sub_rev]
  have hnp : 0 < ‖q - p‖ := norm_pos_iff.2 hv
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ‖q - p‖ ^ 2), div_le_div_iff₀
    (by positivity) hd]
  have h1 : |(w * (starRingEnd ℂ) (q - p)).re| ≤ ‖w‖ * ‖q - p‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have : 2 * |(w * (starRingEnd ℂ) (q - p)).re| * d₀ ≤ 2 * (‖w‖ * ‖q - p‖) * d₀ := by
    gcongr
  calc 2 * |(w * (starRingEnd ℂ) (q - p)).re| * d₀ ≤ 2 * (‖w‖ * ‖q - p‖) * d₀ := this
    _ = ‖w‖ * (2 * d₀ * ‖q - p‖) := by ring
    _ ≤ ‖w‖ * (‖q - p‖ * ‖q - p‖) := by gcongr
    _ = ‖w‖ * ‖q - p‖ ^ 2 := by ring

section Gauge

variable (hS : SepSites P d₀) (hp : p ∈ P)
include hS hp

theorem abs_gaugeLin_le' (hq : q ∈ P) (w : ℂ) : |gaugeLin p q w| ≤ ‖w‖ / d₀ := by
  by_cases h : p = q
  · subst h; simp [gaugeLin_self]; exact div_nonneg (norm_nonneg _) hS.pos.le
  · exact abs_gaugeLin_le h (hS.sep p hp q hq h) hS.pos w

theorem bddAbove_gaugeLin (w : ℂ) : BddAbove (range fun q : P => gaugeLin p q w) := by
  refine ⟨‖w‖ / d₀, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact (le_abs_self _).trans (abs_gaugeLin_le' hS hp q.2 w)

theorem gaugeLin_le_gauge (hq : q ∈ P) (w : ℂ) : gaugeLin p q w ≤ gauge P p w :=
  le_ciSup (f := fun q : P => gaugeLin p q w) (bddAbove_gaugeLin hS hp w) ⟨q, hq⟩

theorem gauge_nonneg (w : ℂ) : 0 ≤ gauge P p w := by
  have := gaugeLin_le_gauge hS hp hp w
  rwa [gaugeLin_self] at this

theorem gauge_le_iff {c : ℝ} (w : ℂ) : gauge P p w ≤ c ↔ ∀ q ∈ P, gaugeLin p q w ≤ c := by
  have : Nonempty P := ⟨⟨p, hp⟩⟩
  unfold gauge
  rw [ciSup_le_iff (bddAbove_gaugeLin hS hp w)]
  exact ⟨fun h q hq => h ⟨q, hq⟩, fun h q => h q q.2⟩

theorem gauge_le_norm_div (w : ℂ) : gauge P p w ≤ ‖w‖ / d₀ := by
  rw [gauge_le_iff hS hp]
  exact fun q hq => (le_abs_self _).trans (abs_gaugeLin_le' hS hp hq w)

theorem gauge_smul_le (w : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    gauge P p ((c : ℂ) * w) ≤ c * gauge P p w := by
  rw [gauge_le_iff hS hp]
  intro q hq
  rw [gaugeLin_smul]
  exact mul_le_mul_of_nonneg_left (gaugeLin_le_gauge hS hp hq w) hc

theorem gauge_smul (w : ℂ) {c : ℝ} (hc : 0 ≤ c) : gauge P p ((c : ℂ) * w) = c * gauge P p w := by
  rcases hc.eq_or_lt with rfl | hc'
  · simp only [Complex.ofReal_zero, zero_mul, zero_mul]
    refine le_antisymm ?_ (gauge_nonneg hS hp 0)
    rw [gauge_le_iff hS hp]
    intro q hq
    simp [gaugeLin]
  · refine le_antisymm (gauge_smul_le hS hp w hc) ?_
    have h := gauge_smul_le hS hp ((c : ℂ) * w) (inv_nonneg.2 hc)
    have e : ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * w) = w := by
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc'.ne']; simp
    rw [e] at h
    calc c * gauge P p w ≤ c * (c⁻¹ * gauge P p ((c : ℂ) * w)) := by gcongr
      _ = gauge P p ((c : ℂ) * w) := by field_simp

theorem abs_gauge_sub_le (w w' : ℂ) : |gauge P p w - gauge P p w'| ≤ ‖w - w'‖ / d₀ := by
  have key : ∀ w w' : ℂ, gauge P p w ≤ gauge P p w' + ‖w - w'‖ / d₀ := by
    intro w w'
    rw [gauge_le_iff hS hp]
    intro q hq
    have h1 : gaugeLin p q w = gaugeLin p q w' + gaugeLin p q (w - w') := by
      unfold gaugeLin; rw [sub_mul, Complex.sub_re]; ring
    have h2 := (le_abs_self _).trans (abs_gaugeLin_le' hS hp hq (w - w'))
    have h3 := gaugeLin_le_gauge hS hp hq w'
    linarith
  rw [abs_le]
  constructor
  · have := key w' w
    rw [norm_sub_rev] at this
    linarith
  · have := key w w'
    linarith

theorem lipschitzWith_gauge : LipschitzWith (Real.toNNReal (1 / d₀)) (gauge P p) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by have := hS.pos; positivity)]
  refine (abs_gauge_sub_le hS hp w w').trans ?_
  rw [one_div, inv_mul_eq_div]

/-- `p + w` lies in the Voronoi cell of `p` iff the gauge of `w` is at most `1`. -/
theorem gauge_le_one_iff (w : ℂ) : gauge P p w ≤ 1 ↔ p + w ∈ voronoiCell P p := by
  rw [gauge_le_iff hS hp, mem_voronoiCell]
  refine forall_congr' fun q => forall_congr' fun hq => ?_
  by_cases h : p = q
  · subst h; simp [gaugeLin_self]
  · have hv : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
    unfold gaugeLin
    rw [div_le_one (by positivity)]
    have e : p + w - q = w - (q - p) := by ring
    rw [add_sub_cancel_left, e, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_sub]
    constructor <;> intro h <;> linarith [Complex.normSq_nonneg w]

end Gauge

theorem SepSites.isVoronoiSiteSet (hS : SepSites P d₀) : IsVoronoiSiteSet P :=
  ⟨hS.locallyFinite, fun p hp => by
    obtain ⟨R, hR⟩ := hS.bdd
    exact isBounded_closedBall.subset (hR p hp)⟩

theorem gaugeLin_eq_one_of_norm_eq (hq : q ≠ p) {w : ℂ} (h : ‖w‖ = ‖w - (q - p)‖) :
    gaugeLin p q w = 1 := by
  have hv : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hq)
  unfold gaugeLin
  rw [div_eq_one_iff_eq (by positivity)]
  have h2 : ‖w‖ ^ 2 = ‖w - (q - p)‖ ^ 2 := by rw [h]
  simp only [Complex.sq_norm, Complex.normSq_sub] at h2 ⊢
  linarith

theorem gaugeLin_eq_re_div (hpq : p ≠ q) (w : ℂ) :
    gaugeLin p q w = (w * (starRingEnd ℂ) (pairAxis p q)).re / pairHalfDist p q := by
  have hv : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq.symm)
  unfold gaugeLin pairAxis pairHalfDist
  have : (starRingEnd ℂ) ((q - p) / ((‖q - p‖ : ℝ) : ℂ)) =
      (starRingEnd ℂ) (q - p) / ((‖q - p‖ : ℝ) : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal]
  rw [this, ← mul_div_assoc, Complex.div_ofReal_re]
  field_simp

section Cell

variable (hS : SepSites P d₀) (hp : p ∈ P)
include hS hp

theorem norm_le_mul_gauge {R : ℝ} (hR : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R) (w : ℂ) :
    ‖w‖ ≤ R * gauge P p w := by
  have hR0 : 0 ≤ R := by
    have := hR p hp (mem_voronoiCell_self P p)
    simpa using this
  have key : ∀ c : ℝ, 0 ≤ c → c * gauge P p w ≤ 1 → c * ‖w‖ ≤ R := by
    intro c hc hcg
    have hg : gauge P p ((c : ℂ) * w) ≤ 1 := by rw [gauge_smul hS hp w hc]; exact hcg
    have := hR p hp ((gauge_le_one_iff hS hp _).1 hg)
    rw [mem_closedBall, dist_eq_norm] at this
    simpa [norm_mul, abs_of_nonneg hc] using this
  by_cases hw : w = 0
  · subst hw; simp; exact mul_nonneg hR0 (gauge_nonneg hS hp 0)
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  by_contra hcon
  rw [not_le] at hcon
  by_cases hg : gauge P p w = 0
  · have := key ((R + 1) / ‖w‖) (by positivity) (by rw [hg]; simp)
    rw [div_mul_cancel₀ _ hwn.ne'] at this
    linarith
  · have hgpos : 0 < gauge P p w := lt_of_le_of_ne (gauge_nonneg hS hp w) (Ne.symm hg)
    have := key (1 / gauge P p w) (by positivity) (by rw [one_div, inv_mul_cancel₀ hgpos.ne'])
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hgpos] at this
    linarith

theorem gauge_pos {R : ℝ} (hR : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R) {w : ℂ} (hw : w ≠ 0) :
    0 < gauge P p w := by
  have h1 := norm_le_mul_gauge hS hp hR w
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hR0 : 0 ≤ R := by
    have := hR p hp (mem_voronoiCell_self P p)
    simpa using this
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [mul_nonneg hR0 (gauge_nonneg hS hp w)]

theorem mem_cone_of_mem_cell {R T₀ : ℝ} (hR : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R)
    (hT : R ≤ T₀) {z : ℂ} (hz : z ∈ voronoiCell P p) (hne : z ≠ p) :
    (‖z - p‖, gauge P p (z - p)) ∈ cone d₀ T₀ := by
  have hw : z - p ≠ 0 := sub_ne_zero.2 hne
  have hg := gauge_pos hS hp hR hw
  refine ⟨hg, (gauge_le_one_iff hS hp _).2 (by simpa using hz), ?_, ?_⟩
  · have := gauge_le_norm_div hS hp (z - p)
    have h0 := hS.pos
    rw [le_div_iff₀ h0] at this
    simp only
    linarith
  · have h1 := norm_le_mul_gauge hS hp hR (z - p)
    simp only
    have : R * gauge P p (z - p) ≤ T₀ * gauge P p (z - p) := mul_le_mul_of_nonneg_right hT hg.le
    linarith

/-- Two cells agree on their common boundary: the gauge is `1` there and the distances coincide. -/
theorem gauge_eq_one_of_mem_two {p' z : ℂ} (hp' : p' ∈ P) (hne : p ≠ p')
    (hz : z ∈ voronoiCell P p) (hz' : z ∈ voronoiCell P p') :
    gauge P p (z - p) = 1 ∧ ‖z - p‖ = ‖z - p'‖ := by
  have h1 : ‖z - p‖ ≤ ‖z - p'‖ := hz p' hp'
  have h2 : ‖z - p'‖ ≤ ‖z - p‖ := hz' p hp
  have heq : ‖z - p‖ = ‖z - p'‖ := le_antisymm h1 h2
  refine ⟨le_antisymm ((gauge_le_one_iff hS hp _).2 (by simpa using hz)) ?_, heq⟩
  have e : z - p' = (z - p) - (p' - p) := by ring
  have := gaugeLin_eq_one_of_norm_eq (p := p) (q := p') (w := z - p) (Ne.symm hne) (by rw [← e]; exact heq)
  rw [← this]
  exact gaugeLin_le_gauge hS hp hp' _

/-- In the sector of `(p, q)` the gauge is the linear form of the facet of `q`. -/
theorem gauge_eq_gaugeLin_of_mem_sector (h : IsVoronoiNeighbor P p q) {z : ℂ}
    (hz : z ∈ voronoiSector P p q) : gauge P p (z - p) = gaugeLin p q (z - p) := by
  have hSS := hS.isVoronoiSiteSet
  obtain ⟨t, s, ht0, ht1, hs0, hs1, rfl⟩ := exists_of_mem_voronoiSector h hz
  set y := bisectorPoint p q s with hy
  have hycell : y ∈ voronoiCell P p := Icc_subset_facetOrdinates hSS h ⟨hs0.le, hs1.le⟩
  have hqne : q ≠ p := h.ne.symm
  have hy1 : gauge P p (y - p) = 1 := by
    refine le_antisymm ((gauge_le_one_iff hS hp _).2 (by simpa using hycell)) ?_
    have e : y - q = (y - p) - (q - p) := by ring
    have := gaugeLin_eq_one_of_norm_eq (p := p) (q := q) (w := y - p) hqne
      (by rw [← e]; exact norm_bisectorPoint_sub_eq h.ne s)
    rw [← this]
    exact gaugeLin_le_gauge hS hp h.2.1 _
  have hy2 : gaugeLin p q (y - p) = 1 := by
    have e : y - q = (y - p) - (q - p) := by ring
    exact gaugeLin_eq_one_of_norm_eq (p := p) (q := q) (w := y - p) hqne
      (by rw [← e]; exact norm_bisectorPoint_sub_eq h.ne s)
  have e : p + (t : ℂ) * (y - p) - p = (t : ℂ) * (y - p) := by ring
  rw [e, gauge_smul hS hp _ ht0.le, gaugeLin_smul, hy1, hy2]

end Cell

end Dual

end SandierSerfaty

end
