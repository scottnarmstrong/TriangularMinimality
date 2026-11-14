/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiFacet
public import SandierSerfaty.Geometry.PolarSector

/-!
# Voronoi sectors

The sector of the incidence `(p, q)` is the open triangle with apex the site `p` and base the facet
of `p` toward `q`. In the frame of the pair (`z ↦ p + u z`, `u = pairAxis p q`) it is the Cartesian
form `modelSector d α β` of the paper's sector `S(d, α, β)` (paper `geo:sector`).

* `exists_of_mem_voronoiSector`: a point of the sector is `p + t (y - p)` with `t ∈ (0, 1)` and `y`
  a relative-interior point of the facet;
* `norm_sub_lt_of_mem_voronoiSector`: points of the sector are strictly closer to `p` than to any
  other site;
* `disjoint_voronoiSector`: sectors of distinct incidences are disjoint;
* `image_polarSector_subset_voronoiSector`: the sector contains the polar sector of angle `α + β`
  about its site, with any radius `≤ d`;
* `exists_endCone_subset_voronoiSector`: near each facet end the sector contains a polar sector of
  angle `sectorBaseAngle` with apex at that end.


-/

open Metric Set Real

public section

namespace SandierSerfaty

/-- Cartesian form of the paper's `S(d, α, β)` (paper `geo:sector`). -/
@[expose] def modelSector (d α β : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < d ∧ -Real.tan α * z.re < z.im ∧ z.im < Real.tan β * z.re}

/-- The sector of the incidence `(p, q)`, placed in the plane. -/
@[expose] noncomputable def voronoiSector (P : Set ℂ) (p q : ℂ) : Set ℂ :=
  (fun z => p + pairAxis p q * z) ''
    modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q)

/-- Lower angle of the cone of the sector of `(p, q)` at its facet end `b` (seen from the end, in the
frame rotated by `-pairAxis p q`). -/
@[expose] noncomputable def endConeLo (P : Set ℂ) (p q : ℂ) : Bool → ℝ
  | true => sectorBeta P p q
  | false => -(π / 2)

/-- Upper angle of the cone of the sector of `(p, q)` at its facet end `b`. -/
@[expose] noncomputable def endConeHi (P : Set ℂ) (p q : ℂ) : Bool → ℝ
  | true => π / 2
  | false => -sectorAlpha P p q

theorem endConeHi_sub_endConeLo (P : Set ℂ) (p q : ℂ) (b : Bool) :
    endConeHi P p q b - endConeLo P p q b = sectorBaseAngle P p q b := by
  cases b
  · simp only [endConeHi, endConeLo, sectorBaseAngle]; ring
  · simp only [endConeHi, endConeLo, sectorBaseAngle]

/-! ### Points of a sector -/

section Strict

variable {P : Set ℂ} {p q : ℂ}

/-- Strictly inside the segment from a site `p` to a point of its cell, every other site is
strictly farther than `p`. -/
theorem norm_sub_lt_of_mem_segment {y q' : ℂ} (hy : y ∈ voronoiCell P p) (hq' : q' ∈ P)
    (hne : q' ≠ p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖p + t * (y - p) - p‖ < ‖p + t * (y - p) - q'‖ := by
  have h := hy q' hq'
  have e1 : p + t * (y - p) - p = (t : ℂ) * (y - p) := by ring
  have e2 : p + t * (y - p) - q' = (t : ℂ) * (y - p) - (q' - p) := by ring
  have e3 : y - q' = (y - p) - (q' - p) := by ring
  rw [e3] at h
  rw [e1, e2]
  have hE : 0 < (q' - p).re * (q' - p).re + (q' - p).im * (q' - p).im := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hne)
    rw [← Complex.normSq_apply, ← Complex.sq_norm]; positivity
  set a := y - p
  set e := q' - p
  rw [norm_le_norm_iff_re_im] at h
  rw [norm_lt_norm_iff_re_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at h ⊢
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 h), mul_pos (sub_pos.2 ht1) hE]

/-- A point of the sector is `p + t (y - p)` for `t ∈ (0, 1)` and `y` the bisector point of an
ordinate strictly between the facet ends. -/
theorem exists_of_mem_voronoiSector (h : IsVoronoiNeighbor P p q) {z : ℂ}
    (hz : z ∈ voronoiSector P p q) :
    ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ facetLo P p q < s ∧ s < facetHi P p q ∧
      z = p + t * (bisectorPoint p q s - p) := by
  obtain ⟨w, ⟨hw0, hwd, hlo, hhi⟩, rfl⟩ := hz
  have hd := pairHalfDist_pos h.ne
  set d := pairHalfDist p q with hd'
  rw [tan_sectorAlpha, ← hd'] at hlo
  rw [tan_sectorBeta, ← hd'] at hhi
  refine ⟨w.re / d, d * w.im / w.re, div_pos hw0 hd, (div_lt_one hd).2 hwd, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hw0]
    have : facetLo P p q * w.re = d * (-(-facetLo P p q / d) * w.re) := by field_simp
    rw [this]; exact mul_lt_mul_of_pos_left hlo hd
  · rw [div_lt_iff₀ hw0]
    have : facetHi P p q * w.re = d * (facetHi P p q / d * w.re) := by field_simp
    rw [this]; exact mul_lt_mul_of_pos_left hhi hd
  · rw [bisectorPoint, add_sub_cancel_left, ← hd']
    have : w = ((w.re / d : ℝ) : ℂ) * ((d : ℂ) + ((d * w.im / w.re : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.add_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im]
        field_simp
        ring
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.add_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im]
        field_simp
        ring
    conv_lhs => rw [this]
    ring

/-- **Points of a sector are strictly closer to its site than to any other site.** -/
theorem norm_sub_lt_of_mem_voronoiSector (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q)
    {z q' : ℂ} (hz : z ∈ voronoiSector P p q) (hq' : q' ∈ P) (hne : q' ≠ p) :
    ‖z - p‖ < ‖z - q'‖ := by
  obtain ⟨t, s, ht0, ht1, hs0, hs1, rfl⟩ := exists_of_mem_voronoiSector h hz
  exact norm_sub_lt_of_mem_segment (Icc_subset_facetOrdinates hP h ⟨hs0.le, hs1.le⟩) hq' hne
    ht0.le ht1

end Strict

/-! ### Disjointness -/

section Disjoint

variable {P : Set ℂ} {p q : ℂ}

/-- Distances from bisector points, in the frame of the pair. -/
theorem norm_bisectorPoint_sub_frame (h : p ≠ q) (σ : ℝ) (c : ℂ) :
    ‖bisectorPoint p q σ - c‖ =
      ‖((pairHalfDist p q : ℂ) + (σ : ℂ) * Complex.I) - (starRingEnd ℂ) (pairAxis p q) * (c - p)‖ := by
  have hu := norm_pairAxis h
  have e1 := eq_add_mul_conj_mul hu p c
  calc ‖bisectorPoint p q σ - c‖ =
        ‖(p + pairAxis p q * ((pairHalfDist p q : ℂ) + (σ : ℂ) * Complex.I)) -
          (p + pairAxis p q * ((starRingEnd ℂ) (pairAxis p q) * (c - p)))‖ := by
        rw [← e1]; rfl
    _ = _ := norm_add_mul_sub_add_mul hu _ _ _

/-- If a relative-interior point of the facet of `(p, q)` is also on the bisector of `p` and another
site `q'`, then `q' = q`. -/
theorem eq_of_mem_bisector_of_interior (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q)
    {s : ℝ} (hs0 : facetLo P p q < s) (hs1 : s < facetHi P p q) {q' : ℂ} (hq' : q' ∈ P)
    (hne : q' ≠ p) (hbis : ‖bisectorPoint p q s - p‖ = ‖bisectorPoint p q s - q'‖) : q' = q := by
  set η := min (s - facetLo P p q) (facetHi P p q - s) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hη1 : η ≤ s - facetLo P p q := min_le_left _ _
  have hη2 : η ≤ facetHi P p q - s := min_le_right _ _
  have hmem : ∀ σ, facetLo P p q ≤ σ → σ ≤ facetHi P p q →
      ‖bisectorPoint p q σ - p‖ ≤ ‖bisectorPoint p q σ - q'‖ := fun σ h1 h2 =>
    Icc_subset_facetOrdinates hP h ⟨h1, h2⟩ q' hq'
  have hplus := hmem (s + η) (by linarith) (by linarith)
  have hminus := hmem (s - η) (by linarith) (by linarith)
  have hd := pairHalfDist_pos h.ne
  rw [norm_bisectorPoint_sub_frame h.ne _ p, norm_bisectorPoint_sub_frame h.ne _ q'] at hbis
  rw [norm_bisectorPoint_sub_frame h.ne _ p, norm_bisectorPoint_sub_frame h.ne _ q'] at hplus
  rw [norm_bisectorPoint_sub_frame h.ne _ p, norm_bisectorPoint_sub_frame h.ne _ q'] at hminus
  set e := (starRingEnd ℂ) (pairAxis p q) * (q' - p) with he
  set d := pairHalfDist p q
  rw [sub_self, mul_zero, sub_zero] at hbis hplus hminus
  rw [norm_eq_norm_iff_re_im] at hbis
  rw [norm_le_norm_iff_re_im] at hplus hminus
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero] at hbis hplus hminus
  have hi1 : η * e.im ≤ 0 := by nlinarith
  have hi2 : 0 ≤ η * e.im := by nlinarith
  have him : e.im = 0 := by
    have := le_antisymm hi1 hi2
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hη0.ne'
    · exact h'
  rw [him] at hbis
  have hre : e.re * (e.re - 2 * d) = 0 := by linear_combination -hbis
  have hu := norm_pairAxis h.ne
  have he0 : e ≠ 0 := by
    rw [he]
    exact mul_ne_zero ((map_ne_zero _).2 (pairAxis_ne_zero h.ne)) (sub_ne_zero.2 hne)
  have hre' : e.re = 2 * d := by
    rcases mul_eq_zero.1 hre with h' | h'
    · exact absurd (Complex.ext h' him) he0
    · linarith
  have hq'e := eq_add_mul_conj_mul hu p q'
  rw [← he] at hq'e
  have : e = ((2 * d : ℝ) : ℂ) := Complex.ext (by simp [hre']) (by simp [him])
  rw [hq'e, this, add_pairAxis_mul h.ne]

/-- **Sectors of distinct incidences are disjoint.** -/
theorem disjoint_voronoiSector (hP : IsVoronoiSiteSet P) {p' q' : ℂ}
    (h : IsVoronoiNeighbor P p q) (h' : IsVoronoiNeighbor P p' q') (hne : (p, q) ≠ (p', q')) :
    Disjoint (voronoiSector P p q) (voronoiSector P p' q') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  by_cases hpp : p = p'
  · subst hpp
    have hqq : q ≠ q' := fun e => hne (by rw [e])
    obtain ⟨t, s, ht0, ht1, hs0, hs1, hzt⟩ := exists_of_mem_voronoiSector h hz
    obtain ⟨t', s', ht0', ht1', hs0', hs1', hzt'⟩ := exists_of_mem_voronoiSector h' hz'
    set y := bisectorPoint p q s
    set y' := bisectorPoint p q' s'
    have hy : y ∈ voronoiCell P p := Icc_subset_facetOrdinates hP h ⟨hs0.le, hs1.le⟩
    have hy' : y' ∈ voronoiCell P p := Icc_subset_facetOrdinates hP h' ⟨hs0'.le, hs1'.le⟩
    have hby : ‖y - p‖ = ‖y - q‖ := norm_bisectorPoint_sub_eq h.ne s
    have hby' : ‖y' - p‖ = ‖y' - q'‖ := norm_bisectorPoint_sub_eq h'.ne s'
    have heq : (t : ℂ) * (y - p) = t' * (y' - p) := by
      have := hzt.symm.trans hzt'; linear_combination this
    rcases lt_trichotomy t t' with htt | htt | htt
    · -- `y'` lies strictly inside the segment from `p` to `y`
      have hy'eq : y' = p + ((t / t' : ℝ) : ℂ) * (y - p) := by
        have ht'0 : (t' : ℂ) ≠ 0 := by exact_mod_cast ht0'.ne'
        push_cast
        field_simp
        linear_combination heq.symm
      have := norm_sub_lt_of_mem_segment hy h'.2.1 h'.ne.symm (div_nonneg ht0.le ht0'.le)
        ((div_lt_one ht0').2 htt)
      rw [← hy'eq] at this
      exact absurd hby' this.ne
    · subst htt
      have hyy : y = y' := by
        have ht0c : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
        have := mul_left_cancel₀ ht0c heq
        linear_combination this
      have := eq_of_mem_bisector_of_interior hP h hs0 hs1 h'.2.1 h'.ne.symm (by rw [hyy]; exact hby' : ‖y - p‖ = ‖y - q'‖)
      exact hqq this.symm
    · have hyeq : y = p + ((t' / t : ℝ) : ℂ) * (y' - p) := by
        have ht0c : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
        push_cast
        field_simp
        linear_combination heq
      have := norm_sub_lt_of_mem_segment hy' h.2.1 h.ne.symm (div_nonneg ht0'.le ht0.le)
        ((div_lt_one ht0).2 htt)
      rw [← hyeq] at this
      exact absurd hby this.ne
  · have h1 := norm_sub_lt_of_mem_voronoiSector hP h hz h'.1 (Ne.symm hpp)
    have h2 := norm_sub_lt_of_mem_voronoiSector hP h' hz' h.1 hpp
    linarith

end Disjoint

/-! ### Cones inside a sector -/

section Cones

theorem cos_pos_of_abs_lt {φ : ℝ} (h1 : -(π / 2) < φ) (h2 : φ < π / 2) : 0 < Real.cos φ :=
  Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩

theorem sin_eq_tan_mul_cos {φ : ℝ} (h1 : -(π / 2) < φ) (h2 : φ < π / 2) :
    Real.sin φ = Real.tan φ * Real.cos φ := by
  rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_of_abs_lt h1 h2).ne']

/-- The polar sector of angle `(-α, β)` and radius `≤ d` lies in `modelSector d α β`. -/
theorem polarSector_subset_modelSector {d α β ε : ℝ} (hε : ε ≤ d) (hα : |α| < π / 2)
    (hβ : |β| < π / 2) : polarSector (-α) β ε ⊆ modelSector d α β := by
  intro z hz
  obtain ⟨r, φ, hr0, hr, ha, hb, rfl⟩ := mem_polarSector_iff.1 hz
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  have hφ1 : -(π / 2) < φ := by linarith
  have hφ2 : φ < π / 2 := by linarith
  have hc := cos_pos_of_abs_lt hφ1 hφ2
  have hc1 := Real.cos_le_one φ
  have hs := sin_eq_tan_mul_cos hφ1 hφ2
  have t1 : Real.tan (-α) < Real.tan φ :=
    Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hφ2 ha
  have t2 : Real.tan φ < Real.tan β := Real.tan_lt_tan_of_lt_of_lt_pi_div_two hφ1 hβ2 hb
  rw [Real.tan_neg] at t1
  have hrc : 0 < r * Real.cos φ := mul_pos hr0 hc
  simp only [modelSector, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    sub_zero, mul_zero, mul_one, zero_add, add_zero]
  rw [hs]
  refine ⟨hrc, ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left hc1 hr0.le]
  · linarith [mul_pos hrc (sub_pos.2 t1)]
  · linarith [mul_pos hrc (sub_pos.2 t2)]

/-- The cone at the `β` end `d + i d tan β`. -/
theorem endCone_true_subset_modelSector {d α β ε : ℝ} (hβ : |β| < π / 2)
    (hε : ε ≤ d) (hε' : ε * (1 + |Real.tan α|) ≤ d * (Real.tan α + Real.tan β)) {w : ℂ}
    (hw : w ∈ polarSector β (π / 2) ε) :
    ((d : ℂ) + ((d * Real.tan β : ℝ) : ℂ) * Complex.I) - w ∈ modelSector d α β := by
  obtain ⟨r, φ, hr0, hr, ha, hb, rfl⟩ := mem_polarSector_iff.1 hw
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  have hφ1 : -(π / 2) < φ := by linarith
  have hc := cos_pos_of_abs_lt hφ1 hb
  have hc1 := Real.cos_le_one φ
  have hs1 := Real.sin_le_one φ
  have hs := sin_eq_tan_mul_cos hφ1 hb
  have t2 : Real.tan β < Real.tan φ := Real.tan_lt_tan_of_lt_of_lt_pi_div_two hβ1 hb ha
  have hrc : 0 < r * Real.cos φ := mul_pos hr0 hc
  have hTa : Real.tan α * Real.cos φ ≤ |Real.tan α| := by
    calc Real.tan α * Real.cos φ ≤ |Real.tan α| * Real.cos φ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hc.le
      _ ≤ |Real.tan α| * 1 := mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
      _ = _ := mul_one _
  simp only [modelSector, mem_ofPred_eq, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, sub_zero, mul_zero, mul_one, zero_add, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left hc1 hr0.le]
  · linarith
  · -- `r (sin φ + tan α cos φ) ≤ r (1 + |tan α|) < ε (1 + |tan α|) ≤ d (tan α + tan β)`
    have k1 : r * (Real.sin φ + Real.tan α * Real.cos φ) ≤ r * (1 + |Real.tan α|) :=
      mul_le_mul_of_nonneg_left (by linarith) hr0.le
    have k2 : r * (1 + |Real.tan α|) < ε * (1 + |Real.tan α|) :=
      mul_lt_mul_of_pos_right hr (by positivity)
    linarith
  · rw [hs]
    linarith [mul_pos hrc (sub_pos.2 t2)]

/-- The cone at the `α` end `d - i d tan α`. -/
theorem endCone_false_subset_modelSector {d α β ε : ℝ} (hα : |α| < π / 2)
    (hε : ε ≤ d) (hε' : ε * (1 + |Real.tan β|) ≤ d * (Real.tan α + Real.tan β)) {w : ℂ}
    (hw : w ∈ polarSector (-(π / 2)) (-α) ε) :
    ((d : ℂ) + ((-(d * Real.tan α) : ℝ) : ℂ) * Complex.I) - w ∈ modelSector d α β := by
  obtain ⟨r, φ, hr0, hr, ha, hb, rfl⟩ := mem_polarSector_iff.1 hw
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  have hφ2 : φ < π / 2 := by linarith
  have hc := cos_pos_of_abs_lt ha hφ2
  have hc1 := Real.cos_le_one φ
  have hs1 := Real.neg_one_le_sin φ
  have hs := sin_eq_tan_mul_cos ha hφ2
  have t1 : Real.tan φ < Real.tan (-α) :=
    Real.tan_lt_tan_of_lt_of_lt_pi_div_two ha (by linarith) hb
  rw [Real.tan_neg] at t1
  have hrc : 0 < r * Real.cos φ := mul_pos hr0 hc
  have hTb : Real.tan β * Real.cos φ ≤ |Real.tan β| := by
    calc Real.tan β * Real.cos φ ≤ |Real.tan β| * Real.cos φ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hc.le
      _ ≤ |Real.tan β| * 1 := mul_le_mul_of_nonneg_left hc1 (abs_nonneg _)
      _ = _ := mul_one _
  simp only [modelSector, mem_ofPred_eq, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, sub_zero, mul_zero, mul_one, zero_add, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left hc1 hr0.le]
  · linarith
  · rw [hs]
    linarith [mul_pos hrc (sub_pos.2 t1)]
  · have k1 : r * (Real.tan β * Real.cos φ - Real.sin φ) ≤ r * (1 + |Real.tan β|) :=
      mul_le_mul_of_nonneg_left (by linarith) hr0.le
    have k2 : r * (1 + |Real.tan β|) < ε * (1 + |Real.tan β|) :=
      mul_lt_mul_of_pos_right hr (by positivity)
    linarith

variable {P : Set ℂ} {p q : ℂ}

/-- **Cone at the site.** -/
theorem image_polarSector_subset_voronoiSector {ε : ℝ}
    (hε : ε ≤ pairHalfDist p q) :
    (fun z => p + pairAxis p q * z) '' polarSector (-sectorAlpha P p q) (sectorBeta P p q) ε ⊆
      voronoiSector P p q :=
  image_mono (polarSector_subset_modelSector hε (abs_sectorAlpha_lt P p q)
    (abs_sectorBeta_lt P p q))

theorem tan_sectorAlpha_add_tan_sectorBeta_pos (hP : IsVoronoiSiteSet P)
    (h : IsVoronoiNeighbor P p q) :
    0 < Real.tan (sectorAlpha P p q) + Real.tan (sectorBeta P p q) := by
  rw [tan_sectorAlpha, tan_sectorBeta, neg_div, ← sub_eq_neg_add, ← sub_div]
  exact div_pos (sub_pos.2 (facetLo_lt_facetHi hP h)) (pairHalfDist_pos h.ne)

/-- **Cones at the facet ends.** Near its end `b`, the sector of `(p, q)` contains a polar sector of
angle `sectorBaseAngle P p q b` with apex at that end (rotated by `-pairAxis p q`). -/
theorem exists_endCone_subset_voronoiSector (hP : IsVoronoiSiteSet P)
    (h : IsVoronoiNeighbor P p q) (b : Bool) :
    ∃ ε > 0, ∀ ε' ≤ ε, (fun z => facetEnd P p q b + (-pairAxis p q) * z) ''
      polarSector (endConeLo P p q b) (endConeHi P p q b) ε' ⊆ voronoiSector P p q := by
  have hd := pairHalfDist_pos h.ne
  have hT := tan_sectorAlpha_add_tan_sectorBeta_pos hP h
  set d := pairHalfDist p q with hd'
  set Ta := Real.tan (sectorAlpha P p q) with hTa
  set Tb := Real.tan (sectorBeta P p q) with hTb
  have hfe : ∀ c : Bool, ∀ v : ℂ, facetEnd P p q c = p + pairAxis p q * v →
      ∀ w, facetEnd P p q c + (-pairAxis p q) * w = p + pairAxis p q * (v - w) := by
    intro c v hv w; rw [hv]; ring
  cases b
  · set ε := min d (d * (Ta + Tb) / (1 + |Tb|)) with hε
    have hε0 : 0 < ε := lt_min hd (by positivity)
    refine ⟨ε, hε0, fun ε' hε' => ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    show facetEnd P p q false + -pairAxis p q * w ∈ _
    have hv : facetEnd P p q false =
        p + pairAxis p q * ((d : ℂ) + ((-(d * Ta) : ℝ) : ℂ) * Complex.I) := by
      simp only [facetEnd, bisectorPoint, hTa, tan_sectorAlpha, ← hd']
      congr 3
      field_simp
    rw [hfe false _ hv w]
    refine mem_image_of_mem _ (endCone_false_subset_modelSector (abs_sectorAlpha_lt P p q)
      ((hε'.trans (min_le_left _ _))) ?_ hw)
    have := hε'.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg Tb]
  · set ε := min d (d * (Ta + Tb) / (1 + |Ta|)) with hε
    have hε0 : 0 < ε := lt_min hd (by positivity)
    refine ⟨ε, hε0, fun ε' hε' => ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    show facetEnd P p q true + -pairAxis p q * w ∈ _
    have hv : facetEnd P p q true =
        p + pairAxis p q * ((d : ℂ) + ((d * Tb : ℝ) : ℂ) * Complex.I) := by
      simp only [facetEnd, bisectorPoint, hTb, tan_sectorBeta, ← hd']
      congr 3
      field_simp
    rw [hfe true _ hv w]
    refine mem_image_of_mem _ (endCone_true_subset_modelSector (abs_sectorBeta_lt P p q)
      ((hε'.trans (min_le_left _ _))) ?_ hw)
    have := hε'.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [abs_nonneg Ta]

end Cones

end SandierSerfaty

end
