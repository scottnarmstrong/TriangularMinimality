/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Pinwheel

/-!
# Regions of the pinwheel (screening note, Lemma 4.14(c), and the geometry in Lemma 4.17)

The screening note, Lemma 4.14(c) (`lem:pinwheel`) and the proof of Lemma 4.17
(`lem:strip`), in the coordinates `(u, v)` of `R_j = Ψ_j([0, L] × [0, w_f])`, where the depth is
`δ = min(v, L - u)` (Lemma 4.14(b), `Pinwheel.sqDepth_chart`):

* `Pinwheel.mem_top_of_lt_sqDepth`: `(A ∪ Ω₊) ∩ R_j ⊆ T^{(j)} = Ψ_j([0, L] × [d - 1, w_f])`
  (both lie in `{δ > d - 1}`);
* `Pinwheel.sqDepth_mem_of_mem_bottom`: `Ψ_j([0, L] × [0, d - 1]) ⊆ O_- = Q ∩ {δ ≤ d - 1}`;
-/

open MeasureTheory Set

public section

namespace SandierSerfaty.Screening.Pinwheel

variable {c : ℂ} {t d : ℝ} {j : Fin 4}

/-- The depth of a point of `R_j` in the coordinates of `R_j`. -/
theorem sqDepth_eq_of_mem_rect (ha : 0 ≤ offset t d) {x : ℂ} (hx : x ∈ (rect c t d j).carrier) :
    sqDepth c t x = min ((rect c t d j).coords x).im (side t d - ((rect c t d j).coords x).re) := by
  have := sqDepth_chart (c := c) (j := j) ha hx
  rwa [Rect.chart_coords] at this

/-- **Lemma 4.14(c)**: `(A ∪ Ω₊) ∩ R_j ⊆ T^{(j)}`: points of `R_j` with `δ > d - 1` lie in the top zone. -/
theorem mem_top_of_lt_sqDepth (ha : 0 ≤ offset t d) {x : ℂ} (hx : x ∈ (rect c t d j).carrier)
    (hδ : d - 1 < sqDepth c t x) :
    x ∈ (rect c t d j).box (Icc 0 (side t d)) (Icc (d - 1) (d + 8)) := by
  rw [sqDepth_eq_of_mem_rect ha hx, lt_min_iff] at hδ
  obtain ⟨⟨h1, h2⟩, _, h4⟩ := hx
  exact ⟨⟨h1, h2⟩, hδ.1.le, h4⟩

/-- **Lemma 4.14(c)**: the bottom part `Ψ_j([0, L] × [0, d - 1])` lies in `O_- = Q ∩ {δ ≤ d - 1}`. -/
theorem sqDepth_mem_of_mem_bottom (ha : 0 ≤ offset t d) {x : ℂ}
    (hx : x ∈ (rect c t d j).box (Icc 0 (side t d)) (Icc 0 (d - 1))) :
    sqDepth c t x ∈ Icc 0 (d - 1) := by
  have hxR : x ∈ (rect c t d j).carrier :=
    Rect.box_mono subset_rfl (Icc_subset_Icc le_rfl (by simp only [rect_height]; linarith)) hx
  refine ⟨(sqDepth_mem_Icc_of_mem_rect ha hxR).1, ?_⟩
  rw [sqDepth_eq_of_mem_rect ha hxR]
  exact (min_le_left _ _).trans hx.2.2

end SandierSerfaty.Screening.Pinwheel

end
