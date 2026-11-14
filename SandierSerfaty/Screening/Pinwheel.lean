/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ChartBox
public import SandierSerfaty.Screening.Depth
public import Mathlib.Analysis.Complex.Isometry

/-!
# The pinwheel frame (screening note Def 4.13, Lemma 4.14, carry cells of Lemma 4.20)

The screening note, Definition 4.13 (`def:pinwheel`) and Lemma 4.14
(`lem:pinwheel`), with a corrected orientation of the frames and a corrected disjointness condition for the carry cells.

For the square `Q = sq c t` and the cut depth `d`, put `a□ = t/2 - d - 8` (`Pinwheel.offset`),
`L = t - d - 8` (`Pinwheel.side`), `w_f = d + 8`, `ω = -i`, and for `j ∈ Fin 4`
`Ψ_j(u, v) = c + ω^j ((u - a□) + i(t/2 - v))` — an orientation-**reversing** isometry —
and `R_j = Ψ_j([0, L] × [0, w_f])` (`Pinwheel.rect c t d j`, a `Rect` with frame `w ↦ ω^j w̄`).

* `Pinwheel.chart_rect`, `Pinwheel.coords_rect`: the chart and its inverse, with
  `ζ_j(x) = i^j (x - c)` (`Pinwheel.rot`): `Ψ_j⁻¹(x) = (Re ζ_j + a□, t/2 - Im ζ_j)`;
* Lemma 4.14(a): `Pinwheel.mem_rect_iff` (`R_0 = c + [-a□, t/2] × [a□, t/2]`, `R_{j+1} = c + ω(R_j - c)`),
  `Pinwheel.iUnion_rect` (`⋃ R_j = F = {0 ≤ δ ≤ d + 8}`), `Pinwheel.aedisjoint_rect` (disjoint
  interiors: the pairwise intersections are null);
* Lemma 4.14(b): `Pinwheel.sqDepth_chart`: `δ(Ψ_j(u, v)) = min(v, L - u)` on `[0, L] × [0, w_f]`;
* Lemma 4.14(c): the region inclusions follow from (b);
* Lemma 4.14(d) and the carry cells of Lemma 4.20: `Pinwheel.chart_rect_succ`
  (`Ψ_j(L - v, w_f + u) = Ψ_{j+1}(u, v)`), the carry rectangle
  `Pinwheel.carryRect c t d j w' = Ψ_{j+1}([-1, 1] × [0, w'])` with its `s`-axis along the common
  segment, `Pinwheel.carryRect_carrier` (`H^c_j = A_j ∪ A'_j`), `Pinwheel.carryRect_chart_mem_carryA`,
  `Pinwheel.carryRect_chart_mem_carryA'` (in carry coordinates `A_j = {r ≤ 1}`, `A'_j = {r ≥ 1}`),
  `Pinwheel.sqDepth_le_of_mem_carryRect` (`δ ≤ w'` on `H^c_j`), and the corrected disjointness
  `Pinwheel.disjoint_carryRect` (`w'_j < d + 7` for all `j`, `a□ > 0`).
-/

open MeasureTheory Set Complex
open scoped ENNReal ComplexConjugate

public section

namespace SandierSerfaty.Screening.Pinwheel

/-- `a□ = t/2 - d - 8`. -/
@[expose] noncomputable def offset (t d : ℝ) : ℝ := t / 2 - d - 8

/-- `L = t - d - 8`. -/
@[expose] noncomputable def side (t d : ℝ) : ℝ := t - d - 8

/-- `ω = -i` as an element of the unit circle. -/
@[expose] noncomputable def omega : Circle := ⟨-I, by simp [Submonoid.unitSphere]⟩

theorem coe_omega_pow (n : ℕ) : ((omega ^ n : Circle) : ℂ) = (-I) ^ n := by
  rw [Circle.coe_pow]; rfl

/-- The frame `M_j w = ω^j w̄` of `R_j` (orientation-reversing). -/
@[expose] noncomputable def frame (j : Fin 4) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  conjLIE.trans (rotation (omega ^ (j : ℕ)))

theorem frame_apply (j : Fin 4) (w : ℂ) : frame j w = (-I) ^ (j : ℕ) * conj w := by
  simp only [frame, LinearIsometryEquiv.trans_apply, conjLIE_apply, rotation_apply, coe_omega_pow]

/-- The rectangle `R_j = Ψ_j([0, L] × [0, d + 8])` of the pinwheel, with chart
`Ψ_j(u, v) = c + ω^j ((u - a□) + i(t/2 - v))`. -/
@[expose] noncomputable def rect (c : ℂ) (t d : ℝ) (j : Fin 4) : Rect :=
  ⟨c + (-I) ^ (j : ℕ) * ⟨-offset t d, t / 2⟩, frame j, side t d, d + 8⟩

/-- `ζ_j(x) = i^j (x - c)`, the point `x` rotated back into the position of `R_0`. -/
@[expose] noncomputable def rot (c : ℂ) (j : Fin 4) (x : ℂ) : ℂ := I ^ (j : ℕ) * (x - c)

variable {c : ℂ} {t d : ℝ} {j : Fin 4}

@[simp] theorem rect_width : (rect c t d j).width = side t d := rfl

@[simp] theorem rect_height : (rect c t d j).height = d + 8 := rfl

theorem negI_pow_mul_I_pow (n : ℕ) : (-I : ℂ) ^ n * I ^ n = 1 := by
  rw [← mul_pow]; simp

theorem negI_pow_succ (j : Fin 4) : (-I : ℂ) ^ ((j + 1 : Fin 4) : ℕ) = (-I) ^ (j : ℕ) * (-I) := by
  fin_cases j <;> simp [pow_succ]

/-- `Ψ_j(u, v) = c + ω^j ((u - a□) + i(t/2 - v))`. -/
theorem chart_rect (w : ℂ) :
    (rect c t d j).chart w = c + (-I) ^ (j : ℕ) * ⟨w.re - offset t d, t / 2 - w.im⟩ := by
  simp only [Rect.chart, rect, frame_apply]
  have : (⟨-offset t d, t / 2⟩ : ℂ) + conj w = ⟨w.re - offset t d, t / 2 - w.im⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [add_assoc, ← mul_add, this]

/-- `Ψ_j⁻¹(x) = (Re ζ_j(x) + a□, t/2 - Im ζ_j(x))`. -/
theorem coords_rect (x : ℂ) :
    (rect c t d j).coords x = ⟨(rot c j x).re + offset t d, t / 2 - (rot c j x).im⟩ := by
  apply (rect c t d j).chartHomeomorph.injective
  rw [Rect.coe_chartHomeomorph, Rect.chart_coords, chart_rect]
  simp only [add_sub_cancel_right, sub_sub_cancel]
  have : (⟨(rot c j x).re, (rot c j x).im⟩ : ℂ) = rot c j x := Complex.eta _
  rw [this, rot, ← mul_assoc, negI_pow_mul_I_pow, one_mul, add_sub_cancel]

theorem mem_rect_box_iff {I J : Set ℝ} {x : ℂ} :
    x ∈ (rect c t d j).box I J ↔
      (rot c j x).re + offset t d ∈ I ∧ t / 2 - (rot c j x).im ∈ J := by
  rw [Rect.mem_box, coords_rect]

/-- **Lemma 4.14(a)**: `R_j = {x : Re ζ_j(x) ∈ [-a□, t/2], Im ζ_j(x) ∈ [a□, t/2]}`; for `j = 0`,
`R_0 = c + [-a□, t/2] × [a□, t/2]`. -/
theorem mem_rect_iff {x : ℂ} :
    x ∈ (rect c t d j).carrier ↔
      (rot c j x).re ∈ Icc (-offset t d) (t / 2) ∧ (rot c j x).im ∈ Icc (offset t d) (t / 2) := by
  rw [Rect.carrier_eq_box, mem_rect_box_iff]
  simp only [rect_width, rect_height, mem_Icc, side, offset]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The real and imaginary parts of `ζ_j = i^j z` (`z = x - c`): `(Re z, Im z)`, `(-Im z, Re z)`,
`(-Re z, -Im z)`, `(Im z, -Re z)`. -/
theorem rot_re_im (j : Fin 4) (x : ℂ) :
    ((rot c j x).re, (rot c j x).im) =
      match j with
      | 0 => ((x - c).re, (x - c).im)
      | 1 => (-(x - c).im, (x - c).re)
      | 2 => (-(x - c).re, -(x - c).im)
      | 3 => ((x - c).im, -(x - c).re) := by
  fin_cases j <;> simp [rot, pow_succ]

/-- The sup norm `|·|_∞` is invariant under the rotation by `ω^n`. -/
theorem max_abs_negI_pow_mul (n : ℕ) (z : ℂ) :
    max |((-I) ^ n * z).re| |((-I) ^ n * z).im| = max |z.re| |z.im| := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, ih]
    simp only [neg_mul, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im, zero_mul, one_mul, zero_sub, zero_add, abs_neg, neg_neg]
    rw [max_comm]

/-- **Lemma 4.14(b)**: `δ(Ψ_j(u, v)) = min(v, L - u)` on `[0, L] × [0, w_f]` (for `a□ ≥ 0`). -/
theorem sqDepth_chart (ha : 0 ≤ offset t d) {w : ℂ} (hw : w ∈ (rect c t d j).std) :
    sqDepth c t ((rect c t d j).chart w) = min w.im (side t d - w.re) := by
  obtain ⟨⟨hu0, huL⟩, hv0, hvw⟩ := hw
  simp only [rect_width, rect_height] at huL hvw
  rw [sqDepth, chart_rect, add_sub_cancel_left, max_abs_negI_pow_mul]
  simp only
  have hv : |t / 2 - w.im| = t / 2 - w.im := abs_of_nonneg (by unfold offset at ha; linarith)
  rw [hv]
  unfold side
  unfold offset at ha ⊢
  rcases le_total w.re (t / 2 - d - 8) with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), min_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith)]
    rcases le_total (w.re - (t / 2 - d - 8)) (t / 2 - w.im) with h' | h'
    · rw [max_eq_right h', min_eq_left (by linarith)]; ring
    · rw [max_eq_left h', min_eq_right (by linarith)]; ring

/-- The points of `R_j` lie in `Q`, at depth `≤ w_f`. -/
theorem sqDepth_mem_Icc_of_mem_rect (ha : 0 ≤ offset t d) {x : ℂ} (hx : x ∈ (rect c t d j).carrier) :
    sqDepth c t x ∈ Icc 0 (d + 8) := by
  have hx' := (rect c t d j).chart_coords x
  rw [← hx', sqDepth_chart ha hx]
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  simp only [rect_width, rect_height] at h2 h4
  exact ⟨le_min h3 (by linarith), (min_le_left _ _).trans h4⟩

/-! ### The frame `F` and the partition into the `R_j` -/

/-- The frame `F = Q ∩ {δ ≤ d + 8} = {0 ≤ δ ≤ d + 8}`. -/
@[expose] def frameSet (c : ℂ) (t d : ℝ) : Set ℂ := {x | 0 ≤ sqDepth c t x ∧ sqDepth c t x ≤ d + 8}

/-- **Lemma 4.14(a)**: the four rectangles cover the frame, `⋃ R_j = F`. -/
theorem iUnion_rect (ha : 0 ≤ offset t d) :
    ⋃ j, (rect c t d j).carrier = frameSet c t d := by
  ext x
  simp only [mem_iUnion, frameSet, mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact sqDepth_mem_Icc_of_mem_rect ha hj
  · rintro ⟨h0, h1⟩
    rw [sqDepth] at h0 h1
    set X := (x - c).re
    set Y := (x - c).im
    have hX : |X| ≤ t / 2 := by have := le_max_left |X| |Y|; linarith
    have hY : |Y| ≤ t / 2 := by have := le_max_right |X| |Y|; linarith
    have hM : offset t d ≤ max |X| |Y| := by unfold offset; linarith
    obtain ⟨hX1, hX2⟩ := abs_le.1 hX
    obtain ⟨hY1, hY2⟩ := abs_le.1 hY
    have hr : ∀ j : Fin 4, x ∈ (rect c t d j).carrier ↔ _ := fun j => mem_rect_iff (j := j)
    -- the four cases of the screening note
    by_cases hA : offset t d ≤ Y ∧ -offset t d ≤ X
    · refine ⟨0, (hr 0).2 ?_⟩
      have := rot_re_im (c := c) 0 x
      simp only [Prod.mk.injEq] at this
      rw [this.1, this.2]
      exact ⟨⟨hA.2, hX2⟩, hA.1, hY2⟩
    by_cases hB : offset t d ≤ X ∧ Y ≤ offset t d
    · refine ⟨1, (hr 1).2 ?_⟩
      have := rot_re_im (c := c) 1 x
      simp only [Prod.mk.injEq] at this
      rw [this.1, this.2]
      exact ⟨⟨by linarith [hB.2], by linarith⟩, hB.1, hX2⟩
    by_cases hC : Y ≤ -offset t d ∧ X ≤ offset t d
    · refine ⟨2, (hr 2).2 ?_⟩
      have := rot_re_im (c := c) 2 x
      simp only [Prod.mk.injEq] at this
      rw [this.1, this.2]
      exact ⟨⟨by linarith [hC.2], by linarith⟩, by linarith [hC.1], by linarith⟩
    · refine ⟨3, (hr 3).2 ?_⟩
      have := rot_re_im (c := c) 3 x
      simp only [Prod.mk.injEq] at this
      rw [this.1, this.2]
      rcases le_max_iff.1 hM with hM | hM
      · rcases abs_cases X with ⟨hXa, _⟩ | ⟨hXa, _⟩
        · rw [hXa] at hM
          by_cases hYa : offset t d ≤ Y
          · exact absurd ⟨hYa, by linarith⟩ hA
          · exact absurd ⟨hM, by linarith⟩ hB
        · rw [hXa] at hM
          by_cases hYa : -offset t d ≤ Y
          · exact ⟨⟨hYa, hY2⟩, by linarith, by linarith⟩
          · exact absurd ⟨by linarith, by linarith⟩ hC
      · rcases abs_cases Y with ⟨hYa, _⟩ | ⟨hYa, _⟩
        · rw [hYa] at hM
          by_cases hXa : -offset t d ≤ X
          · exact absurd ⟨hM, hXa⟩ hA
          · exact ⟨⟨by linarith, hY2⟩, by linarith, by linarith⟩
        · rw [hYa] at hM
          by_cases hXa : X ≤ offset t d
          · exact absurd ⟨by linarith, hXa⟩ hC
          · exact absurd ⟨by linarith, by linarith⟩ hB

/-- The four lines `Re(x - c) = ±a□`, `Im(x - c) = ±a□` that carry the pairwise intersections. -/
@[expose] def junctionLines (c : ℂ) (a : ℝ) : Set ℂ :=
  {x | (x - c).re = a} ∪ {x | (x - c).re = -a} ∪ {x | (x - c).im = a} ∪ {x | (x - c).im = -a}

theorem volume_re_eq (c : ℂ) (r : ℝ) : volume {x : ℂ | (x - c).re = r} = 0 := by
  have : {x : ℂ | (x - c).re = r} = {r + c.re} ×ℂ univ := by
    ext x; simp [Complex.mem_reProdIm, sub_eq_iff_eq_add]
  rw [this, volume_reProdIm, Real.volume_singleton, zero_mul]

theorem volume_im_eq (c : ℂ) (r : ℝ) : volume {x : ℂ | (x - c).im = r} = 0 := by
  have : {x : ℂ | (x - c).im = r} = univ ×ℂ {r + c.im} := by
    ext x; simp [Complex.mem_reProdIm, sub_eq_iff_eq_add]
  rw [this, volume_reProdIm, Real.volume_singleton, mul_zero]

theorem volume_junctionLines (c : ℂ) (a : ℝ) : volume (junctionLines c a) = 0 := by
  refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
  · exact volume_re_eq c a
  · exact volume_re_eq c (-a)
  · exact volume_im_eq c a
  · exact volume_im_eq c (-a)

theorem rect_inter_subset (ha : 0 < offset t d) {i j : Fin 4} (hij : i ≠ j) :
    (rect c t d i).carrier ∩ (rect c t d j).carrier ⊆ junctionLines c (offset t d) := by
  rintro x ⟨hi, hj⟩
  rw [mem_rect_iff] at hi hj
  have ri := rot_re_im (c := c) i x
  have rj := rot_re_im (c := c) j x
  simp only [junctionLines, mem_union, mem_ofPred_eq]
  fin_cases i <;> fin_cases j <;> simp only [Prod.mk.injEq] at ri rj <;>
    simp only [ri, rj, mem_Icc] at hi hj <;> first
      | exact absurd rfl hij
      | (left; left; left; linarith)
      | (left; left; right; linarith)
      | (left; right; linarith)
      | (right; linarith)

/-- **Lemma 4.14(a)**: the `R_j` have disjoint interiors (null pairwise intersections). -/
theorem aedisjoint_rect (ha : 0 < offset t d) :
    Pairwise fun i j => AEDisjoint volume (rect c t d i).carrier (rect c t d j).carrier :=
  fun _ _ hij => measure_mono_null (rect_inter_subset ha hij) (volume_junctionLines c _)

/-- `∫_F g = ∑_j ∫_{R_j} g`. -/
theorem integral_frameSet_eq_sum (ha : 0 < offset t d) {g : ℂ → ℝ}
    (hg : IntegrableOn g (frameSet c t d)) :
    ∫ x in frameSet c t d, g x = ∑ j : Fin 4, ∫ x in (rect c t d j).carrier, g x := by
  rw [← iUnion_rect ha.le] at hg ⊢
  rw [integral_iUnion_ae (fun j => (rect c t d j).measurableSet_carrier.nullMeasurableSet)
    (aedisjoint_rect ha) hg, tsum_fintype]

/-! ### Consecutive charts and the carry cells (Lemma 4.14(d), Lemma 4.20) -/

/-- `Ψ_j(L - v, w_f + u) = Ψ_{j+1}(u, v)` (indices mod 4). -/
theorem chart_rect_succ (w : ℂ) :
    (rect c t d j).chart ⟨side t d - w.im, d + 8 + w.re⟩ = (rect c t d (j + 1)).chart w := by
  rw [chart_rect, chart_rect, negI_pow_succ, mul_assoc]
  congr 2
  apply Complex.ext <;> simp [side, offset] <;> ring

/-- `Ψ_j⁻¹(x) = (L - v, w_f + u)` for `(u, v) = Ψ_{j+1}⁻¹(x)`. -/
theorem coords_rect_succ (x : ℂ) :
    (rect c t d j).coords x =
      ⟨side t d - ((rect c t d (j + 1)).coords x).im, d + 8 + ((rect c t d (j + 1)).coords x).re⟩ := by
  apply (rect c t d j).chartHomeomorph.injective
  rw [Rect.coe_chartHomeomorph, Rect.chart_coords, chart_rect_succ, Rect.chart_coords]

/-- `i` as an element of the unit circle. -/
@[expose] noncomputable def iCircle : Circle := ⟨I, by simp [Submonoid.unitSphere]⟩

theorem coe_iCircle : ((iCircle : Circle) : ℂ) = I := rfl

/-- The swap `s + i r ↦ r + i s` (`w ↦ i w̄`). -/
@[expose] noncomputable def swapLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  conjLIE.trans (rotation iCircle)

theorem swapLIE_apply (w : ℂ) : swapLIE w = ⟨w.im, w.re⟩ := by
  simp only [swapLIE, LinearIsometryEquiv.trans_apply, conjLIE_apply, rotation_apply, coe_iCircle]
  apply Complex.ext <;> simp

/-- The **carry cell** `H^c_j = Ψ_{j+1}([-1, 1] × [0, w'])`, a `w' × 2` rectangle whose `s`-axis runs
along the common segment `Ψ_{j+1}({0} × [0, w'])` and whose `r`-axis crosses it (screening note, Lemma 4.20). -/
@[expose] noncomputable def carryRect (c : ℂ) (t d : ℝ) (j : Fin 4) (w' : ℝ) : Rect :=
  ⟨(rect c t d (j + 1)).chart ⟨-1, 0⟩, swapLIE.trans (rect c t d (j + 1)).frame, w', 2⟩

variable {w' : ℝ}

@[simp] theorem carryRect_width : (carryRect c t d j w').width = w' := rfl

@[simp] theorem carryRect_height : (carryRect c t d j w').height = 2 := rfl

/-- In carry coordinates `(s, r)`: `Ψ^c(s, r) = Ψ_{j+1}(r - 1, s)`. -/
theorem carryRect_chart (z : ℂ) :
    (carryRect c t d j w').chart z = (rect c t d (j + 1)).chart ⟨z.im - 1, z.re⟩ := by
  simp only [Rect.chart, carryRect, LinearIsometryEquiv.trans_apply, swapLIE_apply]
  rw [add_assoc, ← map_add]
  congr 2
  apply Complex.ext <;> simp [add_comm, sub_eq_add_neg]

theorem carryRect_coords (x : ℂ) :
    (carryRect c t d j w').coords x =
      ⟨((rect c t d (j + 1)).coords x).im, ((rect c t d (j + 1)).coords x).re + 1⟩ := by
  apply (carryRect c t d j w').chartHomeomorph.injective
  rw [Rect.coe_chartHomeomorph, Rect.chart_coords, carryRect_chart]
  simp only [add_sub_cancel_right, Complex.eta, Rect.chart_coords]

/-- `H^c_j = Ψ_{j+1}([-1, 1] × [0, w'])`. -/
theorem mem_carryRect_iff {x : ℂ} :
    x ∈ (carryRect c t d j w').carrier ↔
      ((rect c t d (j + 1)).coords x).re ∈ Icc (-1) 1 ∧
        ((rect c t d (j + 1)).coords x).im ∈ Icc 0 w' := by
  rw [Rect.carrier, mem_preimage, Rect.std, Complex.mem_reProdIm, carryRect_coords]
  simp only [carryRect_width, carryRect_height, mem_Icc]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The negative carry region `A_j = Ψ_j([L - w', L] × [w_f - 1, w_f])` (top of the last column of
`R_j`). -/
@[expose] def carryA (c : ℂ) (t d : ℝ) (j : Fin 4) (w' : ℝ) : Set ℂ :=
  (rect c t d j).box (Icc (side t d - w') (side t d)) (Icc (d + 7) (d + 8))

/-- The positive carry region `A'_j = Ψ_{j+1}([0, 1] × [0, w'])` (bottom of the first column of
`R_{j+1}`). -/
@[expose] def carryA' (c : ℂ) (t d : ℝ) (j : Fin 4) (w' : ℝ) : Set ℂ :=
  (rect c t d (j + 1)).box (Icc 0 1) (Icc 0 w')

theorem mem_carryA_iff {x : ℂ} :
    x ∈ carryA c t d j w' ↔
      ((rect c t d (j + 1)).coords x).re ∈ Icc (-1) 0 ∧
        ((rect c t d (j + 1)).coords x).im ∈ Icc 0 w' := by
  rw [carryA, Rect.mem_box, coords_rect_succ]
  simp only [mem_Icc]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **Lemma 4.14(d)**: `H^c_j = A_j ∪ A'_j`, bisected by the common segment. -/
theorem carryRect_carrier : (carryRect c t d j w').carrier = carryA c t d j w' ∪ carryA' c t d j w' := by
  ext x
  rw [mem_union, mem_carryRect_iff, mem_carryA_iff, carryA', Rect.mem_box]
  simp only [mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rcases le_total ((rect c t d (j + 1)).coords x).re 0 with h | h
    · exact Or.inl ⟨⟨h1, h⟩, h3, h4⟩
    · exact Or.inr ⟨⟨h, h2⟩, h3, h4⟩
  · rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩)
    · exact ⟨⟨h1, by linarith⟩, h3, h4⟩
    · exact ⟨⟨by linarith, h2⟩, h3, h4⟩

/-- In carry coordinates, `A_j = {0 ≤ r ≤ 1}`. -/
theorem carryRect_chart_mem_carryA {z : ℂ} (hs : z.re ∈ Icc 0 w') :
    (carryRect c t d j w').chart z ∈ carryA c t d j w' ↔ z.im ∈ Icc 0 1 := by
  rw [mem_carryA_iff, carryRect_chart, Rect.coords_chart]
  simp only [mem_Icc, hs.1, hs.2, and_self, and_true]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- In carry coordinates, `A'_j = {1 ≤ r ≤ 2}`. -/
theorem carryRect_chart_mem_carryA' {z : ℂ} (hs : z.re ∈ Icc 0 w') :
    (carryRect c t d j w').chart z ∈ carryA' c t d j w' ↔ z.im ∈ Icc 1 2 := by
  rw [carryA', carryRect_chart, Rect.chart_mem_box]
  simp only [mem_Icc, hs.1, hs.2, and_self, and_true]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem carryA_subset_rect (hwL : w' ≤ side t d) (hd : -7 ≤ d) :
    carryA c t d j w' ⊆ (rect c t d j).carrier := by
  rw [Rect.carrier_eq_box, carryA]
  refine Rect.box_mono (Icc_subset_Icc (by linarith) le_rfl) (Icc_subset_Icc (by linarith) ?_)
  simp

theorem carryA'_subset_rect (hw0 : 1 ≤ side t d) (hwd : w' ≤ d + 8) :
    carryA' c t d j w' ⊆ (rect c t d (j + 1)).carrier := by
  rw [Rect.carrier_eq_box, carryA']
  exact Rect.box_mono (Icc_subset_Icc le_rfl (by simpa using hw0))
    (Icc_subset_Icc le_rfl (by simpa using hwd))

theorem volume_carryA : volume (carryA c t d j w') = ENNReal.ofReal w' := by
  rw [carryA, Rect.volume_box_Icc]; norm_num

theorem volume_carryA' : volume (carryA' c t d j w') = ENNReal.ofReal w' := by
  rw [carryA', Rect.volume_box_Icc]; simp

/-- **Lemma 4.20 (location)**: `H^c_j ⊆ {0 ≤ δ ≤ w'}` (for `0 ≤ w' ≤ min(L, d + 8)`, `a□ ≥ 0`). -/
theorem sqDepth_mem_of_mem_carryRect (ha : 0 ≤ offset t d) (hwL : w' ≤ side t d)
    (hwd : w' ≤ d + 8) (hL : 1 ≤ side t d) (hd : -7 ≤ d) {x : ℂ}
    (hx : x ∈ (carryRect c t d j w').carrier) : sqDepth c t x ∈ Icc 0 w' := by
  rw [carryRect_carrier] at hx
  rcases hx with hx | hx
  · have hx' := hx
    rw [carryA, Rect.mem_box] at hx'
    have hR := carryA_subset_rect hwL hd hx
    have := sqDepth_mem_Icc_of_mem_rect ha hR
    rw [← (rect c t d j).chart_coords x, sqDepth_chart ha hR] at this ⊢
    refine ⟨this.1, (min_le_right _ _).trans (by linarith [hx'.1.1])⟩
  · have hx' := hx
    rw [carryA', Rect.mem_box] at hx'
    have hR := carryA'_subset_rect hL hwd hx
    have := sqDepth_mem_Icc_of_mem_rect ha hR
    rw [← (rect c t d (j + 1)).chart_coords x, sqDepth_chart ha hR] at this ⊢
    exact ⟨this.1, (min_le_left _ _).trans hx'.2.2⟩

/-- `H^c_j` in absolute coordinates: `Re ζ_{j+1} ∈ [-a□ - 1, -a□ + 1]`, `Im ζ_{j+1} ∈ [t/2 - w', t/2]`
(for `j = 0`: `H^c_0 ⊆ c + [t/2 - w', t/2] × [a□ - 1, a□ + 1]`, as in the corrected disjointness condition). -/
theorem mem_carryRect_iff_rot {x : ℂ} :
    x ∈ (carryRect c t d j w').carrier ↔
      (rot c (j + 1) x).re ∈ Icc (-offset t d - 1) (-offset t d + 1) ∧
        (rot c (j + 1) x).im ∈ Icc (t / 2 - w') (t / 2) := by
  rw [mem_carryRect_iff, coords_rect]
  simp only [mem_Icc]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **Disjointness of the carry cells** (screening note, Lemma 4.20): the carry cells are pairwise disjoint when
`w'_j < d + 7` for all `j` (i.e. `d + 8 > w'_j + 1`; in the screening note `w'_j < 3ℓc`, `d ≥ 8ℓc`) and
`a□ > 0`. -/
theorem disjoint_carryRect (ha : 0 < offset t d) {w : Fin 4 → ℝ} (hw : ∀ j, w j < d + 7)
    {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (carryRect c t d i (w i)).carrier (carryRect c t d j (w j)).carrier := by
  rw [Set.disjoint_left]
  intro x hi hj
  rw [mem_carryRect_iff_rot] at hi hj
  obtain ⟨⟨hi1, hi2⟩, hi3, hi4⟩ := hi
  obtain ⟨⟨hj1, hj2⟩, hj3, hj4⟩ := hj
  have hwi := hw i
  have hwj := hw j
  unfold offset at ha hi1 hi2 hj1 hj2
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | (simp [rot, pow_succ] at hi1 hi2 hi3 hi4 hj1 hj2 hj3 hj4 hwi hwj; linarith)

end SandierSerfaty.Screening.Pinwheel

end
