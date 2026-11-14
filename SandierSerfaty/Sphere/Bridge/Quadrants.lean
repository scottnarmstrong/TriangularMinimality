/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.Transport
public import SandierSerfaty.Sphere.Lower.Reflection
public import SandierSerfaty.Screening.SquareCell
public import Mathlib.Analysis.Convex.Measure

/-!
# The four reflected, rescaled copies of a square

For `Q = a₀ + [0, t]²`, `σ > 0`, `b = σ a₀` and `s = σ t`, the `e`-th copy (`e : Fin 4`) of `σ Q` reflected
evenly through the corner `b` is the image of `Q` under the similarity `quadMap σ a₀ e y = b + L_e (σ (y - a₀))`,
`L_e ∈ {id, flipRe, flipIm, -id}` (`Bridge.quadL`), and `quadMap σ a₀ e (Y i)` is the reflected point
`reflectPts b (σ Y) (e, i)` of Definition 6.1 (`Bridge.reflectPts_eq_quadMap`).

* `Bridge.quadClosed b s e`, `Bridge.quadOpen b s e`: the closed and open quadrants, described by signs;
  `Bridge.image_quadMap_sqAt`, `Bridge.image_quadMap_interior`: they are the images of `Q` and `Q°`;
* `Bridge.disjoint_quadOpen_quadClosed`: an open quadrant misses the other closed quadrants;
* `Bridge.quadClosed_subset_sq`, `Bridge.quadOpen_subset_interior_sq`: all lie in `sq b (2 s)`;
* `Bridge.ae_exists_mem_quadOpen`: a.e. point of `sq b (2 s)` lies in an open quadrant.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open Lower

theorem sqAt_eq_sq (a₀ : ℂ) (t : ℝ) : sqAt a₀ t = sq (a₀ + ⟨t / 2, t / 2⟩) t := by
  ext x
  simp only [sqAt, sq, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc, Complex.add_re, Complex.add_im]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

theorem interior_sqAt_ae_eq (a₀ : ℂ) (t : ℝ) : interior (sqAt a₀ t) =ᵐ[volume] sqAt a₀ t := by
  rw [sqAt_eq_sq]
  exact interior_ae_eq_of_null_frontier (Convex.addHaar_frontier volume (Screening.convex_sq _ _))

theorem sgnRe_mul_self (e : Fin 4) : sgnRe e * sgnRe e = 1 := by
  fin_cases e <;> simp [sgnRe]

theorem sgnIm_mul_self (e : Fin 4) : sgnIm e * sgnIm e = 1 := by
  fin_cases e <;> simp [sgnIm]

theorem sgnRe_eq (e : Fin 4) : sgnRe e = 1 ∨ sgnRe e = -1 := by
  fin_cases e <;> simp [sgnRe]

theorem sgnIm_eq (e : Fin 4) : sgnIm e = 1 ∨ sgnIm e = -1 := by
  fin_cases e <;> simp [sgnIm]

/-- The linear parts of the four reflections. -/
@[expose] noncomputable def quadL : Fin 4 → (ℂ ≃ₗᵢ[ℝ] ℂ) :=
  ![LinearIsometryEquiv.refl ℝ ℂ, flipRe, flipIm, LinearIsometryEquiv.neg ℝ]

theorem quadL_re (e : Fin 4) (w : ℂ) : (quadL e w).re = sgnRe e * w.re := by
  fin_cases e <;> simp [quadL, sgnRe, flipRe_apply, flipIm_apply]

theorem quadL_im (e : Fin 4) (w : ℂ) : (quadL e w).im = sgnIm e * w.im := by
  fin_cases e <;> simp [quadL, sgnIm, flipRe_apply, flipIm_apply]

/-- The translation part of the `e`-th similarity. -/
@[expose] noncomputable def quadC (σ : ℝ) (a₀ : ℂ) (e : Fin 4) : ℂ := σ • a₀ - quadL e (σ • a₀)

/-- The `e`-th similarity `y ↦ σ a₀ + L_e (σ (y - a₀))`. -/
@[expose] noncomputable def quadMap (σ : ℝ) (a₀ : ℂ) (e : Fin 4) : ℂ → ℂ :=
  simMap σ (quadL e) (quadC σ a₀ e)

/-- The `e`-th transported field. -/
@[expose] noncomputable def quadField (σ : ℝ) (a₀ : ℂ) (e : Fin 4) (E : ℂ → ℂ) : ℂ → ℂ :=
  simField σ (quadL e) (quadC σ a₀ e) E

variable {σ : ℝ} {a₀ : ℂ} {t : ℝ}

theorem quadMap_sub (e : Fin 4) (y : ℂ) :
    quadMap σ a₀ e y - σ • a₀ = quadL e (σ • (y - a₀)) := by
  simp only [quadMap, quadC, simMap, smul_sub, map_sub]
  ring

theorem quadMap_re (e : Fin 4) (y : ℂ) :
    (quadMap σ a₀ e y - σ • a₀).re = sgnRe e * (σ * (y - a₀).re) := by
  rw [quadMap_sub, quadL_re, Complex.smul_re, smul_eq_mul]

theorem quadMap_im (e : Fin 4) (y : ℂ) :
    (quadMap σ a₀ e y - σ • a₀).im = sgnIm e * (σ * (y - a₀).im) := by
  rw [quadMap_sub, quadL_im, Complex.smul_im, smul_eq_mul]

theorem sgnRe_mul_quadMap_re (e : Fin 4) (y : ℂ) :
    sgnRe e * (quadMap σ a₀ e y - σ • a₀).re = σ * (y - a₀).re := by
  rw [quadMap_re, ← mul_assoc, sgnRe_mul_self, one_mul]

theorem sgnIm_mul_quadMap_im (e : Fin 4) (y : ℂ) :
    sgnIm e * (quadMap σ a₀ e y - σ • a₀).im = σ * (y - a₀).im := by
  rw [quadMap_im, ← mul_assoc, sgnIm_mul_self, one_mul]

theorem reflect4_eq_quadMap (e : Fin 4) (y : ℂ) :
    reflect4 (σ • a₀) (σ • y) e = quadMap σ a₀ e y := by
  apply Complex.ext
  · have h := quadMap_re (σ := σ) (a₀ := a₀) e y
    rw [Complex.sub_re] at h
    rw [reflect4_re, Complex.sub_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
    rw [Complex.smul_re, smul_eq_mul, Complex.sub_re] at h
    linarith
  · have h := quadMap_im (σ := σ) (a₀ := a₀) e y
    rw [Complex.sub_im] at h
    rw [reflect4_im, Complex.sub_im, Complex.smul_im, Complex.smul_im, smul_eq_mul, smul_eq_mul]
    rw [Complex.smul_im, smul_eq_mul, Complex.sub_im] at h
    linarith

theorem reflectPts_eq_quadMap {nb : ℕ} (Y : Fin nb → ℂ) (e : Fin 4) (i : Fin nb) :
    reflectPts (σ • a₀) (fun i => σ • Y i) (finProdFinEquiv (e, i)) = quadMap σ a₀ e (Y i) := by
  rw [reflectPts_apply, reflect4_eq_quadMap]

theorem norm_quadMap_sub (hσ : 0 < σ) (e : Fin 4) (y z : ℂ) :
    ‖quadMap σ a₀ e y - quadMap σ a₀ e z‖ = σ * ‖y - z‖ :=
  norm_simMap_sub hσ y z

theorem quadMap_injective (hσ : 0 < σ) (e : Fin 4) : Function.Injective (quadMap σ a₀ e) :=
  simMap_injective hσ.ne'

/-! ### Quadrants -/

/-- The closed quadrant of the `e`-th copy. -/
@[expose] def quadClosed (b : ℂ) (s : ℝ) (e : Fin 4) : Set ℂ :=
  {x | 0 ≤ sgnRe e * (x - b).re ∧ sgnRe e * (x - b).re ≤ s ∧
    0 ≤ sgnIm e * (x - b).im ∧ sgnIm e * (x - b).im ≤ s}

/-- The open quadrant of the `e`-th copy. -/
@[expose] def quadOpen (b : ℂ) (s : ℝ) (e : Fin 4) : Set ℂ :=
  {x | 0 < sgnRe e * (x - b).re ∧ sgnRe e * (x - b).re < s ∧
    0 < sgnIm e * (x - b).im ∧ sgnIm e * (x - b).im < s}

theorem quadOpen_subset_quadClosed (b : ℂ) (s : ℝ) (e : Fin 4) : quadOpen b s e ⊆ quadClosed b s e :=
  fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem measurableSet_quadClosed (b : ℂ) (s : ℝ) (e : Fin 4) : MeasurableSet (quadClosed b s e) := by
  have hc1 : Continuous fun x : ℂ => sgnRe e * (x - b).re := by fun_prop
  have hc2 : Continuous fun x : ℂ => sgnIm e * (x - b).im := by fun_prop
  have h : quadClosed b s e = ({x | 0 ≤ sgnRe e * (x - b).re} ∩ {x | sgnRe e * (x - b).re ≤ s}) ∩
      ({x | 0 ≤ sgnIm e * (x - b).im} ∩ {x | sgnIm e * (x - b).im ≤ s}) := by
    ext x; simp only [quadClosed, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [h]
  exact ((measurableSet_le measurable_const hc1.measurable).inter
    (measurableSet_le hc1.measurable measurable_const)).inter
    ((measurableSet_le measurable_const hc2.measurable).inter
    (measurableSet_le hc2.measurable measurable_const))

theorem isOpen_quadOpen (b : ℂ) (s : ℝ) (e : Fin 4) : IsOpen (quadOpen b s e) := by
  have hc1 : Continuous fun x : ℂ => sgnRe e * (x - b).re := by fun_prop
  have hc2 : Continuous fun x : ℂ => sgnIm e * (x - b).im := by fun_prop
  have h : quadOpen b s e = ({x | 0 < sgnRe e * (x - b).re} ∩ {x | sgnRe e * (x - b).re < s}) ∩
      ({x | 0 < sgnIm e * (x - b).im} ∩ {x | sgnIm e * (x - b).im < s}) := by
    ext x; simp only [quadOpen, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [h]
  exact ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)).inter
    ((isOpen_lt continuous_const hc2).inter (isOpen_lt hc2 continuous_const))

theorem measurableSet_quadOpen (b : ℂ) (s : ℝ) (e : Fin 4) : MeasurableSet (quadOpen b s e) :=
  (isOpen_quadOpen b s e).measurableSet

theorem quadMap_mem_quadClosed_iff (hσ : 0 < σ) (e : Fin 4) (y : ℂ) :
    quadMap σ a₀ e y ∈ quadClosed (σ • a₀) (σ * t) e ↔ y ∈ sqAt a₀ t := by
  simp only [quadClosed, mem_ofPred_eq, sgnRe_mul_quadMap_re, sgnIm_mul_quadMap_im]
  simp only [sqAt, mem_ofPred_eq, Complex.sub_re, Complex.sub_im]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem quadMap_mem_quadOpen_iff (hσ : 0 < σ) (e : Fin 4) (y : ℂ) :
    quadMap σ a₀ e y ∈ quadOpen (σ • a₀) (σ * t) e ↔ y ∈ interior (sqAt a₀ t) := by
  rw [interior_sqAt]
  simp only [quadOpen, mem_ofPred_eq, sgnRe_mul_quadMap_re, sgnIm_mul_quadMap_im]
  simp only [openSq, mem_ofPred_eq, Complex.sub_re, Complex.sub_im]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem quadMap_surjective (hσ : 0 < σ) (e : Fin 4) : Function.Surjective (quadMap σ a₀ e) :=
  fun x => ⟨_, simMap_simInv hσ.ne' x⟩

theorem image_quadMap_sqAt (hσ : 0 < σ) (e : Fin 4) :
    quadMap σ a₀ e '' sqAt a₀ t = quadClosed (σ • a₀) (σ * t) e := by
  ext x
  obtain ⟨y, rfl⟩ := quadMap_surjective (a₀ := a₀) hσ e x
  rw [(quadMap_injective hσ e).mem_set_image, quadMap_mem_quadClosed_iff hσ]

theorem image_quadMap_interior (hσ : 0 < σ) (e : Fin 4) :
    quadMap σ a₀ e '' interior (sqAt a₀ t) = quadOpen (σ • a₀) (σ * t) e := by
  ext x
  obtain ⟨y, rfl⟩ := quadMap_surjective (a₀ := a₀) hσ e x
  rw [(quadMap_injective hσ e).mem_set_image, quadMap_mem_quadOpen_iff hσ]

theorem sgn_ne_of_ne {e e' : Fin 4} (h : e ≠ e') :
    sgnRe e' = -sgnRe e ∨ sgnIm e' = -sgnIm e := by
  fin_cases e <;> fin_cases e' <;> simp_all [sgnRe, sgnIm]

theorem disjoint_quadOpen_quadClosed (b : ℂ) (s : ℝ) {e e' : Fin 4} (h : e ≠ e') :
    Disjoint (quadOpen b s e) (quadClosed b s e') := by
  rw [Set.disjoint_left]
  rintro x ⟨h1, -, h3, -⟩ ⟨h1', -, h3', -⟩
  rcases sgn_ne_of_ne h with h' | h'
  · rw [h'] at h1'; linarith
  · rw [h'] at h3'; linarith

theorem abs_le_of_sgn {u v s : ℝ} (hv : v = 1 ∨ v = -1) (h1 : 0 ≤ v * u) (h2 : v * u ≤ s) :
    |u| ≤ s := by
  rcases hv with rfl | rfl
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

theorem abs_lt_of_sgn {u v s : ℝ} (hv : v = 1 ∨ v = -1) (h1 : 0 < v * u) (h2 : v * u < s) :
    |u| < s := by
  rcases hv with rfl | rfl
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith

theorem quadClosed_subset_sq (b : ℂ) (s : ℝ) (e : Fin 4) : quadClosed b s e ⊆ sq b (2 * s) := by
  rintro x ⟨h1, h2, h3, h4⟩
  have hr := abs_le_of_sgn (sgnRe_eq e) h1 h2
  have hi := abs_le_of_sgn (sgnIm_eq e) h3 h4
  rw [Complex.sub_re, abs_le] at hr
  rw [Complex.sub_im, abs_le] at hi
  rw [Screening.mem_sq_iff, mem_Icc, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hr.1, hr.2, hi.1, hi.2]

theorem quadOpen_subset_interior_sq (b : ℂ) (s : ℝ) (e : Fin 4) :
    quadOpen b s e ⊆ interior (sq b (2 * s)) := by
  rintro x ⟨h1, h2, h3, h4⟩
  have hr := abs_lt_of_sgn (sgnRe_eq e) h1 h2
  have hi := abs_lt_of_sgn (sgnIm_eq e) h3 h4
  rw [Complex.sub_re, abs_lt] at hr
  rw [Complex.sub_im, abs_lt] at hi
  rw [Screening.mem_interior_sq_iff, mem_Ioo, mem_Ioo]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hr.1, hr.2, hi.1, hi.2]

/-- Almost every point of `sq b (2 s)` lies in one of the open quadrants. -/
theorem ae_exists_mem_quadOpen (b : ℂ) (s : ℝ) :
    ∀ᵐ x ∂volume, x ∈ sq b (2 * s) → ∃ e, x ∈ quadOpen b s e := by
  have hnull : volume (({x : ℂ | x.re = b.re} ∪ {x : ℂ | x.im = b.im}) ∪
      (({x : ℂ | x.re = b.re + s} ∪ {x : ℂ | x.re = b.re - s}) ∪
        ({x : ℂ | x.im = b.im + s} ∪ {x : ℂ | x.im = b.im - s}))) = 0 :=
    measure_union_null (measure_union_null (volume_re_eq _) (volume_im_eq _))
      (measure_union_null (measure_union_null (volume_re_eq _) (volume_re_eq _))
        (measure_union_null (volume_im_eq _) (volume_im_eq _)))
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxQ
  simp only [mem_union, mem_ofPred_eq, not_or] at hx
  obtain ⟨⟨hr0, hi0⟩, ⟨hr1, hr2⟩, hi1, hi2⟩ := hx
  rw [Screening.mem_sq_iff, mem_Icc, mem_Icc] at hxQ
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hxQ
  have r1 : b.re - s < x.re := lt_of_le_of_ne (by linarith) (Ne.symm hr2)
  have r2 : x.re < b.re + s := lt_of_le_of_ne (by linarith) hr1
  have i1 : b.im - s < x.im := lt_of_le_of_ne (by linarith) (Ne.symm hi2)
  have i2 : x.im < b.im + s := lt_of_le_of_ne (by linarith) hi1
  simp only [quadOpen, mem_ofPred_eq, Complex.sub_re, Complex.sub_im]
  rcases lt_or_gt_of_ne hr0 with hr | hr <;> rcases lt_or_gt_of_ne hi0 with hi | hi
  · exact ⟨3, by simp only [sgnRe, sgnIm]; norm_num; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩
  · exact ⟨1, by simp only [sgnRe, sgnIm]; norm_num; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩
  · exact ⟨2, by simp only [sgnRe, sgnIm]; norm_num; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩
  · exact ⟨0, by simp only [sgnRe, sgnIm]; norm_num; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩

theorem pairwise_disjoint_quadOpen (b : ℂ) (s : ℝ) :
    Pairwise (Function.onFun Disjoint (quadOpen b s)) := fun _ _ h =>
  (disjoint_quadOpen_quadClosed b s h).mono_right (quadOpen_subset_quadClosed b s _)

/-- `sq b (2 s)` is a.e. the disjoint union of the four open quadrants. -/
theorem sq_ae_eq_iUnion_quadOpen (b : ℂ) (s : ℝ) :
    sq b (2 * s) =ᵐ[volume] ⋃ e, quadOpen b s e := by
  refine (ae_le_set.2 ?_).antisymm (Eventually.of_forall fun x hx => ?_)
  · have h := ae_exists_mem_quadOpen b s
    rw [ae_iff] at h
    refine measure_mono_null (fun x hx => ?_) h
    obtain ⟨h1, h2⟩ := hx
    simp only [mem_iUnion, not_exists] at h2
    simp only [mem_ofPred_eq, not_imp, not_exists]
    exact ⟨h1, h2⟩
  · obtain ⟨e, he⟩ := mem_iUnion.1 hx
    exact interior_subset (quadOpen_subset_interior_sq b s e he)

end Bridge

end Sphere

end SandierSerfaty

end
