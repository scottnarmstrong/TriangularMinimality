/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Neumann
public import SandierSerfaty.Torus.SquareLatticeGeometry
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Reflections of the plane and the reflected configuration (sphere note, Lemma 6.2, algebra)

* `Lower.reflX c`, `Lower.reflY c`: the reflections across the lines `Re z = c` and `Im z = c`,
  as affine isometries `x ↦ L x + const` with linear parts `Lower.flipRe`, `Lower.flipIm`;
* `Lower.laplacian_comp_isom`: `Δ (f ∘ (L · + c)) x = Δ f (L x + c)` for a linear isometry `L` of `ℂ`;
* the four reflected copies `reflect4 b y e`, their coordinates relative to the corner `b`, and the
  permutation of `Fin (4 n̄)` induced by `reflX`, `reflY` on the reflected configuration `reflectPts`;
* the `4 n̄` reflected points are pairwise distinct modulo the lattice `√(4 n̄) ℤ[i] = 2 √n̄ ℤ[i]` when
  the `n̄` points are distinct and lie in the open square `b + (0, √n̄)²`.
-/

open Laplacian

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- Reflection across the vertical line `Re z = c`. -/
@[expose] def reflX (c : ℝ) (x : ℂ) : ℂ := ⟨2 * c - x.re, x.im⟩

/-- Reflection across the horizontal line `Im z = c`. -/
@[expose] def reflY (c : ℝ) (x : ℂ) : ℂ := ⟨x.re, 2 * c - x.im⟩

@[simp] theorem reflX_re (c : ℝ) (x : ℂ) : (reflX c x).re = 2 * c - x.re := rfl
@[simp] theorem reflX_im (c : ℝ) (x : ℂ) : (reflX c x).im = x.im := rfl
@[simp] theorem reflY_re (c : ℝ) (x : ℂ) : (reflY c x).re = x.re := rfl
@[simp] theorem reflY_im (c : ℝ) (x : ℂ) : (reflY c x).im = 2 * c - x.im := rfl

theorem reflX_reflX (c : ℝ) (x : ℂ) : reflX c (reflX c x) = x := by
  apply Complex.ext <;> simp

theorem reflY_reflY (c : ℝ) (x : ℂ) : reflY c (reflY c x) = x := by
  apply Complex.ext <;> simp

theorem reflX_reflY (c d : ℝ) (x : ℂ) : reflX c (reflY d x) = reflY d (reflX c x) := by
  apply Complex.ext <;> simp

/-- The linear part of `reflX`: `w ↦ -conj w = (-Re w) + i Im w`. -/
@[expose] noncomputable def flipRe : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

/-- The linear part of `reflY`: `w ↦ conj w`. -/
@[expose] noncomputable def flipIm : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE

theorem flipRe_apply (w : ℂ) : flipRe w = ⟨-w.re, w.im⟩ := by
  apply Complex.ext <;> simp [flipRe]

theorem flipIm_apply (w : ℂ) : flipIm w = ⟨w.re, -w.im⟩ := by
  apply Complex.ext <;> simp [flipIm]

theorem reflX_eq (c : ℝ) (x : ℂ) : reflX c x = flipRe x + ⟨2 * c, 0⟩ := by
  apply Complex.ext <;> simp [flipRe_apply]; ring

theorem reflY_eq (c : ℝ) (x : ℂ) : reflY c x = flipIm x + ⟨0, 2 * c⟩ := by
  apply Complex.ext <;> simp [flipIm_apply]; ring

/-- **Laplacian of a composition with an affine isometry.** -/
theorem laplacian_comp_isom (f : ℂ → ℝ) (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c x : ℂ) :
    Δ (fun y => f (L y + c)) x = Δ f (L x + c) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun y => f (L y + c)) Complex.orthonormalBasisOneI,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (Complex.orthonormalBasisOneI.map L)]
  have h : iteratedFDeriv ℝ 2 (fun y => f (L y + c)) x =
      (iteratedFDeriv ℝ 2 f (L x + c)).compContinuousLinearMap fun _ => (L : ℂ →L[ℝ] ℂ) := by
    have := L.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right (fun z => f (z + c))
      uniqueDiffOn_univ (x := x) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at this
    have e : (fun y => f (L y + c)) = (fun z => f (z + c)) ∘ L.toContinuousLinearEquiv := rfl
    rw [e, this, iteratedFDeriv_comp_add_right]
    rfl
  simp only [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, OrthonormalBasis.coe_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext j
  fin_cases j <;> rfl

section Lattice

open Torus in
theorem flipRe_mem_squareLattice {n : ℕ} {γ : ℂ} (h : γ ∈ squareLattice n) :
    flipRe γ ∈ squareLattice n := by
  obtain ⟨p, q, rfl⟩ := mem_squareLattice_iff.1 h
  rw [flipRe_apply]
  have := mk_mem_squareLattice (n := n) (-p) q
  simpa using this

open Torus in
theorem flipIm_mem_squareLattice {n : ℕ} {γ : ℂ} (h : γ ∈ squareLattice n) :
    flipIm γ ∈ squareLattice n := by
  obtain ⟨p, q, rfl⟩ := mem_squareLattice_iff.1 h
  rw [flipIm_apply]
  have := mk_mem_squareLattice (n := n) p (-q)
  simpa using this

end Lattice

section Reflect4

theorem reflect4_zero (b y : ℂ) : reflect4 b y 0 = y := rfl

theorem reflect4_one (b y : ℂ) : reflect4 b y 1 = reflX b.re y := by
  apply Complex.ext <;> simp [reflect4]; ring

theorem reflect4_two (b y : ℂ) : reflect4 b y 2 = reflY b.im y := by
  apply Complex.ext <;> simp [reflect4]; ring

theorem reflect4_three (b y : ℂ) : reflect4 b y 3 = reflX b.re (reflY b.im y) := by
  apply Complex.ext <;> simp [reflect4]

/-- Sign of the real part (relative to the corner) of the `e`-th reflected copy. -/
@[expose] def sgnRe (e : Fin 4) : ℝ := ![1, -1, 1, -1] e

/-- Sign of the imaginary part (relative to the corner) of the `e`-th reflected copy. -/
@[expose] def sgnIm (e : Fin 4) : ℝ := ![1, 1, -1, -1] e

theorem reflect4_re (b y : ℂ) (e : Fin 4) : (reflect4 b y e).re = b.re + sgnRe e * (y - b).re := by
  fin_cases e <;> simp [reflect4, sgnRe]; ring

theorem reflect4_im (b y : ℂ) (e : Fin 4) : (reflect4 b y e).im = b.im + sgnIm e * (y - b).im := by
  fin_cases e <;> simp [reflect4, sgnIm]; ring

/-- The index permutation of `reflX`. -/
@[expose] def permX : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- The index permutation of `reflY`. -/
@[expose] def permY : Fin 4 → Fin 4 := ![2, 3, 0, 1]

theorem reflX_reflect4 (b y : ℂ) (e : Fin 4) :
    reflX b.re (reflect4 b y e) = reflect4 b y (permX e) := by
  fin_cases e
  · simp [permX, reflect4_zero, reflect4_one]
  · simp [permX, reflect4_zero, reflect4_one, reflX_reflX]
  · simp [permX, reflect4_two, reflect4_three]
  · simp [permX, reflect4_two, reflect4_three, reflX_reflX]

theorem reflY_reflect4 (b y : ℂ) (e : Fin 4) :
    reflY b.im (reflect4 b y e) = reflect4 b y (permY e) := by
  fin_cases e
  · simp [permY, reflect4_zero, reflect4_two]
  · simp [permY, reflect4_one, reflect4_three, reflX_reflY]
  · simp [permY, reflect4_zero, reflect4_two, reflY_reflY]
  · simp [permY, reflect4_one, reflect4_three, ← reflX_reflY, reflY_reflY]

variable {nb : ℕ}

theorem reflectPts_apply (b : ℂ) (Z : Fin nb → ℂ) (e : Fin 4) (i : Fin nb) :
    reflectPts b Z (finProdFinEquiv (e, i)) = reflect4 b (Z i) e := by
  simp [reflectPts]

theorem exists_reflectPts_eq (b : ℂ) (Z : Fin nb → ℂ) (k : Fin (4 * nb)) :
    ∃ e i, reflectPts b Z k = reflect4 b (Z i) e :=
  ⟨(finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2, rfl⟩

/-- `reflX` permutes the reflected charges. -/
theorem exists_reflX_reflectPts (b : ℂ) (Z : Fin nb → ℂ) (k : Fin (4 * nb)) :
    ∃ k', reflX b.re (reflectPts b Z k) = reflectPts b Z k' := by
  obtain ⟨e, i, h⟩ := exists_reflectPts_eq b Z k
  exact ⟨finProdFinEquiv (permX e, i), by rw [reflectPts_apply, h, reflX_reflect4]⟩

/-- `reflY` permutes the reflected charges. -/
theorem exists_reflY_reflectPts (b : ℂ) (Z : Fin nb → ℂ) (k : Fin (4 * nb)) :
    ∃ k', reflY b.im (reflectPts b Z k) = reflectPts b Z k' := by
  obtain ⟨e, i, h⟩ := exists_reflectPts_eq b Z k
  exact ⟨finProdFinEquiv (permY e, i), by rw [reflectPts_apply, h, reflY_reflect4]⟩

end Reflect4

section Distinct

theorem sqrt_four_mul (nb : ℕ) : √((4 * nb : ℕ) : ℝ) = 2 * √(nb : ℝ) := by
  push_cast
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem int_eq_zero_of_abs_lt {s : ℝ} (hs : 0 < s) {p : ℤ} (h : |(p : ℝ) * (2 * s)| < 2 * s) :
    p = 0 := by
  by_contra hne
  have h1 : (1 : ℤ) ≤ |p| := Int.one_le_abs hne
  have h2 : (1 : ℝ) ≤ |(p : ℝ)| := by exact_mod_cast h1
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * s)] at h
  nlinarith

open Torus in
/-- Two reflected copies of points of the open quadrant `b + (0, s)²` that agree modulo `2 s ℤ[i]` are the
same copy of the same point. -/
theorem reflect4_eq_of_sub_mem {nb : ℕ} (hnb : 1 ≤ nb) (b : ℂ) (Z : Fin nb → ℂ)
    (hZ : ∀ i, 0 < (Z i - b).re ∧ (Z i - b).re < √nb ∧ 0 < (Z i - b).im ∧ (Z i - b).im < √nb)
    (e e' : Fin 4) (i j : Fin nb)
    (h : reflect4 b (Z i) e - reflect4 b (Z j) e' ∈ squareLattice (4 * nb)) :
    e = e' ∧ Z i = Z j := by
  have hs : 0 < √(nb : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnb)
  obtain ⟨p, q, hpq⟩ := mem_squareLattice_iff.1 h
  rw [sqrt_four_mul] at hpq
  have hre := congrArg Complex.re hpq
  have him := congrArg Complex.im hpq
  simp only [Complex.sub_re, Complex.sub_im, reflect4_re, reflect4_im] at hre him
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hZ i
  obtain ⟨hj1, hj2, hj3, hj4⟩ := hZ j
  simp only [Complex.sub_re, Complex.sub_im] at hi1 hi2 hi3 hi4 hj1 hj2 hj3 hj4
  have hsr : ∀ e : Fin 4, sgnRe e = 1 ∨ sgnRe e = -1 := fun e => by
    fin_cases e <;> simp [sgnRe]
  have hsi : ∀ e : Fin 4, sgnIm e = 1 ∨ sgnIm e = -1 := fun e => by
    fin_cases e <;> simp [sgnIm]
  have hp : p = 0 := by
    apply int_eq_zero_of_abs_lt hs
    rw [abs_lt]
    rcases hsr e with h1 | h1 <;> rcases hsr e' with h2 | h2 <;> rw [h1, h2] at hre <;>
      constructor <;> linarith
  have hq : q = 0 := by
    apply int_eq_zero_of_abs_lt hs
    rw [abs_lt]
    rcases hsi e with h1 | h1 <;> rcases hsi e' with h2 | h2 <;> rw [h1, h2] at him <;>
      constructor <;> linarith
  subst hp hq
  simp only [Int.cast_zero, zero_mul] at hre him
  have hZeq : ∀ (e e' : Fin 4), sgnRe e * ((Z i).re - b.re) = sgnRe e' * ((Z j).re - b.re) →
      sgnIm e * ((Z i).im - b.im) = sgnIm e' * ((Z j).im - b.im) → e = e' ∧ Z i = Z j := by
    intro e e' h1 h2
    fin_cases e <;> fin_cases e' <;> simp only [sgnRe, sgnIm] at h1 h2 <;> simp at h1 h2 <;>
      first
      | (exfalso; linarith)
      | (refine ⟨rfl, ?_⟩
         apply Complex.ext
         · linarith
         · linarith)
  exact hZeq e e' (by linarith) (by linarith)

open Torus in
theorem reflectPts_distinct {nb : ℕ} (hnb : 1 ≤ nb) (b : ℂ) (Z : Fin nb → ℂ)
    (hZi : Function.Injective Z)
    (hZ : ∀ i, 0 < (Z i - b).re ∧ (Z i - b).re < √nb ∧ 0 < (Z i - b).im ∧ (Z i - b).im < √nb)
    (k l : Fin (4 * nb)) (h : reflectPts b Z k - reflectPts b Z l ∈ squareLattice (4 * nb)) :
    k = l := by
  have := reflect4_eq_of_sub_mem hnb b Z hZ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm l).1
    (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm l).2 h
  obtain ⟨h1, h2⟩ := this
  apply finProdFinEquiv.symm.injective
  exact Prod.ext h1 (hZi h2)

end Distinct

section Measure

open MeasureTheory

theorem measurePreserving_isom_add (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) :
    MeasurePreserving (fun x => L x + c) volume volume := by
  have : (fun x => L x + c) = (fun x => x + c) ∘ L := rfl
  rw [this]
  exact (measurePreserving_add_right volume c).comp L.measurePreserving

theorem measurableEmbedding_isom_add (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) :
    MeasurableEmbedding (fun x => L x + c) := by
  have : (fun x => L x + c) = ((L.toHomeomorph).trans (Homeomorph.addRight c) : ℂ → ℂ) := by
    funext x; simp
  rw [this]
  exact (L.toHomeomorph.trans (Homeomorph.addRight c)).measurableEmbedding

theorem measurePreserving_reflX (c : ℝ) : MeasurePreserving (reflX c) volume volume := by
  have : reflX c = fun x => flipRe x + ⟨2 * c, 0⟩ := funext (reflX_eq c)
  rw [this]; exact measurePreserving_isom_add _ _

theorem measurePreserving_reflY (c : ℝ) : MeasurePreserving (reflY c) volume volume := by
  have : reflY c = fun x => flipIm x + ⟨0, 2 * c⟩ := funext (reflY_eq c)
  rw [this]; exact measurePreserving_isom_add _ _

theorem measurableEmbedding_reflX (c : ℝ) : MeasurableEmbedding (reflX c) := by
  have : reflX c = fun x => flipRe x + ⟨2 * c, 0⟩ := funext (reflX_eq c)
  rw [this]; exact measurableEmbedding_isom_add _ _

theorem measurableEmbedding_reflY (c : ℝ) : MeasurableEmbedding (reflY c) := by
  have : reflY c = fun x => flipIm x + ⟨0, 2 * c⟩ := funext (reflY_eq c)
  rw [this]; exact measurableEmbedding_isom_add _ _

/-- Vertical lines are null. -/
theorem volume_re_eq (c : ℝ) : volume {x : ℂ | x.re = c} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := ({c} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
    (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet)
  have e : {x : ℂ | x.re = c} = Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ Set.univ) := by
    ext x; simp [Complex.measurableEquivRealProd]
  rw [e, h, Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Horizontal lines are null. -/
theorem volume_im_eq (c : ℝ) : volume {x : ℂ | x.im = c} = 0 := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := (Set.univ : Set ℝ) ×ˢ ({c} : Set ℝ))
    ((MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet)
  have e : {x : ℂ | x.im = c} = Complex.measurableEquivRealProd ⁻¹' ((Set.univ : Set ℝ) ×ˢ ({c} : Set ℝ)) := by
    ext x; simp [Complex.measurableEquivRealProd]
  rw [e, h, Measure.volume_eq_prod, Measure.prod_prod]
  simp

end Measure

end Lower

end Sphere

end SandierSerfaty

end
