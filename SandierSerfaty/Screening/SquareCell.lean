/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.Lattice
public import SandierSerfaty.Torus.SquareLatticeGeometry
public import SandierSerfaty.Statements.Jellium.Defs.Cube
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Closed squares and the square lattice

`SandierSerfaty.sq c t` is the closed axis-parallel square of side `t` centred at `c`
(`sq 0 t = cube t`; the screening note's §1.1).

For `Q = sq c √n` and `Γ = squareLattice n = √n ℤ[i]` (screening note, §5, "Setting"):

* `add_notMem_sq_of_mem_interior`: `(γ + int Q) ∩ Q = ∅` for `0 ≠ γ ∈ Γ`;
* `exists_sub_mem_sq`: the `Γ`-translates of `Q` cover `ℂ`;
* `isAddFundamentalDomain_sq`: `Q` is an a.e. fundamental domain of `Γ`;
* `eq_of_sub_mem_squareLattice`: two points of `int Q` in the same class modulo `Γ` are equal.
-/

open MeasureTheory Metric Set
open scoped Pointwise

public section

namespace SandierSerfaty

/-- The closed axis-parallel square of side `t` centred at `c` (`sq 0 t = cube t`). -/
@[expose] def sq (c : ℂ) (t : ℝ) : Set ℂ :=
  Icc (c.re - t / 2) (c.re + t / 2) ×ℂ Icc (c.im - t / 2) (c.im + t / 2)

namespace Screening

open Torus

theorem mem_sq_iff {c x : ℂ} {t : ℝ} :
    x ∈ sq c t ↔ x.re ∈ Icc (c.re - t / 2) (c.re + t / 2) ∧
      x.im ∈ Icc (c.im - t / 2) (c.im + t / 2) := Iff.rfl

theorem sq_zero (t : ℝ) : sq 0 t = cube t := by
  ext x
  simp [sq, cube, Complex.mem_reProdIm, sub_eq_add_neg]

theorem interior_sq (c : ℂ) (t : ℝ) :
    interior (sq c t) = Ioo (c.re - t / 2) (c.re + t / 2) ×ℂ Ioo (c.im - t / 2) (c.im + t / 2) := by
  rw [sq, Complex.interior_reProdIm, interior_Icc, interior_Icc]

theorem mem_interior_sq_iff {c x : ℂ} {t : ℝ} :
    x ∈ interior (sq c t) ↔ x.re ∈ Ioo (c.re - t / 2) (c.re + t / 2) ∧
      x.im ∈ Ioo (c.im - t / 2) (c.im + t / 2) := by
  rw [interior_sq]; exact Iff.rfl

theorem isClosed_sq (c : ℂ) (t : ℝ) : IsClosed (sq c t) := by
  unfold sq; exact isClosed_Icc.reProdIm isClosed_Icc

theorem measurableSet_sq (c : ℂ) (t : ℝ) : MeasurableSet (sq c t) :=
  (isClosed_sq c t).measurableSet

theorem isBounded_sq (c : ℂ) (t : ℝ) : Bornology.IsBounded (sq c t) := by
  refine (Metric.isBounded_iff_subset_closedBall c).2 ⟨|t|, fun x hx => ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have : |x.re - c.re| ≤ |t| / 2 := abs_le.2 ⟨by linarith [le_abs_self t, neg_abs_le t],
    by linarith [le_abs_self t]⟩
  have : |x.im - c.im| ≤ |t| / 2 := abs_le.2 ⟨by linarith [le_abs_self t, neg_abs_le t],
    by linarith [le_abs_self t]⟩
  linarith

theorem isCompact_sq (c : ℂ) (t : ℝ) : IsCompact (sq c t) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_sq c t) (isBounded_sq c t)

theorem convex_sq (c : ℂ) (t : ℝ) : Convex ℝ (sq c t) := by
  unfold sq
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

/-! ### The square lattice -/

variable {n : ℕ}

/-- An integer `p` with `|p s| < s`, `s > 0`, vanishes. -/
theorem int_eq_zero_of_abs_mul_lt {p : ℤ} {s : ℝ} (hs : 0 < s) (h : |(p : ℝ) * s| < s) :
    p = 0 := by
  rw [abs_mul, abs_of_pos hs, mul_lt_iff_lt_one_left hs] at h
  have : |p| < 1 := by exact_mod_cast h
  exact abs_lt.1 this |>.elim (fun h1 h2 => by omega)

/-- **`(γ + int Q) ∩ Q = ∅`** for `0 ≠ γ ∈ √n ℤ[i]` and `Q = sq c √n`. -/
theorem add_notMem_sq_of_mem_interior {c x γ : ℂ} (hx : x ∈ interior (sq c √n))
    (hγ : γ ∈ squareLattice n) (hγ0 : γ ≠ 0) : x + γ ∉ sq c √n := by
  intro hxγ
  obtain ⟨p, q, rfl⟩ := mem_squareLattice_iff.1 hγ
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_interior_sq_iff.1 hx
  obtain ⟨⟨h5, h6⟩, h7, h8⟩ := hxγ
  simp only [Complex.add_re, Complex.add_im] at h5 h6 h7 h8
  have hs : 0 < √(n : ℝ) := by
    by_contra h0
    have : √(n : ℝ) = 0 := le_antisymm (not_lt.1 h0) (Real.sqrt_nonneg _)
    rw [this] at h1 h2; linarith
  have hp : p = 0 := int_eq_zero_of_abs_mul_lt hs (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hq : q = 0 := int_eq_zero_of_abs_mul_lt hs (abs_lt.2 ⟨by linarith, by linarith⟩)
  exact hγ0 (by subst hp hq; apply Complex.ext <;> simp)

/-- Two points of `int Q` that differ by an element of `√n ℤ[i]` are equal. -/
theorem eq_of_sub_mem_squareLattice {c x y : ℂ} (hx : x ∈ interior (sq c √n))
    (hy : y ∈ interior (sq c √n)) (hxy : x - y ∈ squareLattice n) : x = y := by
  by_contra hne
  have := add_notMem_sq_of_mem_interior hy hxy (sub_ne_zero.2 hne)
  rw [add_sub_cancel] at this
  exact this (interior_subset hx)

/-- **Covering.** Every point is congruent modulo `√n ℤ[i]` to a point of `sq c √n`. -/
theorem exists_sub_mem_sq (hn : 1 ≤ n) (c x : ℂ) : ∃ γ ∈ squareLattice n, x - γ ∈ sq c √n := by
  set o : ℂ := ⟨c.re - √(n : ℝ) / 2, c.im - √(n : ℝ) / 2⟩ with ho
  obtain ⟨γ, hγ, hbox⟩ := exists_sub_mem_box hn (x - o)
  refine ⟨γ, hγ, ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hbox
  simp only [Complex.sub_re, Complex.sub_im, ho] at h1 h2 h3 h4
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Complex.sub_re, Complex.sub_im] <;> linarith

/-- The `Γ`-action on `ℂ` is translation. -/
theorem lattice_vadd_eq {Γ : Submodule ℤ ℂ} (g : Γ) (x : ℂ) : g +ᵥ x = (g : ℂ) + x := rfl

theorem lattice_vadd_set_eq {Γ : Submodule ℤ ℂ} (g : Γ) (s : Set ℂ) :
    g +ᵥ s = (fun x => (g : ℂ) + x) '' s := rfl

/-- **The closed square of side `√n` is an a.e. fundamental domain of `√n ℤ[i]`.** -/
theorem isAddFundamentalDomain_sq [NeZero n] (c : ℂ) :
    IsAddFundamentalDomain (squareLattice n) (sq c √n) volume := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  refine ⟨(measurableSet_sq c _).nullMeasurableSet, Filter.Eventually.of_forall fun x => ?_,
    fun g g' hgg' => ?_⟩
  · obtain ⟨γ, hγ, hx⟩ := exists_sub_mem_sq hn c x
    refine ⟨⟨-γ, (squareLattice n).neg_mem hγ⟩, ?_⟩
    rw [lattice_vadd_eq]
    simpa [neg_add_eq_sub] using hx
  · show volume ((g +ᵥ sq c √n) ∩ (g' +ᵥ sq c √n)) = 0
    rw [lattice_vadd_set_eq, lattice_vadd_set_eq]
    set T : Set ℂ := (fun x => (g : ℂ) + x) '' sq c √n with hT
    have hconv : Convex ℝ T := (convex_sq c _).translate _
    have hsub : T ∩ (fun x => (g' : ℂ) + x) '' sq c √n ⊆ frontier T := by
      rintro x ⟨hx1, hx2⟩
      rw [frontier, mem_sdiff]
      refine ⟨subset_closure hx1, fun hint => ?_⟩
      have himg : interior T = (fun x => (g : ℂ) + x) '' interior (sq c √n) := by
        rw [hT]
        exact ((Homeomorph.addLeft (g : ℂ)).image_interior (sq c √n)).symm
      rw [himg] at hint
      obtain ⟨y, hy, rfl⟩ := hint
      obtain ⟨z, hz, hzy⟩ := hx2
      have hne : (g : ℂ) - g' ≠ 0 := by
        rw [sub_ne_zero]; exact fun h => hgg' (Subtype.ext h)
      have hmem : (g : ℂ) - g' ∈ squareLattice n := (squareLattice n).sub_mem g.2 g'.2
      refine add_notMem_sq_of_mem_interior hy hmem hne ?_
      have : y + ((g : ℂ) - g') = z := by linear_combination hzy.symm
      rw [this]; exact hz
    exact measure_mono_null hsub (hconv.addHaar_frontier volume)

end Screening

end SandierSerfaty

end
