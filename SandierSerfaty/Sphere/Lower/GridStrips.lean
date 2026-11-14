/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GridOffset

/-!
# Strips of grid squares and the band integral (sphere note, Lemma 6.12, geometry)

`Lower.gridSq R θ j = θ + R (j + [0,1)²)` is the half-open grid square of index `j ∈ ℤ²`;
`Lower.sideDist R θ j z` is the distance from `z ∈ K` to the four sides of `K = gridSq R θ j`;
`Lower.stripSq R θ a b j = {z ∈ K | a ≤ dist(z, ∂K) ≤ b}` (`strip⁺(K)` for `[a,b] = [ℓ̃/2, 2ℓ̃+1]`, `lay(K)` for
`[a,b] = [0,2]`).

* `Lower.gridDist_eq_sideDist`: on `K`, the distance to the walls of the grid is `dist(z, ∂K)`;
* `Lower.sum_lintegral_strip_le`: for any finite family `J` of grid squares and any `g ≥ 0`,
  `∑_{K ∈ J} ∫_{strip(K)} g ≤ ∫_{gridBand R θ a b} g` (the squares are pairwise disjoint), which turns the abstract Fubini
  bound `exists_offset_two_bands` into the form of Lemma 6.12.
-/

open MeasureTheory Set
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The half-open grid square `θ + R (j + [0,1)²)`. -/
@[expose] def gridSq (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) : Set ℂ :=
  {z | θ.1 + R * j.1 ≤ z.re ∧ z.re < θ.1 + R * (j.1 + 1) ∧
    θ.2 + R * j.2 ≤ z.im ∧ z.im < θ.2 + R * (j.2 + 1)}

/-- The distance from `z` to the four sides of the grid square of index `j`. -/
@[expose] noncomputable def sideDist (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) (z : ℂ) : ℝ :=
  min (min (z.re - (θ.1 + R * j.1)) (θ.1 + R * (j.1 + 1) - z.re))
    (min (z.im - (θ.2 + R * j.2)) (θ.2 + R * (j.2 + 1) - z.im))

/-- `{z ∈ K | a ≤ dist(z, ∂K) ≤ b}` for `K = gridSq R θ j`. -/
@[expose] def stripSq (R : ℝ) (θ : ℝ × ℝ) (a b : ℝ) (j : ℤ × ℤ) : Set ℂ :=
  {z | z ∈ gridSq R θ j ∧ a ≤ sideDist R θ j z ∧ sideDist R θ j z ≤ b}

theorem cellPos_sub_int_mul {R : ℝ} (hR : 0 < R) (x : ℝ) (k : ℤ) :
    cellPos R (x - R * k) = cellPos R x := by
  unfold cellPos
  have : (x - R * k) / R = x / R - k := by field_simp
  rw [this, Int.floor_sub_intCast]
  push_cast; ring

theorem cellPos_eq_of_mem {R : ℝ} (hR : 0 < R) {x : ℝ} {k : ℤ} (h1 : R * k ≤ x)
    (h2 : x < R * (k + 1)) : cellPos R x = x - R * k := by
  have := cellPos_sub_int_mul hR x k
  rw [← this]
  exact cellPos_of_mem_Ico hR ⟨by linarith, by linarith⟩

theorem wallDist_eq_of_mem {R : ℝ} (hR : 0 < R) {x : ℝ} {k : ℤ} (h1 : R * k ≤ x)
    (h2 : x < R * (k + 1)) : wallDist R x = min (x - R * k) (R * (k + 1) - x) := by
  unfold wallDist
  rw [cellPos_eq_of_mem hR h1 h2]
  congr 1
  ring

theorem gridDist_eq_sideDist {R : ℝ} (hR : 0 < R) {θ : ℝ × ℝ} {j : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ gridSq R θ j) : gridDist R θ z = sideDist R θ j z := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  unfold gridDist sideDist
  rw [wallDist_eq_of_mem hR (k := j.1) (by linarith) (by linarith),
    wallDist_eq_of_mem hR (k := j.2) (by linarith) (by linarith)]
  congr 2 <;> ring

theorem measurableSet_gridSq (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) : MeasurableSet (gridSq R θ j) := by
  have : gridSq R θ j = (Complex.re ⁻¹' Ico (θ.1 + R * j.1) (θ.1 + R * (j.1 + 1))) ∩
      (Complex.im ⁻¹' Ico (θ.2 + R * j.2) (θ.2 + R * (j.2 + 1))) := by
    ext z; simp [gridSq, and_assoc]
  rw [this]
  exact (measurableSet_Ico.preimage Complex.measurable_re).inter
    (measurableSet_Ico.preimage Complex.measurable_im)

theorem measurable_sideDist (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) : Measurable (sideDist R θ j) := by
  unfold sideDist
  have hre := Complex.measurable_re
  have him := Complex.measurable_im
  exact (((hre.sub_const _).min (measurable_const.sub hre)).min
    ((him.sub_const _).min (measurable_const.sub him)))

theorem measurableSet_stripSq (R : ℝ) (θ : ℝ × ℝ) (a b : ℝ) (j : ℤ × ℤ) :
    MeasurableSet (stripSq R θ a b j) := by
  have : stripSq R θ a b j = gridSq R θ j ∩ ({z | a ≤ sideDist R θ j z} ∩ {z | sideDist R θ j z ≤ b}) := by
    ext z; simp only [stripSq, mem_inter_iff, mem_ofPred_eq]
  rw [this]
  exact (measurableSet_gridSq R θ j).inter
    ((measurableSet_le measurable_const (measurable_sideDist R θ j)).inter
      (measurableSet_le (measurable_sideDist R θ j) measurable_const))

theorem gridSq_eq_of_mem {R : ℝ} (hR : 0 < R) {θ : ℝ × ℝ} {j j' : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ gridSq R θ j) (hz' : z ∈ gridSq R θ j') : j = j' := by
  have key : ∀ (y c : ℝ) (k k' : ℤ), c + R * k ≤ y → y < c + R * (k + 1) →
      c + R * k' ≤ y → y < c + R * (k' + 1) → k = k' := by
    intro y c k k' h1 h2 h3 h4
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
      nlinarith
    · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
      nlinarith
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨h1', h2', h3', h4'⟩ := hz'
  exact Prod.ext (key z.re θ.1 j.1 j'.1 h1 h2 h1' h2') (key z.im θ.2 j.2 j'.2 h3 h4 h3' h4')

/-- **Lemma 6.12, geometry.** For a finite family of grid squares and `g ≥ 0`, the strips' masses sum to at most the
mass of the band of grid distances. -/
theorem sum_lintegral_strip_le {R : ℝ} (hR : 0 < R) (θ : ℝ × ℝ) (a b : ℝ) (J : Finset (ℤ × ℤ))
    (g : ℂ → ℝ≥0∞) :
    ∑ j ∈ J, ∫⁻ z in stripSq R θ a b j, g z ≤ ∫⁻ z in gridBand R θ a b, g z := by
  have hd : Set.PairwiseDisjoint (↑J : Set (ℤ × ℤ)) (stripSq R θ a b) := by
    intro j _ j' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    exact hne (gridSq_eq_of_mem hR hz.1 hz'.1)
  rw [← lintegral_biUnion_finset hd (fun j _ => measurableSet_stripSq R θ a b j)]
  refine lintegral_mono_set ?_
  intro z hz
  obtain ⟨j, -, hz⟩ := Set.mem_iUnion₂.1 hz
  obtain ⟨hzs, ha, hb⟩ := hz
  have := gridDist_eq_sideDist hR hzs
  exact ⟨by rw [this]; exact ha, by rw [this]; exact hb⟩

end Lower

end Sphere

end SandierSerfaty

end
