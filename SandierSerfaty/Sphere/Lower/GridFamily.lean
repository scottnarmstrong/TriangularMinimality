/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GridStrips
public import SandierSerfaty.Sphere.Lower.Discrepancy

/-!
# The family of quantized squares (sphere note, Definition 6.8)

For `R > 0`, an offset `θ` and the radius `ρ`, `Lower.cellFin R θ ρ` is the finite set of grid cells `K_j = θ + R (j + [0,1)²)`
whose closure lies in `closedBall 0 (ρ - 1)`.  The quantized square of `j` is `Q_j = a_j + [0, t_j]²` with `a_j` the corner of
the cell and `t_j = Lower.qSide n R a_j ∈ [R-1, R-1/2]` chosen so that `∫_{Q_j} m ∈ ℕ`.

* `Lower.card_cellFin_mul_le`: `#cells · R² ≤ π ρ²`;
* `Lower.sqAt_subset_gridSq`, `Lower.sqAt_disjoint`: `Q_j` is contained in the half-open cell, hence the `Q_j` are pairwise
  disjoint;
* `Lower.strip_subset_stripSq`: `Q^{s₁} ∖ Q^{s₂} ⊆ strip⁺(K)` (the inclusions of Definition 6.8).
-/

open MeasureTheory Set Metric
open scoped ENNReal Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The lower-left corner of the grid cell `j`. -/
@[expose] def cellAt (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) : ℂ := ⟨θ.1 + R * j.1, θ.2 + R * j.2⟩

@[simp] theorem cellAt_re (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) : (cellAt R θ j).re = θ.1 + R * j.1 := rfl

@[simp] theorem cellAt_im (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) : (cellAt R θ j).im = θ.2 + R * j.2 := rfl

theorem sqAt_subset_gridSq {R : ℝ} (θ : ℝ × ℝ) (j : ℤ × ℤ) {t : ℝ} (ht : t < R) :
    sqAt (cellAt R θ j) t ⊆ gridSq R θ j := by
  intro z hz
  rw [mem_sqAt] at hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  simp only [cellAt_re, cellAt_im] at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem gridSq_subset_sqAt {R : ℝ} (θ : ℝ × ℝ) (j : ℤ × ℤ) :
    gridSq R θ j ⊆ sqAt (cellAt R θ j) R := by
  intro z hz
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_sqAt]
  simp only [cellAt_re, cellAt_im]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem sqAt_disjoint {R : ℝ} (hR : 0 < R) (θ : ℝ × ℝ) {j j' : ℤ × ℤ} (hne : j ≠ j') {t t' : ℝ}
    (ht : t < R) (ht' : t' < R) : Disjoint (sqAt (cellAt R θ j) t) (sqAt (cellAt R θ j') t') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hne (gridSq_eq_of_mem hR (sqAt_subset_gridSq θ j ht hz) (sqAt_subset_gridSq θ j' ht' hz'))

theorem volume_gridSq (R : ℝ) (θ : ℝ × ℝ) (j : ℤ × ℤ) :
    volume (gridSq R θ j) = ENNReal.ofReal R * ENNReal.ofReal R := by
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico (θ.1 + R * j.1) (θ.1 + R * (j.1 + 1)) ×ˢ Ico (θ.2 + R * j.2) (θ.2 + R * (j.2 + 1)))
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet)
  have e : gridSq R θ j = Complex.measurableEquivRealProd ⁻¹'
      (Ico (θ.1 + R * j.1) (θ.1 + R * (j.1 + 1)) ×ˢ Ico (θ.2 + R * j.2) (θ.2 + R * (j.2 + 1))) := by
    ext x
    simp only [gridSq, Complex.measurableEquivRealProd, mem_ofPred_eq, mem_preimage, mem_prod,
      mem_Ico]
    tauto
  rw [e, h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  congr 1 <;> congr 1 <;> ring

/-- The finite set of cells whose closure lies in `closedBall 0 (ρ - 1)`. -/
@[expose] noncomputable def cellFin (R : ℝ) (θ : ℝ × ℝ) (ρ : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc ((-⌈(ρ + |θ.1| + |θ.2|) / R⌉), (-⌈(ρ + |θ.1| + |θ.2|) / R⌉))
      (⌈(ρ + |θ.1| + |θ.2|) / R⌉, ⌈(ρ + |θ.1| + |θ.2|) / R⌉)).filter
    fun j => sqAt (cellAt R θ j) R ⊆ closedBall (0 : ℂ) (ρ - 1)

theorem mem_cellFin {R : ℝ} (hR : 0 < R) {θ : ℝ × ℝ} {ρ : ℝ} (_hρ : 1 ≤ ρ) {j : ℤ × ℤ} :
    j ∈ cellFin R θ ρ ↔ sqAt (cellAt R θ j) R ⊆ closedBall (0 : ℂ) (ρ - 1) := by
  unfold cellFin
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hc : cellAt R θ j ∈ sqAt (cellAt R θ j) R := by
    rw [mem_sqAt]; exact ⟨le_rfl, by linarith, le_rfl, by linarith⟩
  have hb := h hc
  rw [mem_closedBall, dist_zero_right] at hb
  have h1 : |(cellAt R θ j).re| ≤ ρ - 1 := (Complex.abs_re_le_norm _).trans hb
  have h2 : |(cellAt R θ j).im| ≤ ρ - 1 := (Complex.abs_im_le_norm _).trans hb
  simp only [cellAt_re, cellAt_im] at h1 h2
  rw [abs_le] at h1 h2
  rw [Finset.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
  have hB : (ρ + |θ.1| + |θ.2|) / R ≤ ⌈(ρ + |θ.1| + |θ.2|) / R⌉ := Int.le_ceil _
  have hRB : ρ + |θ.1| + |θ.2| ≤ R * ⌈(ρ + |θ.1| + |θ.2|) / R⌉ := by
    rw [div_le_iff₀ hR] at hB; linarith
  have a1 := le_abs_self θ.1
  have a2 := neg_abs_le θ.1
  have a3 := le_abs_self θ.2
  have a4 := neg_abs_le θ.2
  have a5 := abs_nonneg θ.1
  have a6 := abs_nonneg θ.2
  have hk1 : (j.1 : ℝ) ≤ ⌈(ρ + |θ.1| + |θ.2|) / R⌉ := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hk1' : -(⌈(ρ + |θ.1| + |θ.2|) / R⌉ : ℝ) ≤ j.1 := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hk2 : (j.2 : ℝ) ≤ ⌈(ρ + |θ.1| + |θ.2|) / R⌉ := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hk2' : -(⌈(ρ + |θ.1| + |θ.2|) / R⌉ : ℝ) ≤ j.2 := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  exact ⟨⟨by exact_mod_cast hk1', by exact_mod_cast hk2'⟩, by exact_mod_cast hk1, by exact_mod_cast hk2⟩

theorem card_cellFin_mul_le {R : ℝ} (hR : 0 < R) {θ : ℝ × ℝ} {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ((cellFin R θ ρ).card : ℝ) * R ^ 2 ≤ Real.pi * ρ ^ 2 := by
  have hd : Set.PairwiseDisjoint (↑(cellFin R θ ρ) : Set (ℤ × ℤ)) (gridSq R θ) := by
    intro j _ j' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    exact hne (gridSq_eq_of_mem hR hz hz')
  have h1 := measure_biUnion_finset (μ := volume) hd (fun j _ => measurableSet_gridSq R θ j)
  have hsub : (⋃ j ∈ cellFin R θ ρ, gridSq R θ j) ⊆ ball (0 : ℂ) ρ := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.1 hz
    have := ((mem_cellFin hR hρ).1 hj) (gridSq_subset_sqAt θ j hzj)
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_ball, dist_zero_right]
    linarith
  have h2 : volume (⋃ j ∈ cellFin R θ ρ, gridSq R θ j) ≤ volume (ball (0 : ℂ) ρ) := measure_mono hsub
  rw [h1, Complex.volume_ball] at h2
  simp only [volume_gridSq, Finset.sum_const, nsmul_eq_mul] at h2
  have h3 := ENNReal.toReal_mono (by finiteness) h2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hR.le,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ρ), ENNReal.coe_toReal,
    NNReal.coe_real_pi] at h3
  linarith

/-- The quantized side of the square at the corner `a` (`∫_{a + [0,t]²} m ∈ ℕ`, `t ∈ [R-1, R-1/2]`). -/
@[expose] noncomputable def qSide (n : ℕ) (R : ℝ) (a : ℂ) : ℝ :=
  if h : ∃ t ∈ Icc (R - 1) (R - 1 / 2), ∃ k : ℕ, ∫ x in sqAt a t, blowupDens n x = k then h.choose
  else R - 1

theorem qSide_spec (n : ℕ) {R : ℝ} (hR : 1 ≤ R) {a : ℂ}
    (hlow : ∀ x ∈ sqAt a (R - 1 / 2), mMinus ≤ blowupDens n x) (hbig : 1 ≤ mMinus * (R - 3 / 4)) :
    qSide n R a ∈ Icc (R - 1) (R - 1 / 2) ∧
      ∃ k : ℕ, ∫ x in sqAt a (qSide n R a), blowupDens n x = k := by
  have h := exists_quantized_side (ρ := blowupDens n) (M := mPlus) (measurable_blowupDens n)
    (blowupDens_nonneg n) (blowupDens_le n) a hR hlow hbig
  have h' : ∃ t ∈ Icc (R - 1) (R - 1 / 2), ∃ k : ℕ, ∫ x in sqAt a t, blowupDens n x = k := h
  unfold qSide
  rw [dite_eq_left h']
  exact h'.choose_spec

/-- The integer mass of a quantized square. -/
@[expose] noncomputable def sqMassNat (n : ℕ) (a : ℂ) (t : ℝ) : ℕ := ⌊∫ x in sqAt a t, blowupDens n x⌋₊

theorem sqMassNat_spec {n : ℕ} {a : ℂ} {t : ℝ} {k : ℕ} (h : ∫ x in sqAt a t, blowupDens n x = k) :
    (sqMassNat n a t : ℝ) = ∫ x in sqAt a t, blowupDens n x := by
  unfold sqMassNat
  rw [h, Nat.floor_natCast]

/-- `Q^{s₁} ∖ Q^{s₂} ⊆ strip(K)`: a point of the quantized square at distance `≥ s₁` and `< s₂` from `∂Q` is at distance in
`[s₁, s₂ + 1]` from the sides of the cell `K`. -/
theorem strip_subset_stripSq {R : ℝ} (θ : ℝ × ℝ) (j : ℤ × ℤ) {t : ℝ} (ht1 : R - 1 ≤ t) (ht2 : t ≤ R - 1 / 2)
    {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) :
    sqShrink (cellAt R θ j) t s₁ \ sqShrink (cellAt R θ j) t s₂ ⊆ stripSq R θ s₁ (s₂ + 1) j := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [mem_sqShrink] at hz1
  simp only [cellAt_re, cellAt_im] at hz1
  obtain ⟨h1, h2, h3, h4⟩ := hz1
  have hgs : z ∈ gridSq R θ j := by
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨hgs, ?_, ?_⟩
  · unfold sideDist
    refine le_min (le_min (by linarith) (by linarith)) (le_min (by linarith) (by linarith))
  · rw [mem_sqShrink] at hz2
    simp only [cellAt_re, cellAt_im, not_and_or, not_le] at hz2
    unfold sideDist
    rcases hz2 with h | h | h | h
    · calc _ ≤ min (z.re - (θ.1 + R * j.1)) (θ.1 + R * (j.1 + 1) - z.re) := min_le_left _ _
        _ ≤ z.re - (θ.1 + R * j.1) := min_le_left _ _
        _ ≤ s₂ + 1 := by linarith
    · calc _ ≤ min (z.re - (θ.1 + R * j.1)) (θ.1 + R * (j.1 + 1) - z.re) := min_le_left _ _
        _ ≤ θ.1 + R * (j.1 + 1) - z.re := min_le_right _ _
        _ ≤ s₂ + 1 := by linarith
    · calc _ ≤ min (z.im - (θ.2 + R * j.2)) (θ.2 + R * (j.2 + 1) - z.im) := min_le_right _ _
        _ ≤ z.im - (θ.2 + R * j.2) := min_le_left _ _
        _ ≤ s₂ + 1 := by linarith
    · calc _ ≤ min (z.im - (θ.2 + R * j.2)) (θ.2 + R * (j.2 + 1) - z.im) := min_le_right _ _
        _ ≤ θ.2 + R * (j.2 + 1) - z.im := min_le_right _ _
        _ ≤ s₂ + 1 := by linarith

end Lower

end Sphere

end SandierSerfaty

end
