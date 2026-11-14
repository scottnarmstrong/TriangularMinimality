/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ColumnMass

/-!
# Column cuts with carries (screening note, Lemma 4.18)

The screening note, Lemma 4.18 (`lem:cuts`) with the justification that
the strip bound for `g̃^{(j)}` is Lemma 4.17 with `κ = 0` on the non-last columns.

Under `Pinwheel.CutHyp` (the hypotheses on the soft-cut source `g`), `Pinwheel.exists_columnCut`
produces column partitions `0 = u_j 0 < ⋯ < u_j K_j = L` of the four rectangles `R_j` and carries
`θ_0, θ_1, θ_2 ∈ [0, 1)`, `θ_3 = 0` (`Pinwheel.ColumnCut`), such that, with `w'_j` the width of the last
column of `R_j` and `g̃ = g - ∑_j (2πθ_j/w'_j)(1_{A_j} - 1_{A'_j})` (`ColumnCut.src`):

* (a) all columns have width in `[ℓc, 2ℓc]` except the last of each `R_j`, in `[ℓc, 3ℓc)`;
* (b) every column has `g̃`-mass `2π n_k` with `n_k ∈ ℕ`, `n_k ≥ 1`, and `∑ n_k = n_tot`
  (`ColumnCut.IsCut`);
* (c) `ColumnCut.carryA_subset_top`, `ColumnCut.carryA'_subset_bottom`,
  `ColumnCut.sqDepth_le_of_mem_carryRect` (the carry cells lie in `O_- ∩ {δ ≤ 3ℓc}`),
  `ColumnCut.src_bottom` (`g̃ = 2πm + κ_{j-1} 1_{A'_{j-1}}` a.e. on the bottom parts) and
  `ColumnCut.kappa_mem` (`κ_j = 2πθ_j/w'_j ∈ [0, 2π/ℓc]`);
* (d) `ColumnCut.abs_integral_top_le` (`|∫_{T_I} g̃| ≤ (π/2)mwℓc`) and `ColumnCut.col_mass_ge`
  (`(2π)⁻¹ ∫_{Ψ_j(I × [0, w_f])} g̃ ≥ 6mwℓc`) for every `I ⊆ [0, L]` with `|I| ∈ [ℓc, 3ℓc]`.

The construction runs over `R_0, R_1, R_2, R_3` in turn: the cumulative mass of `R_j` includes the
incoming carry `θ_{j-1}` (spread on `A'_{j-1}`), the non-last cuts are chosen by the intermediate value
theorem (`exists_partition`), the fractional part of the last column's mass is carried to `R_{j+1}`,
and for `R_3` the integrality of the last column follows from `∫_F g = 2π n_tot`.
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty.Screening.Pinwheel

/-- The data of a column cut: `K_j` columns of `R_j`, cut at `u_j 0 < ⋯ < u_j K_j`, and carries
`θ_j`. -/
structure ColumnCut where
  /-- number of columns of `R_j` -/
  K : Fin 4 → ℕ
  /-- cut points of `R_j` -/
  u : Fin 4 → ℕ → ℝ
  /-- the carries -/
  θ : Fin 4 → ℝ

namespace ColumnCut

variable (C : ColumnCut)

/-- The width `w'_j = u_j(K_j) - u_j(K_j - 1)` of the last column of `R_j`. -/
@[expose] def lastWidth (j : Fin 4) : ℝ := C.u j (C.K j) - C.u j (C.K j - 1)

/-- The `k`-th column `Col_k = Ψ_j([u_k, u_{k+1}] × [0, w_f])` of `R_j` (`k < K_j`). -/
@[expose] def col (c : ℂ) (t d : ℝ) (j : Fin 4) (k : ℕ) : Set ℂ :=
  (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d + 8))

/-- The source with carries `g̃` of the cut `C`. -/
@[expose] noncomputable def src (c : ℂ) (t d : ℝ) (g : ℂ → ℝ) : ℂ → ℝ :=
  tildeG c t d g C.θ C.lastWidth

/-- The carry density `κ_j = 2πθ_j / w'_j`. -/
@[expose] noncomputable def kappa (j : Fin 4) : ℝ := 2 * π * C.θ j / C.lastWidth j

/-- **The screening note's Lemma 4.18(a),(b)**: the conclusion of the column cut. -/
structure IsCut (c : ℂ) (t d ℓ : ℝ) (g : ℂ → ℝ) (ntot : ℤ) : Prop where
  partition : ∀ j, IsPartition ℓ 0 (side t d) (C.K j) (C.u j)
  θ_mem : ∀ j, C.θ j ∈ Ico (0 : ℝ) 1
  θ_three : C.θ 3 = 0
  mass : ∀ j k, k < C.K j → ∃ n : ℕ, 1 ≤ n ∧ ∫ z in C.col c t d j k, C.src c t d g z = 2 * π * n
  total : ∑ j, ∑ k ∈ Finset.range (C.K j), ∫ z in C.col c t d j k, C.src c t d g z = 2 * π * ntot

end ColumnCut

namespace CutHyp

variable {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {ntot : ℤ} (h : CutHyp c t d m ℓ g ntot)
include h

/-- `Λ_j(L) = (2π)⁻¹ ∫_{R_j} g + θ_{j-1}`. -/
theorem cumMass_side (j : Fin 4) (θp : ℝ) :
    cumMass c t d g j θp (side t d) = (2 * π)⁻¹ * (∫ z in (rect c t d j).carrier, g z) + θp := by
  have := h.cumMass_sub j θp le_rfl h.side_pos.le le_rfl
  rw [cumMass_zero, sub_zero, min_eq_right (by linarith [h.side_ge, h.K4]), min_eq_left zero_le_one,
    sub_zero, mul_one] at this
  rw [this, Rect.carrier_eq_box, rect_width, rect_height]

/-- **`g̃` on the columns of a partition of `R_j`**: the mass of `Col_k` is the increment of `Λ_j`,
minus the outgoing carry `2πθ_j` on the last column. -/
theorem integral_col_tildeG_of_partition (j : Fin 4) {θ w : Fin 4 → ℝ}
    (hw : ∀ i, w i ∈ Icc ℓ (3 * ℓ)) {K : ℕ} {u : ℕ → ℝ} (hP : IsPartition ℓ 0 (side t d) K u)
    (hwj : w j = side t d - u (K - 1)) {k : ℕ} (hk : k < K) :
    ∫ z in (rect c t d j).box (Icc (u k) (u (k + 1))) (Icc 0 (d + 8)), tildeG c t d g θ w z =
      2 * π * (cumMass c t d g j (θ (j - 1)) (u (k + 1)) - cumMass c t d g j (θ (j - 1)) (u k)) -
        (if k + 1 = K then 2 * π * θ j else 0) := by
  have hℓ := h.ℓ_pos
  have hw' : ∀ i, w i ∈ Icc 0 (3 * ℓ) := fun i => ⟨hℓ.le.trans (hw i).1, (hw i).2⟩
  have huk := hP.mem_Icc hℓ.le hk.le
  have huk1 := hP.mem_Icc hℓ.le (Nat.succ_le_of_lt hk)
  have hle : u k ≤ u (k + 1) := hP.mono hℓ.le (Nat.le_succ k) (Nat.succ_le_of_lt hk)
  rw [h.integral_col_tildeG j hw' huk.1 huk1.2, volume_real_Icc_inter_Icc_zero_one huk.1 hle]
  have hcm := h.cumMass_sub j (θ (j - 1)) huk.1 hle huk1.2
  have hwpos : w (j - 1) ≠ 0 := (hℓ.trans_le (hw (j - 1)).1).ne'
  have hwjpos : w j ≠ 0 := (hℓ.trans_le (hw j).1).ne'
  have hAj : volume.real (Icc (u k) (u (k + 1)) ∩ Icc (side t d - w j) (side t d)) =
      if k + 1 = K then w j else 0 := by
    split_ifs with hkK
    · have hk' : k = K - 1 := by omega
      have e1 : u (k + 1) = side t d := by rw [hkK, hP.last]
      have e2 : side t d - w j = u k := by rw [hwj, sub_sub_cancel, hk']
      rw [e1, e2, inter_self, Real.volume_real_Icc, max_eq_left (by linarith [huk.2]), hwj, hk']
    · have hlt : k + 1 ≤ K - 1 := by omega
      have h1 : u (k + 1) ≤ side t d - w j := by
        rw [hwj, sub_sub_cancel]; exact hP.le_pred_last hℓ.le hlt
      rw [Icc_inter_Icc, Real.volume_real_Icc, max_eq_right]
      linarith [min_le_left (u (k + 1)) (side t d), le_max_right (u k) (side t d - w j)]
  have e1 : 2 * π * θ (j - 1) / w (j - 1) * ((min (u (k + 1)) 1 - min (u k) 1) * w (j - 1)) =
      2 * π * θ (j - 1) * (min (u (k + 1)) 1 - min (u k) 1) := by
    field_simp
  have e2 : 2 * π * θ j / w j * w j = 2 * π * θ j := by field_simp
  have hcm' : ∫ z in (rect c t d j).box (Icc (u k) (u (k + 1))) (Icc 0 (d + 8)), g z =
      2 * π * (cumMass c t d g j (θ (j - 1)) (u (k + 1)) - cumMass c t d g j (θ (j - 1)) (u k)) -
        2 * π * θ (j - 1) * (min (u (k + 1)) 1 - min (u k) 1) := by
    rw [hcm]; field_simp; ring
  rw [hAj, e1]
  split_ifs
  · rw [e2, hcm']; ring
  · rw [mul_zero, hcm']; ring

/-- The `g̃`-mass of all columns of `R_j`: `∑_k ∫_{Col_k} g̃ = 2π Λ_j(L) - 2πθ_j`. -/
theorem sum_integral_col_tildeG (j : Fin 4) {θ w : Fin 4 → ℝ}
    (hw : ∀ i, w i ∈ Icc ℓ (3 * ℓ)) {K : ℕ} {u : ℕ → ℝ} (hP : IsPartition ℓ 0 (side t d) K u)
    (hwj : w j = side t d - u (K - 1)) :
    ∑ k ∈ Finset.range K,
        ∫ z in (rect c t d j).box (Icc (u k) (u (k + 1))) (Icc 0 (d + 8)), tildeG c t d g θ w z =
      2 * π * cumMass c t d g j (θ (j - 1)) (side t d) - 2 * π * θ j := by
  rw [Finset.sum_congr rfl fun k hk =>
    h.integral_col_tildeG_of_partition j hw hP hwj (Finset.mem_range.1 hk),
    Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k => cumMass c t d g j (θ (j - 1)) (u k)), hP.last, hP.zero,
    cumMass_zero, sub_zero]
  congr 1
  have hK1 := hP.one_le
  rw [Finset.sum_eq_single (K - 1)]
  · simp [show K - 1 + 1 = K by omega]
  · intro k hk hne
    simp [show ¬(k + 1 = K) by omega]
  · intro hK
    exact absurd (Finset.mem_range.2 (by have := hP.one_le; omega)) hK

/-- The total `g̃`-mass: `∑_j ∑_k ∫_{Col_k} g̃ = 2π n_tot` (for any column partitions and any
carries; the carries cancel). -/
theorem total_of_partition (C : ColumnCut)
    (hP : ∀ j, IsPartition ℓ 0 (side t d) (C.K j) (C.u j))
    (hw : ∀ i, C.lastWidth i ∈ Icc ℓ (3 * ℓ)) :
    ∑ j, ∑ k ∈ Finset.range (C.K j), ∫ z in C.col c t d j k, C.src c t d g z = 2 * π * ntot := by
  have hwj : ∀ j, C.lastWidth j = side t d - C.u j (C.K j - 1) := fun j => by
    rw [ColumnCut.lastWidth, (hP j).last]
  simp only [ColumnCut.col, ColumnCut.src]
  rw [Finset.sum_congr rfl fun j _ => h.sum_integral_col_tildeG j hw (hP j) (hwj j)]
  simp only [h.cumMass_side, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hθ : ∑ j : Fin 4, 2 * π * C.θ (j - 1) = ∑ j : Fin 4, 2 * π * C.θ j :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ fun j => rfl
  rw [hθ, add_sub_cancel_right]
  have hπ : (2 * π) ≠ 0 := by positivity
  simp only [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
  rw [← integral_frameSet_eq_sum h.offset_pos h.integrableOn, h.total]

/-- **Masses from integrality** (screening note, Lemma 4.18(b)): if `Λ_j` has integer increments on the
non-last columns and the last column's mass minus `θ_j` is an integer, all column masses are positive
multiples of `2π`. -/
theorem mass_of_partition (C : ColumnCut)
    (hP : ∀ j, IsPartition ℓ 0 (side t d) (C.K j) (C.u j)) (hθ : ∀ j, C.θ j ∈ Ico (0 : ℝ) 1)
    (hI : ∀ j k, k + 1 < C.K j → ∃ z : ℤ,
      cumMass c t d g j (C.θ (j - 1)) (C.u j (k + 1)) - cumMass c t d g j (C.θ (j - 1)) (C.u j k) = z)
    (hlast : ∀ j, ∃ z : ℤ, cumMass c t d g j (C.θ (j - 1)) (side t d) -
      cumMass c t d g j (C.θ (j - 1)) (C.u j (C.K j - 1)) - C.θ j = z)
    (j : Fin 4) (k : ℕ) (hk : k < C.K j) :
    ∃ n : ℕ, 1 ≤ n ∧ ∫ z in C.col c t d j k, C.src c t d g z = 2 * π * n := by
  have hℓ := h.ℓ_pos
  have hw : ∀ i, C.lastWidth i ∈ Icc ℓ (3 * ℓ) := fun i => by
    have := (hP i).stepLast; exact ⟨this.1, this.2.le⟩
  have hwj : C.lastWidth j = side t d - C.u j (C.K j - 1) := by
    rw [ColumnCut.lastWidth, (hP j).last]
  have hθp : 0 ≤ C.θ (j - 1) := (hθ (j - 1)).1
  -- the increment over column `k` is at least `1`
  have hstep := (hP j).step_mem hℓ.le (Nat.succ_le_of_lt hk)
  have huk := (hP j).mem_Icc hℓ.le hk.le
  have hge := h.cumMass_sub_ge j hθp (x := C.u j k) (w := C.u j (k + 1) - C.u j k) huk.1
    (by rw [add_sub_cancel]; exact ((hP j).mem_Icc hℓ.le (Nat.succ_le_of_lt hk)).2) hstep
  rw [add_sub_cancel] at hge
  have hmwl : 0 ≤ 6 * m * (C.u j (k + 1) - C.u j k) * ℓ := by
    have hm := h.m_pos
    have : 0 ≤ C.u j (k + 1) - C.u j k := by linarith [hstep.1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm.le) this) hℓ.le
  simp only [ColumnCut.col, ColumnCut.src]
  rw [h.integral_col_tildeG_of_partition j hw (hP j) hwj hk]
  split_ifs with hkK
  · obtain ⟨z, hz⟩ := hlast j
    have hk' : k = C.K j - 1 := by omega
    have e1 : C.u j (k + 1) = side t d := by rw [hkK, (hP j).last]
    have e2 : C.u j k = C.u j (C.K j - 1) := by rw [hk']
    rw [e1, e2] at hge hmwl ⊢
    have hθ1 := (hθ j).2
    have hz1 : (0 : ℝ) < z := by linarith
    have hz1' : 0 < z := by exact_mod_cast hz1
    refine ⟨z.toNat, by omega, ?_⟩
    rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg (by omega), ← hz]
    ring
  · obtain ⟨z, hz⟩ := hI j k (by omega)
    have hz1 : (1 : ℝ) ≤ z := by rw [← hz]; linarith
    have hz1' : 1 ≤ z := by exact_mod_cast hz1
    refine ⟨z.toNat, by omega, ?_⟩
    rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg (by omega), ← hz]
    ring

/-- **The column cut** (screening note, Lemma 4.18(a),(b)). -/
theorem exists_columnCut : ∃ C : ColumnCut, C.IsCut c t d ℓ g ntot := by
  have hℓ := h.ℓ_pos
  set L := side t d
  obtain ⟨K0, u0, P0, I0⟩ := h.exists_rect_cut 0 (le_refl (0 : ℝ))
  set M0 := cumMass c t d g 0 0 L - cumMass c t d g 0 0 (u0 (K0 - 1))
  obtain ⟨K1, u1, P1, I1⟩ := h.exists_rect_cut 1 (Int.fract_nonneg M0)
  set M1 := cumMass c t d g 1 (Int.fract M0) L - cumMass c t d g 1 (Int.fract M0) (u1 (K1 - 1))
  obtain ⟨K2, u2, P2, I2⟩ := h.exists_rect_cut 2 (Int.fract_nonneg M1)
  set M2 := cumMass c t d g 2 (Int.fract M1) L - cumMass c t d g 2 (Int.fract M1) (u2 (K2 - 1))
  obtain ⟨K3, u3, P3, I3⟩ := h.exists_rect_cut 3 (Int.fract_nonneg M2)
  set M3 := cumMass c t d g 3 (Int.fract M2) L - cumMass c t d g 3 (Int.fract M2) (u3 (K3 - 1))
  set C : ColumnCut := ⟨![K0, K1, K2, K3], ![u0, u1, u2, u3],
    ![Int.fract M0, Int.fract M1, Int.fract M2, 0]⟩ with hC
  have hP : ∀ j, IsPartition ℓ 0 L (C.K j) (C.u j) := by
    intro j; fin_cases j
    exacts [P0, P1, P2, P3]
  have hθ : ∀ j, C.θ j ∈ Ico (0 : ℝ) 1 := by
    intro j; fin_cases j
    exacts [⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨le_rfl, zero_lt_one⟩]
  have hI : ∀ j k, k + 1 < C.K j → ∃ z : ℤ,
      cumMass c t d g j (C.θ (j - 1)) (C.u j (k + 1)) -
        cumMass c t d g j (C.θ (j - 1)) (C.u j k) = z := by
    intro j; fin_cases j
    exacts [I0, I1, I2, I3]
  -- the integer parts of the cumulative masses at `u_j(K_j - 1)`
  have hZ : ∀ j, ∃ Z : ℤ, cumMass c t d g j (C.θ (j - 1)) (C.u j (C.K j - 1)) = Z := by
    intro j
    obtain ⟨Z, hZ⟩ := (hP j).exists_int_sub_of_int_steps (hI j)
    rw [(hP j).zero, cumMass_zero, sub_zero] at hZ
    exact ⟨Z, hZ⟩
  -- the identity `∑_j (Λ_j(L) - θ_j) = n_tot`
  have hsum : ∑ j, (cumMass c t d g j (C.θ (j - 1)) L - C.θ j) = ntot := by
    have hw : ∀ i, C.lastWidth i ∈ Icc ℓ (3 * ℓ) := fun i => by
      have := (hP i).stepLast; exact ⟨this.1, this.2.le⟩
    have htot := h.total_of_partition C hP hw
    have hwj : ∀ j, C.lastWidth j = L - C.u j (C.K j - 1) := fun j => by
      rw [ColumnCut.lastWidth, (hP j).last]
    simp only [ColumnCut.col, ColumnCut.src] at htot
    rw [Finset.sum_congr rfl fun j _ => h.sum_integral_col_tildeG j hw (hP j) (hwj j)] at htot
    have hπ : (2 * π) ≠ 0 := by positivity
    have : ∑ j : Fin 4, (2 * π * cumMass c t d g j (C.θ (j - 1)) L - 2 * π * C.θ j) =
        2 * π * ∑ j, (cumMass c t d g j (C.θ (j - 1)) L - C.θ j) := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [this] at htot
    exact mul_left_cancel₀ hπ htot
  have hlast : ∀ j, ∃ z : ℤ, cumMass c t d g j (C.θ (j - 1)) L -
      cumMass c t d g j (C.θ (j - 1)) (C.u j (C.K j - 1)) - C.θ j = z := by
    have h012 : ∀ j : Fin 4, j ≠ 3 → ∃ z : ℤ, cumMass c t d g j (C.θ (j - 1)) L -
        cumMass c t d g j (C.θ (j - 1)) (C.u j (C.K j - 1)) - C.θ j = z := by
      intro j hj
      fin_cases j
      · exact ⟨⌊M0⌋, by rw [← Int.self_sub_fract M0]; rfl⟩
      · exact ⟨⌊M1⌋, by rw [← Int.self_sub_fract M1]; rfl⟩
      · exact ⟨⌊M2⌋, by rw [← Int.self_sub_fract M2]; rfl⟩
      · exact absurd rfl hj
    intro j
    by_cases hj : j ≠ 3
    · exact h012 j hj
    push Not at hj
    subst hj
    obtain ⟨z0, hz0⟩ := h012 0 (by decide)
    obtain ⟨z1, hz1⟩ := h012 1 (by decide)
    obtain ⟨z2, hz2⟩ := h012 2 (by decide)
    obtain ⟨Z0, hZ0⟩ := hZ 0
    obtain ⟨Z1, hZ1⟩ := hZ 1
    obtain ⟨Z2, hZ2⟩ := hZ 2
    obtain ⟨Z3, hZ3⟩ := hZ 3
    refine ⟨ntot - (z0 + Z0) - (z1 + Z1) - (z2 + Z2) - Z3, ?_⟩
    rw [Fin.sum_univ_four] at hsum
    have e : (3 : Fin 4) - 1 = 2 := rfl
    rw [e] at hsum hZ3
    push_cast
    linear_combination hsum - hz0 - hz1 - hz2 - hZ0 - hZ1 - hZ2 - hZ3
  refine ⟨C, ⟨hP, hθ, rfl, h.mass_of_partition C hP hθ hI hlast, ?_⟩⟩
  exact h.total_of_partition C hP fun i => by
    have := (hP i).stepLast; exact ⟨this.1, this.2.le⟩

end CutHyp

end SandierSerfaty.Screening.Pinwheel

end
