/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropEPiece
public import SandierSerfaty.Tails.TailSums

/-!
# The off-block terms of `e - ẽ` on a spline piece (paper `tail:e-estimate`)

`e - ẽ = ½ ∑_{(i,k) ∉ [0,38]²} Q_i Q_k/(k_i + k_k)`. On the piece `j ≤ 5` the terms have the explicit jets
`(rP0, rP1, rP2)` (`JE`), valid on the open interior `Vg j` of the segment `seg j` with the bound holding on the
closed `Sg j ⊆ seg j`. Sharp bound on `seg j ∩ [b, l]` (`rest_tsum_sharp`): from the finite-core premise
`∑_{i ≤ 38} (k_i+1)³ |D_i|_{3,t} < 2·10⁶` and `∑_{i ≥ 39} (k_i+1)|D_i|_{3,t} ≤ (8/3) 𝔞` with `(8/3) = 1+1+1/2+1/6`.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem pnormD_nonneg (j i : ℕ) (t : ℝ) : 0 ≤ pnormD j i t := by unfold pnormD; positivity

theorem continuousOn_pnormD (i j : ℕ) : ContinuousOn (pnormD j i) (Ioi 0) := by
  have h3 := contDiffOn_PD i j 3
  have h2 : ContDiffOn ℝ 2 (deriv (Piece.D i j)) (Ioi 0) := h3.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ContDiffOn ℝ 1 (deriv (deriv (Piece.D i j))) (Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h0 : ContDiffOn ℝ 0 (deriv (deriv (deriv (Piece.D i j)))) (Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have c0 := h3.continuousOn
  have c1 := h2.continuousOn
  have c2 := h1.continuousOn
  have c3 := h0.continuousOn
  unfold pnormD
  simp only [iteratedDeriv_one, iter2_eq, iter3_eq]
  exact (((continuous_abs.comp_continuousOn c0).add (continuous_abs.comp_continuousOn c1)).add
    ((continuous_abs.comp_continuousOn c2).div_const 2)).add ((continuous_abs.comp_continuousOn c3).div_const 6)

/-! ### The terms -/

/-- `1/(k_i + k_k)`. -/
@[expose] noncomputable def cc (ij : ℕ × ℕ) : ℝ := 1 / ((k ij.1 : ℝ) + (k ij.2 : ℝ))

theorem abs_cc_le (ij : ℕ × ℕ) : |cc ij| ≤ 1 := by
  have h1 : (6 : ℝ) ≤ k ij.1 := by exact_mod_cast k_ge_six _
  have h2 : (6 : ℝ) ≤ k ij.2 := by exact_mod_cast k_ge_six _
  unfold cc
  rw [abs_of_pos (by positivity), div_le_one (by positivity)]
  linarith

/-- The term `Q_i Q_k/(k_i + k_k)` of the piece `j` and its two derivatives. -/
@[expose] noncomputable def tP0 (j : ℕ) (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  cc ij * (qP0 ij.1 j t * qP0 ij.2 j t)

@[expose] noncomputable def tP1 (j : ℕ) (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  cc ij * mul₁ (qP0 ij.1 j) (qP1 ij.1 j) (qP0 ij.2 j) (qP1 ij.2 j) t

@[expose] noncomputable def tP2 (j : ℕ) (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  cc ij * mul₂ (qP0 ij.1 j) (qP1 ij.1 j) (qP2 ij.1 j) (qP0 ij.2 j) (qP1 ij.2 j) (qP2 ij.2 j) t

/-- The same terms off the retained block `[0, 38]²`, `0` on it. -/
@[expose] noncomputable def rP0 (j : ℕ) (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0 else tP0 j ij t

@[expose] noncomputable def rP1 (j : ℕ) (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0 else tP1 j ij t

@[expose] noncomputable def rP2 (j : ℕ) (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0 else tP2 j ij t

/-- The bound `2 (k_i + 1) |D_i|_{3,t}` of `|Q_i|_{2,t}`. -/
@[expose] noncomputable def qb (j : ℕ) (t : ℝ) (i : ℕ) : ℝ := 2 * ((k i : ℝ) + 1) * pnormD j i t

theorem qb_nonneg (j : ℕ) (t : ℝ) (i : ℕ) : 0 ≤ qb j t i := by
  unfold qb; have := pnormD_nonneg j i t; positivity

theorem je_tP (j : ℕ) (ij : ℕ × ℕ) :
    JE (Ioi 0) (Ioc 0 1) (tP0 j ij) (tP1 j ij) (tP2 j ij) (fun t => |cc ij| * (qb j t ij.1 * qb j t ij.2)) :=
  ((je_qP ij.1 j).mul (je_qP ij.2 j)).const_mul (cc ij)

theorem je_rP (j : ℕ) (ij : ℕ × ℕ) :
    JE (Ioi 0) (Ioc 0 1) (rP0 j ij) (rP1 j ij) (rP2 j ij) (fun t => rest (qb j t) ij) := by
  by_cases h : ij.1 < 39 ∧ ij.2 < 39
  · have e0 : rP0 j ij = fun _ => 0 := by funext t; simp [rP0, h]
    have e1 : rP1 j ij = fun _ => 0 := by funext t; simp [rP1, h]
    have e2 : rP2 j ij = fun _ => 0 := by funext t; simp [rP2, h]
    rw [e0, e1, e2]
    refine (JE.const (U := Ioi 0) (S := Ioc 0 1) 0).mono_bound fun t _ => ?_
    simpa using rest_nonneg (qb_nonneg j t) ij
  · have e0 : rP0 j ij = tP0 j ij := by funext t; simp [rP0, h]
    have e1 : rP1 j ij = tP1 j ij := by funext t; simp [rP1, h]
    have e2 : rP2 j ij = tP2 j ij := by funext t; simp [rP2, h]
    rw [e0, e1, e2]
    refine (je_tP j ij).mono_bound fun t _ => ?_
    have hq1 := qb_nonneg j t ij.1
    have hq2 := qb_nonneg j t ij.2
    simp only [rest, ite_eq_right h]
    calc |cc ij| * (qb j t ij.1 * qb j t ij.2) ≤ 1 * (qb j t ij.1 * qb j t ij.2) :=
          mul_le_mul_of_nonneg_right (abs_cc_le ij) (by positivity)
      _ = _ := one_mul _

/-! ### Majorants -/

theorem exists_CP (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i < 39, ∀ t ∈ Icc (b / 2) 1, qb j t i ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_finite (isCompact_Icc (a := b / 2) (b := 1)) 39
    (F := fun i t => qb j t i) (fun i _ => by
      unfold qb
      exact continuousOn_const.mul ((continuousOn_pnormD i j).mono fun t ht =>
        lt_of_lt_of_le (by have := b_pos; positivity) ht.1))
  exact ⟨C, hC0, fun i hi t ht => (le_abs_self _).trans (hC i hi t ht)⟩

/-- A uniform bound of `2 (k_i + 1) |D_i|_{3,t}`, `i ≤ 38`, `t ∈ [b/2, 1]` (convergence only). -/
@[expose] noncomputable def CP (j : ℕ) : ℝ := Classical.choose (exists_CP j)

theorem CP_nonneg (j : ℕ) : 0 ≤ CP j := (Classical.choose_spec (exists_CP j)).1

theorem qb_le_CP {j i : ℕ} (hi : i < 39) {t : ℝ} (ht : t ∈ Icc (b / 2) 1) : qb j t i ≤ CP j :=
  (Classical.choose_spec (exists_CP j)).2 i hi t ht

/-- The majorant of `qb j t i` valid on `Sg j`. -/
@[expose] noncomputable def mq3 (j i : ℕ) : ℝ :=
  if i < 39 then CP j else 2 * ((k i : ℝ) + 1) * (8 / 3 * wk (k i))

theorem mq3_nonneg (j i : ℕ) : 0 ≤ mq3 j i := by
  unfold mq3; have := CP_nonneg j; have := wk_nonneg (k i); split_ifs <;> positivity

theorem mq3_tail (j j' : ℕ) : mq3 j (j' + 39) = 16 / 3 * wt 1 j' := by
  unfold mq3 wt
  rw [ite_eq_right (by omega), k_tail]
  ring

theorem summable_mq3 (j : ℕ) : Summable (mq3 j) := by
  rw [← summable_nat_add_iff 39]
  simp_rw [mq3_tail]
  exact (summable_wt (by norm_num)).mul_left _

theorem pnormD_tail {j : ℕ} (hj : j ≤ 5) (j' : ℕ) {t : ℝ} (ht : t ∈ seg j) :
    pnormD j (j' + 39) t ≤ 8 / 3 * wk (kk j') := by
  obtain ⟨-, ⟨D0, D1, D2, D3⟩⟩ := piece_derivs_le (m := j' + 39) (by omega) hj ht
  rw [k_tail] at D0 D1 D2 D3
  have hp : pnormD j (j' + 39) t =
      |Piece.D (j' + 39) j t| + |iteratedDeriv 1 (Piece.D (j' + 39) j) t| +
        |iteratedDeriv 2 (Piece.D (j' + 39) j) t| / 2 + |iteratedDeriv 3 (Piece.D (j' + 39) j) t| / 6 := rfl
  rw [hp]
  linarith

theorem qb_le_mq3 {j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j ∩ Icc (b / 2) 1) (i : ℕ) :
    qb j t i ≤ mq3 j i := by
  unfold mq3
  split_ifs with h
  · exact qb_le_CP h ht.2
  · obtain ⟨j', rfl⟩ : ∃ j', i = j' + 39 := ⟨i - 39, by omega⟩
    unfold qb
    rw [k_tail]
    exact mul_le_mul_of_nonneg_left (pnormD_tail hj j' ht.1) (by positivity)

/-! ### The sets -/

/-- The closed set on which the bounds hold (`seg j` cut to `[b/2, 1]`). -/
@[expose] def Sg (j : ℕ) : Set ℝ := seg j ∩ Icc (b / 2) 1

/-- The open interior of the segment inside `(b/2, 1)`. -/
@[expose] def Vg (j : ℕ) : Set ℝ := interior (seg j) ∩ Ioo (b / 2) 1

theorem Sg_subset_Ioc (j : ℕ) : Sg j ⊆ Ioc 0 1 := fun t ht =>
  ⟨lt_of_lt_of_le (by have := b_pos; positivity) ht.2.1, ht.2.2⟩

theorem Vg_subset_Sg (j : ℕ) : Vg j ⊆ Sg j := fun _ ht => ⟨interior_subset ht.1, ht.2.1.le, ht.2.2.le⟩

theorem Vg_subset_Ioi (j : ℕ) : Vg j ⊆ Ioi 0 := fun t ht =>
  lt_of_lt_of_le (by have := b_pos; positivity) ht.2.1.le

theorem isOpen_Vg (j : ℕ) : IsOpen (Vg j) := isOpen_interior.inter isOpen_Ioo

theorem convex_seg (j : ℕ) : Convex ℝ (seg j) := by
  match j with
  | 0 => exact convex_Ioc _ _
  | 1 => exact convex_Icc _ _
  | 2 => exact convex_Icc _ _
  | 3 => exact convex_Icc _ _
  | 4 => exact convex_Icc _ _
  | 5 => exact convex_Icc _ _
  | n + 6 => exact convex_Ici _

theorem isPreconnected_Vg (j : ℕ) : IsPreconnected (Vg j) :=
  ((convex_seg j).interior.inter (convex_Ioo _ _)).isPreconnected

theorem je_rP_tsum (j : ℕ) (hj : j ≤ 5) :
    JE (Vg j) (Sg j) (fun x => ∑' ij, rP0 j ij x) (fun x => ∑' ij, rP1 j ij x) (fun x => ∑' ij, rP2 j ij x)
      (fun t => ∑' ij, rest (qb j t) ij) := by
  refine JE.tsum (isOpen_Vg j) (isPreconnected_Vg j) (Vg_subset_Sg j)
    (fun ij => (je_rP j ij).mono_set (Vg_subset_Ioi j) (Sg_subset_Ioc j))
    (summable_rest (mq3_nonneg j) (summable_mq3 j)) fun ij t ht => ?_
  exact rest_mono (qb_nonneg j t) (qb_le_mq3 hj ht) ij

/-! ### The sharp bound -/

theorem rest_tsum_sharp (hc : FiniteCore) {j : ℕ} (hj : j ≤ 5) {t : ℝ} (hts : t ∈ seg j) (h1 : b ≤ t)
    (h2 : t ≤ l) :
    ∑' ij, rest (qb j t) ij ≤ 2 * 4000000 * (16 / 3 * aa) + (16 / 3 * aa) ^ 2 := by
  have htS : t ∈ seg j ∩ Icc (b / 2) 1 :=
    ⟨hts, by have := b_pos; linarith, by have := l_lt; linarith⟩
  have hqs : Summable (qb j t) :=
    Summable.of_nonneg_of_le (qb_nonneg j t) (qb_le_mq3 hj htS) (summable_mq3 j)
  rw [tsum_rest (qb_nonneg j t) hqs]
  have hA : ∑ i ∈ Finset.range 39, qb j t i ≤ 4000000 := by
    have hcore := hc.D_lt j hj t hts h1 h2
    have : ∑ i ∈ Finset.range 39, qb j t i ≤ 2 * ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 * pnormD j i t := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      unfold qb
      have h0 := pnormD_nonneg j i t
      have hk : (0 : ℝ) ≤ k i := by positivity
      have : (k i : ℝ) + 1 ≤ ((k i : ℝ) + 1) ^ 3 := by nlinarith [mul_nonneg hk hk, mul_nonneg hk (mul_nonneg hk hk)]
      calc 2 * ((k i : ℝ) + 1) * pnormD j i t = 2 * (((k i : ℝ) + 1) * pnormD j i t) := by ring
        _ ≤ 2 * (((k i : ℝ) + 1) ^ 3 * pnormD j i t) := by gcongr
    linarith
  have hA0 : 0 ≤ ∑ i ∈ Finset.range 39, qb j t i := Finset.sum_nonneg fun i _ => qb_nonneg j t i
  have hqt : Summable fun j' => qb j t (j' + 39) := (summable_nat_add_iff 39).2 hqs
  have hs1 : Summable fun j' => 16 / 3 * wt 1 j' := (summable_wt (by norm_num)).mul_left _
  have hT : ∑' j', qb j t (j' + 39) ≤ 16 / 3 * aa := by
    have h := Summable.tsum_le_tsum (f := fun j' => qb j t (j' + 39)) (g := fun j' => 16 / 3 * wt 1 j')
      (fun j' => ?_) hqt hs1
    · rw [tsum_mul_left] at h
      have := tsum_wt_le (s := 1) (by norm_num)
      linarith
    · have h3 := pnormD_tail hj j' hts
      unfold qb wt
      rw [k_tail]
      have := wk_nonneg (kk j')
      have hk : (0 : ℝ) ≤ kk j' := by positivity
      calc 2 * ((kk j' : ℝ) + 1) * pnormD j (j' + 39) t ≤ 2 * ((kk j' : ℝ) + 1) * (8 / 3 * wk (kk j')) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 16 / 3 * (((kk j' : ℝ) + 1) ^ 1 * wk (kk j')) := by ring
  have hT0 : 0 ≤ ∑' j', qb j t (j' + 39) := tsum_nonneg fun j' => qb_nonneg j t _
  nlinarith [mul_nonneg hA0 hT0, mul_nonneg hT0 hT0, mul_nonneg (sub_nonneg.2 hA) hT0]

end Tails

end SandierSerfaty

end
