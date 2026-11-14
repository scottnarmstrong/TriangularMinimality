/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.JetExplicit
public import SandierSerfaty.Tails.RetainedCore
public import SandierSerfaty.Tails.WeightedSum
public import SandierSerfaty.Tails.PropBlocks

/-!
# `Q_i` on a spline piece: jets and norms (paper §6.5)

For `j ≤ 5` the piece `Piece.D i j` is smooth on `(0, ∞)`, so `Q_i = t D_i' - k_i D_i` has the explicit jet
`(qP0, qP1, qP2)` there:
`qP0 = t D' - k D`, `qP1 = t D'' + (1 - k) D'`, `qP2 = t D''' + (2 - k) D''` (derivatives of the piece), with
`|Q_i|_{2,t} ≤ 2 (k_i + 1) |D_i|_{3,t}` for `0 < t ≤ 1` (`jn_qP_le`), `|D|_{3,t} = pnormD j i t`.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem contDiffOn_PD (i j n : ℕ) : ContDiffOn ℝ n (Piece.D i j) (Ioi 0) :=
  (contDiffOn_Piece_D i j).of_le (by exact_mod_cast le_top)

/-- The piece `Piece.D i j` and its first two (iterated) derivatives are differentiable on `(0, ∞)`. -/
theorem hasDerivAt_iter_PD (i j n : ℕ) (hn : n ≤ 2) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDeriv n (Piece.D i j)) (iteratedDeriv (n + 1) (Piece.D i j) t) t := by
  have h3 := contDiffOn_PD i j 3
  have h2 : ContDiffOn ℝ 2 (deriv (Piece.D i j)) (Ioi 0) := h3.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ContDiffOn ℝ 1 (deriv (deriv (Piece.D i j))) (Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have mem : Ioi (0 : ℝ) ∈ nhds t := isOpen_Ioi.mem_nhds ht
  interval_cases n
  · simp only [iteratedDeriv_zero, zero_add, iteratedDeriv_one]
    exact ((h3.contDiffAt mem).differentiableAt (by norm_num)).hasDerivAt
  · simp only [iteratedDeriv_succ]
    exact ((h2.contDiffAt mem).differentiableAt (by norm_num)).hasDerivAt
  · rw [iteratedDeriv_succ (n := 2), iteratedDeriv_succ (n := 1), iteratedDeriv_one]
    exact ((h1.contDiffAt mem).differentiableAt (by norm_num)).hasDerivAt

theorem iter2_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

theorem iter3_eq (f : ℝ → ℝ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, iter2_eq]

theorem hasDerivAt_PD0 (i j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Piece.D i j) (iteratedDeriv 1 (Piece.D i j) t) t := by
  simpa using hasDerivAt_iter_PD i j 0 (by norm_num) ht

theorem hasDerivAt_PD1 (i j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDeriv 1 (Piece.D i j)) (iteratedDeriv 2 (Piece.D i j) t) t :=
  hasDerivAt_iter_PD i j 1 (by norm_num) ht

theorem hasDerivAt_PD2 (i j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (iteratedDeriv 2 (Piece.D i j)) (iteratedDeriv 3 (Piece.D i j) t) t :=
  hasDerivAt_iter_PD i j 2 (by norm_num) ht

/-- `Q_i = t D_i' - k_i D_i` for the piece `j`. -/
@[expose] noncomputable def qP0 (i j : ℕ) (t : ℝ) : ℝ :=
  t * iteratedDeriv 1 (Piece.D i j) t - (k i : ℝ) * Piece.D i j t

/-- `Q_i' = t D_i'' + (1 - k_i) D_i'`. -/
@[expose] noncomputable def qP1 (i j : ℕ) (t : ℝ) : ℝ :=
  t * iteratedDeriv 2 (Piece.D i j) t + (1 - (k i : ℝ)) * iteratedDeriv 1 (Piece.D i j) t

/-- `Q_i'' = t D_i''' + (2 - k_i) D_i''`. -/
@[expose] noncomputable def qP2 (i j : ℕ) (t : ℝ) : ℝ :=
  t * iteratedDeriv 3 (Piece.D i j) t + (2 - (k i : ℝ)) * iteratedDeriv 2 (Piece.D i j) t

theorem jet_qP (i j : ℕ) : Jet2 (Ioi 0) (Ioi 0) (qP0 i j) (qP1 i j) (qP2 i j) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, subset_rfl⟩
  · have ht' : (0 : ℝ) < t := ht
    have h := ((hasDerivAt_id' t).mul (hasDerivAt_PD1 i j ht')).sub
      ((hasDerivAt_PD0 i j ht').const_mul (k i : ℝ))
    exact h.congr_deriv (by unfold qP1; ring)
  · have ht' : (0 : ℝ) < t := ht
    have h := ((hasDerivAt_id' t).mul (hasDerivAt_PD2 i j ht')).add
      ((hasDerivAt_PD1 i j ht').const_mul (1 - (k i : ℝ)))
    exact h.congr_deriv (by unfold qP2; ring)

theorem jn_qP_le (i j : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    jn (qP0 i j) (qP1 i j) (qP2 i j) t ≤ 2 * ((k i : ℝ) + 1) * pnormD j i t := by
  have hk : (6 : ℝ) ≤ k i := by exact_mod_cast k_ge_six i
  set d0 := |Piece.D i j t| with hd0
  set d1 := |iteratedDeriv 1 (Piece.D i j) t| with hd1
  set d2 := |iteratedDeriv 2 (Piece.D i j) t| with hd2
  set d3 := |iteratedDeriv 3 (Piece.D i j) t| with hd3
  have n0 : 0 ≤ d0 := abs_nonneg _
  have n1 : 0 ≤ d1 := abs_nonneg _
  have n2 : 0 ≤ d2 := abs_nonneg _
  have n3 : 0 ≤ d3 := abs_nonneg _
  have a0 : |qP0 i j t| ≤ t * d1 + (k i : ℝ) * d0 := by
    unfold qP0
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ k i)]
  have a1 : |qP1 i j t| ≤ t * d2 + ((k i : ℝ) - 1) * d1 := by
    unfold qP1
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonpos (by linarith : 1 - (k i : ℝ) ≤ 0)]
    linarith
  have a2 : |qP2 i j t| ≤ t * d3 + ((k i : ℝ) - 2) * d2 := by
    unfold qP2
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonpos (by linarith : 2 - (k i : ℝ) ≤ 0)]
    linarith
  have b1 : t * d1 ≤ d1 := mul_le_of_le_one_left n1 ht1
  have b2 : t * d2 ≤ d2 := mul_le_of_le_one_left n2 ht1
  have b3 : t * d3 ≤ d3 := mul_le_of_le_one_left n3 ht1
  have hp : pnormD j i t = d0 + d1 + d2 / 2 + d3 / 6 := rfl
  unfold jn
  rw [hp]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ) + 2) n0,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ) + 2) n1,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ)) n2, mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ) - 3) n3]

theorem je_qP (i j : ℕ) :
    JE (Ioi 0) (Ioc 0 1) (qP0 i j) (qP1 i j) (qP2 i j) (fun t => 2 * ((k i : ℝ) + 1) * pnormD j i t) :=
  ⟨jet_qP i j, fun _ ht => jn_qP_le i j ht.1 ht.2⟩

end Tails

end SandierSerfaty

end
