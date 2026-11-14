/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.RetainedSmall
public import SandierSerfaty.Tails.IntegralJets

/-!
# The finite-core premise and bounds on all of `(0, ∞)` (paper `tail:finite-core-premise`)

The retained-mode bounds verified in §7 (`tail:finite-core-premise`) are the hypothesis `FiniteCore` of the
propagation: `|c_1| < 1`, `|B̃₁|_{2,t} < 6000` and `∑_{i ≤ 38} (k_i + 1)³ |D_i|_{3,t} <
2·10⁶` for `b ≤ t ≤ l`, with the norms of the paper (`tail:norms`) taken on the pieces `Piece.u i j`,
`Piece.D i j` of the segment `seg j ∋ t` (the one-sided derivatives at the knots: this is the form in which
the certificate proves them).

* `core_B₁`, `core_D`: the consequences for the splines (their derivatives on `seg j` are those of the pieces);
* `B₁_bound_all`: under `FiniteCore`, `|B̃₁| ≤ 6000` and `|B̃₁'| ≤ 6000` at every `t > 0` (`(0, b]` by
  `B₁_small`, `[b, l]` by the premise, and `B̃₁ = 1/t` beyond `l`);
* the `NearZero` (continuous on `(0, ∞)`, bounded near `0`) facts for the integrands of `S₁, S₂, H_k`.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The norm `|B̃₁|_{2,t}` of the piece `j` (paper §6.3, `tail:finite-core-premise`): `B̃₁ = ∑_{i ≤ 38} u_i' + 1/t` with the
one-sided derivatives of the pieces `Piece.u i j`; `(1/t)' = -1/t²`, `(1/t)'' = 2/t³`. -/
@[expose] noncomputable def pnormB₁ (j : ℕ) (t : ℝ) : ℝ :=
  |∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) t + 1 / t| +
    |∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t - 1 / t ^ 2| +
    |∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 / t ^ 3| / 2

/-- The norm `|D_i|_{3,t}` of the piece `j` (paper §6.3). -/
@[expose] noncomputable def pnormD (j i : ℕ) (t : ℝ) : ℝ :=
  |Piece.D i j t| + |iteratedDeriv 1 (Piece.D i j) t| + |iteratedDeriv 2 (Piece.D i j) t| / 2 +
    |iteratedDeriv 3 (Piece.D i j) t| / 6

/-- **The finite-core premise** `tail:finite-core-premise`, the source premise of
`tail:uniform-error`: it is supplied by the finite verification of §7, not by the analytic estimates of
§6. For every segment `j ≤ 5` and `t ∈ seg j ∩ [b, l]`: `|B̃₁|_{2,t} < 6000` and
`∑_{i=0}^{38} (k_i + 1)³ |D̃_i|_{3,t} < 2·10⁶`; and `|c_1| < 1`. -/
structure FiniteCore : Prop where
  abs_coeff_one : |coeff 1| < 1
  B₁_lt : ∀ j, j ≤ 5 → ∀ t ∈ seg j, b ≤ t → t ≤ l → pnormB₁ j t < 6000
  D_lt : ∀ j, j ≤ 5 → ∀ t ∈ seg j, b ≤ t → t ≤ l →
    ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 * pnormD j i t < 2000000

theorem exists_seg_of_Icc {t : ℝ} (ht : t ∈ Icc b l) : ∃ j, j ≤ 5 ∧ t ∈ seg j :=
  exists_seg_of_mem ⟨lt_of_lt_of_le b_pos ht.1, ht.2⟩

/-- The first two derivatives of the splines on `seg j` are those of the pieces. -/
theorem deriv_u_seg {i j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j) :
    deriv (u i) t = iteratedDeriv 1 (Piece.u i j) t ∧
      deriv (deriv (u i)) t = iteratedDeriv 2 (Piece.u i j) t := by
  obtain ⟨h1, h2⟩ := deriv_u_eq_piece i (by omega : j ≤ 6)
  rw [iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
  exact ⟨h1 ht, h2 ht⟩

theorem deriv_D_seg {i j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j) :
    D i t = Piece.D i j t ∧ deriv (D i) t = iteratedDeriv 1 (Piece.D i j) t ∧
      deriv (deriv (D i)) t = iteratedDeriv 2 (Piece.D i j) t := by
  obtain ⟨h1, h2⟩ := deriv_D_eq_piece i (by omega : j ≤ 6)
  rw [iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
  exact ⟨eqOn_D i (by omega : j ≤ 6) ht, h1 ht, h2 ht⟩

/-- Spline form of the premise on `B̃₁`: `|B̃₁(t)| + |B̃₁'(t)| < 6000` on `[b, l]`. -/
theorem core_B₁ (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc b l) : |Trunc.B₁ t| + |Bt1d t| < 6000 := by
  obtain ⟨j, hj, hts⟩ := exists_seg_of_Icc ht
  have h := hc.B₁_lt j hj t hts ht.1 ht.2
  have htp : 0 < t := lt_of_lt_of_le b_pos ht.1
  unfold pnormB₁ at h
  rw [Trunc_B₁_eq htp]
  unfold Bt1d
  have e1 : ∑ i ∈ Finset.range 39, deriv (u i) t = ∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) t :=
    Finset.sum_congr rfl fun i _ => (deriv_u_seg hj hts).1
  have e2 : ∑ i ∈ Finset.range 39, deriv (deriv (u i)) t =
      ∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t :=
    Finset.sum_congr rfl fun i _ => (deriv_u_seg hj hts).2
  rw [e1, e2]
  have := abs_nonneg (∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 / t ^ 3)
  linarith

/-- Spline form of the premise on `D`: `∑_{i ≤ 38} (k_i + 1)³ (|D_i| + |D_i'| + |D_i''|/2) < 2·10⁶` on `[b, l]`. -/
theorem core_D (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc b l) :
    ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 *
      (|D i t| + |deriv (D i) t| + |deriv (deriv (D i)) t| / 2) < 2000000 := by
  obtain ⟨j, hj, hts⟩ := exists_seg_of_Icc ht
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) (hc.D_lt j hj t hts ht.1 ht.2)
  obtain ⟨e0, e1, e2⟩ := deriv_D_seg (i := i) hj hts
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold pnormD
  rw [e0, e1, e2]
  have := abs_nonneg (iteratedDeriv 3 (Piece.D i j) t)
  linarith

/-! ### The region `t > l` -/

theorem trunc_B₁_of_gt {r : ℝ} (hr : l < r) : Trunc.B₁ r = 1 / r ∧ Bt1d r = -(1 / r ^ 2) := by
  have hr0 : 0 < r := by have := l_gt; linarith
  have h : ∀ i, deriv (u i) r = 0 ∧ deriv (deriv (u i)) r = 0 := fun i =>
    deriv_deriv_zero_of (eventuallyEq_u_of_gt i hr)
  refine ⟨?_, ?_⟩
  · rw [Trunc_B₁_eq hr0]; simp [fun i => (h i).1]
  · unfold Bt1d; simp [fun i => (h i).2]

/-- **Global bound** `|B̃₁(t)| + |B̃₁'(t)| ≤ 6000` at every `t > 0`, under the finite premise. -/
theorem B₁_bound_all (hc : FiniteCore) {r : ℝ} (hr : 0 < r) : |Trunc.B₁ r| + |Bt1d r| ≤ 6000 := by
  rcases le_or_gt r b with h | h
  · have := B₁_small hc.abs_coeff_one hr h
    linarith
  rcases le_or_gt r l with h' | h'
  · have := core_B₁ hc ⟨h.le, h'⟩
    linarith
  · obtain ⟨e1, e2⟩ := trunc_B₁_of_gt h'
    have hl : 696 / 1000 < r := lt_trans l_gt h'
    rw [e1, e2, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    have h1 : 1 / r ≤ 2 := by rw [div_le_iff₀ hr]; nlinarith
    have h2 : 1 / r ^ 2 ≤ 3 := by rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-! ### `NearZero` facts -/

theorem NearZero.zero : NearZero (fun _ : ℝ => (0 : ℝ)) :=
  ⟨continuousOn_const, 0, 1, one_pos, fun _ _ => by simp⟩

theorem NearZero.const (c : ℝ) : NearZero (fun _ : ℝ => c) :=
  ⟨continuousOn_const, |c|, 1, one_pos, fun _ _ => le_rfl⟩

theorem NearZero.finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} (h : ∀ i ∈ s, NearZero (F i)) :
    NearZero (fun r => ∑ i ∈ s, F i r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NearZero.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem NearZero.congr_pos {f g : ℝ → ℝ} (h : ∀ r, 0 < r → f r = g r) (hf : NearZero f) : NearZero g := by
  obtain ⟨hc, C, δ, hδ, hb⟩ := hf
  refine ⟨hc.congr fun r hr => (h r hr).symm, C, δ, hδ, fun r hr => ?_⟩
  rw [← h r hr.1]; exact hb r hr

theorem nearZero_of_jet {U : Set ℝ} {f f₁ : ℝ → ℝ} (hU : Ioi 0 ⊆ U) (h : ∀ x ∈ U, HasDerivAt f (f₁ x) x)
    (C δ : ℝ) (hδ : 0 < δ) (hb : ∀ r ∈ Ioc 0 δ, |f r| ≤ C) : NearZero f :=
  ⟨fun x hx => (h x (hU hx)).continuousAt.continuousWithinAt, C, δ, hδ, hb⟩

theorem nearZero_u_mul (i : ℕ) : NearZero (fun r => u i r * r) := by
  have hc : ContinuousOn (fun r => u i r * r) (Ioi 0) :=
    ((contDiffOn_u i).continuousOn).mul continuousOn_id
  refine ⟨hc, |coeff i| + 3, R₀, R₀_pos, fun r hr => ?_⟩
  have hR := R₀_lt
  have hr1 : r ≤ 1 := by linarith [hr.2]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · show |u 0 r * r| ≤ _
    rw [u_zero_of_le_R₀ hr.2]
    unfold gamma
    have hl := Real.abs_log_mul_self_lt r hr.1 hr1
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have : (-Real.log r + Real.pi * r ^ 2 / 2) * r = -(Real.log r * r) + Real.pi * r ^ 3 / 2 := by ring
    rw [this]
    have h3 : r ^ 3 ≤ 1 := pow_le_one₀ hr.1.le hr1
    have hpi0 := Real.pi_pos
    have hB : 0 ≤ Real.pi * r ^ 3 / 2 := by have := hr.1; positivity
    calc |-(Real.log r * r) + Real.pi * r ^ 3 / 2| ≤ |-(Real.log r * r)| + |Real.pi * r ^ 3 / 2| :=
          abs_add_le _ _
      _ = |Real.log r * r| + Real.pi * r ^ 3 / 2 := by rw [abs_neg, abs_of_nonneg hB]
      _ ≤ |coeff 0| + 3 := by nlinarith [abs_nonneg (coeff 0), pow_pos hr.1 3]
  · show |u i r * r| ≤ _
    rw [u_of_le_R₀ hi hr.2]
    have hpow : r ^ (k i) ≤ 1 := pow_le_one₀ hr.1.le hr1
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_pos hr.1]
    have h1 : r ^ k i * r ≤ 1 := by
      calc r ^ k i * r ≤ 1 * 1 := mul_le_mul hpow hr1 hr.1.le zero_le_one
        _ = 1 := by norm_num
    nlinarith [abs_nonneg (coeff i)]

theorem nearZero_trunc_B_mul : NearZero (fun r => Trunc.B r * r) := by
  have := NearZero.finset_sum (Finset.range 39) (fun i _ => nearZero_u_mul i)
  refine this.congr_pos (fun r _ => ?_)
  unfold Trunc.B
  rw [Trunc.modes_succ, Finset.sum_mul]

theorem nearZero_dU0_mul : NearZero (fun r => dU0 r * r) := by
  refine ⟨fun x hx => ((jet_dU.d0 x hx).continuousAt.mul continuousAt_id).continuousWithinAt, ww, 1, one_pos,
    fun r hr => ?_⟩
  rw [abs_mul, abs_of_pos hr.1]
  have := (dU_bound hr.1).1
  nlinarith [ww_nonneg, hr.2, hr.1]

theorem nearZero_Trunc_B₁ (hc : FiniteCore) : NearZero Trunc.B₁ :=
  nearZero_of_jet (U := Ioi 0) subset_rfl jet_Bt1.d0 10 b b_pos fun r hr => by
    have := B₁_small hc.abs_coeff_one hr.1 hr.2
    linarith [abs_nonneg (Bt1d r)]

theorem nearZero_dU1 : NearZero dU1 :=
  nearZero_of_jet (U := Ioi 0) subset_rfl jet_dU.d1 ww 1 one_pos fun _r hr => (dU_bound hr.1).2.1

theorem nearZero_B₁ (hc : FiniteCore) : NearZero B₁ :=
  (nearZero_Trunc_B₁ hc).add nearZero_dU1 |>.congr_pos fun r hr => by
    simp only [B₁_eq_trunc_add hr]

end Tails

end SandierSerfaty

end
