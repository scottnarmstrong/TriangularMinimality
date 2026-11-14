/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.InnerBound
public import SandierSerfaty.Tails.EdgeNearBound
public import SandierSerfaty.Tails.EdgeMidBound

/-!
# The mode-derivative bound `tail:mode-derivative-bound` (paper `tail:mode-derivative-bound`, §6.2), piecewise

For `m ≥ 39` (`k = 6 m ≥ 234`), the pieces `Piece.u m j`, `Piece.D m j` of `u_m` and `D_m` on each segment
`seg j`, `j ≤ 5` (together `(0, l]`, one-sided at the knots) have all derivatives of order `0, …, 3` bounded by
`wk (k m)` (paper `tail:w-definition`). The proof assembles:

* the baseline `w = U_m` (`BJ_w`: `30 k² (13/20)^k`);
* the radial data `b_m` on each segment: `0` on `seg 0`; `3·10⁶ k³ 2^{-k}` on `seg 1` (`BJ_bPoly`);
  `5600 k⁵ (3/5)^k` on `[p, p + .01]` (`BJ_V_near`) and `3·10⁶ k² (289/500)^k` on `[p + .01, R₀]` (`BJ_V_mid`)
  for `seg 2`; and `(1 + 2·10⁵ + 4000) · 3·10⁶ k² (289/500)^k < 7·10¹¹ k² (289/500)^k` on `seg 3, 4, 5` where
  `b_m` is the continuation `𝓗 V_m` (`BJ_contPolyC`, with `V_m^{(i)}(R₀)` bounded by `BJ_V_mid`, paper §6.2);
* the Leibniz factor of the cutoff `τ` (`τ^{(i)} ≤ 1, 27, 1067, 142223`): `145506 < 10⁶` (`BJ_combine`,
  paper §6.2); `D_m = b_m - u_m` costs one more `b_m`, `145507 < 10⁶`.
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The four terms of `w_k` for `k = k_m`. -/
@[expose] noncomputable def tA (m : ℕ) : ℝ := 30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m)

@[expose] noncomputable def tB1 (m : ℕ) : ℝ := 3000000 * innerF m

@[expose] noncomputable def tB2 (m : ℕ) : ℝ := 5600 * ((k m : ℕ) : ℝ) ^ 5 * (3 / 5 : ℝ) ^ (k m)

@[expose] noncomputable def tB4 (m : ℕ) : ℝ :=
  700000000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)

theorem wk_eq (m : ℕ) : wk (k m) = 1000000 * (tA m + tB1 m + tB2 m + tB4 m) := by
  unfold wk tA tB1 tB2 tB4 innerF twoPowInv
  ring

theorem tA_nonneg (m : ℕ) : 0 ≤ tA m := by unfold tA; positivity
theorem tB1_nonneg (m : ℕ) : 0 ≤ tB1 m := by unfold tB1; have := innerF_nonneg m; positivity
theorem tB2_nonneg (m : ℕ) : 0 ≤ tB2 m := by unfold tB2; positivity
theorem tB4_nonneg (m : ℕ) : 0 ≤ tB4 m := by unfold tB4; positivity

/-- **The Leibniz step with the cutoff** (paper §6.2): if `w` and `b` have jet bounds `A` and `B` and `τ`,
`1 - τ` have the jet bounds `1, 27, 1067, 142223`, then `(1 - τ) w + τ b` has all jet bounds `145506 (A + B)` and
`b - ((1 - τ) w + τ b)` has `145507 (A + B)`. -/
theorem BJ_combine {U s : Set ℝ} {w b τ : ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : BJ U s w A A A A) (hb : BJ U s b B B B B) (hτ : BJ U s τ 1 27 1067 142223)
    (hτ' : BJ U s (fun x => 1 - τ x) 1 27 1067 142223) :
    BJ U s (fun x => (1 - τ x) * w x + τ x * b x) (145506 * (A + B)) (145506 * (A + B))
      (145506 * (A + B)) (145506 * (A + B)) ∧
    BJ U s (fun x => b x - ((1 - τ x) * w x + τ x * b x)) (145507 * (A + B)) (145507 * (A + B))
      (145507 * (A + B)) (145507 * (A + B)) := by
  have h1 := BJ.mul hτ' hw (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := BJ.mul hτ hb (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hu := (h1.add h2).mono (N₀ := 145506 * (A + B)) (N₁ := 145506 * (A + B)) (N₂ := 145506 * (A + B))
    (N₃ := 145506 * (A + B)) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  refine ⟨hu, ?_⟩
  exact (hb.sub hu).mono (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)

/-- Assembling `u` and `D` on `s ⊆ seg j` from the bound `B ≤ B₁ + B₂ + B₄` for `b_m`. -/
theorem BJ_uD_of_b {m j : ℕ} (hm : 39 ≤ m) (hj : j ≤ 5) {U s : Set ℝ} (hs : s ⊆ seg j) {B : ℝ}
    (hB0 : 0 ≤ B) (hBle : B ≤ tB1 m + tB2 m + tB4 m) (hb : BJ U s (Piece.b m j) B B B B) :
    BJ U s (Piece.u m j) (wk (k m)) (wk (k m)) (wk (k m)) (wk (k m)) ∧
    BJ U s (Piece.D m j) (wk (k m)) (wk (k m)) (wk (k m)) (wk (k m)) := by
  have hw := ((BJ_w hm hj).mono_set hs).restrict (subset_univ U)
  have hτ := ((tau_BJ hj).mono_set hs).restrict (subset_univ U)
  have hτ' := ((one_sub_tau_BJ hj).mono_set hs).restrict (subset_univ U)
  obtain ⟨hu, hD⟩ := BJ_combine (A := 30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m)) (B := B)
    (by positivity) hB0 hw hb hτ hτ'
  have hW : 145507 * (30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m) + B) ≤ wk (k m) := by
    rw [wk_eq]
    have h1 := tA_nonneg m
    have h2 := tB1_nonneg m
    have h3 := tB2_nonneg m
    have h4 := tB4_nonneg m
    unfold tA at h1 ⊢
    nlinarith
  have hW' : 145506 * (30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m) + B) ≤ wk (k m) := by
    have : 0 ≤ 30 * ((k m : ℕ) : ℝ) ^ 2 * (13 / 20 : ℝ) ^ (k m) + B := by positivity
    nlinarith
  exact ⟨hu.mono hW' hW' hW' hW', hD.mono hW hW hW hW⟩

/-! ### The radial data `b_m` on each segment -/

theorem BJ_b_seg0 {m : ℕ} (hm : 39 ≤ m) :
    BJ univ (seg 0) (Piece.b m 0) 0 0 0 0 := by
  have hm0 : m ≠ 0 := by omega
  have e : Piece.b m 0 = fun _ => (0 : ℝ) := by funext r; simp [Piece.b, hm0]
  rw [e]
  simpa using BJ.const (0 : ℝ) univ (seg 0)

theorem BJ_b_seg1 {m : ℕ} (hm : 39 ≤ m) :
    BJ univ (seg 1) (Piece.b m 1) (tB1 m) (tB1 m) (tB1 m) (tB1 m) := by
  have hm0 : m ≠ 0 := by omega
  have e : Piece.b m 1 = bPoly m := by funext r; simp [Piece.b, hm0]
  rw [e]
  exact BJ_bPoly (by omega)

theorem p_add_hundredth_le_R₀ : p + 1 / 100 ≤ R₀ := by linarith [p_lt, R₀_gt]

theorem Icc_near_subset_seg2 : Icc p (p + 1 / 100) ⊆ seg 2 := fun r hr =>
  ⟨hr.1, by linarith [hr.2, p_add_hundredth_le_R₀]⟩

theorem Icc_mid_subset_seg2 : Icc (p + 1 / 100) R₀ ⊆ seg 2 := fun r hr =>
  ⟨by linarith [hr.1, p_pos], hr.2⟩

theorem Icc_mid_subset_Ioi : Icc (p + 1 / 100) R₀ ⊆ Ioi p := fun r hr => by
  simp only [mem_Ioi]; linarith [hr.1]

theorem BJ_b_seg2_near {m : ℕ} (hm : 39 ≤ m) :
    BJ univ (Icc p (p + 1 / 100)) (Piece.b m 2) (tB2 m) (tB2 m) (tB2 m) (tB2 m) := by
  have hm0 : m ≠ 0 := by omega
  have e : Piece.b m 2 = V m := by funext r; simp [Piece.b, hm0]
  rw [e]
  exact BJ_V_near hm

theorem BJ_b_seg2_mid {m : ℕ} (hm : 39 ≤ m) :
    BJ (Ioi p) (Icc (p + 1 / 100) R₀) (Piece.b m 2)
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)) := by
  have hm0 : m ≠ 0 := by omega
  have e : Piece.b m 2 = V m := by funext r; simp [Piece.b, hm0]
  rw [e]
  exact BJ_V_mid hm

/-- The values `|V_m^{(i)}(R₀)| ≤ 3·10⁶ k² (289/500)^k`, `i ≤ 2` (paper §6.2). -/
theorem abs_V_derivs_R₀_le {m : ℕ} (hm : 39 ≤ m) :
    |V m R₀| ≤ 3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) ∧
    |deriv (V m) R₀| ≤ 3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) ∧
    |deriv (deriv (V m)) R₀| ≤ 3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) := by
  have hmem : R₀ ∈ Icc (p + 1 / 100) R₀ := ⟨p_add_hundredth_le_R₀, le_rfl⟩
  obtain ⟨a0, a1, a2, -⟩ := BJ.iteratedDeriv_le isOpen_Ioi Icc_mid_subset_Ioi (BJ_V_mid hm) hmem
  refine ⟨a0, ?_, ?_⟩
  · rwa [iteratedDeriv_one] at a1
  · rwa [iteratedDeriv_succ, iteratedDeriv_one] at a2

theorem BJ_b_seg34 {m j : ℕ} (hm : 39 ≤ m) (hj : j = 3 ∨ j = 4) :
    BJ univ (seg j) (Piece.b m j) (205001 * (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)))
      (205001 * (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)))
      (205001 * (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)))
      (205001 * (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨a0, a1, a2⟩ := abs_V_derivs_R₀_le hm
  have hsub : seg j ⊆ Icc R₀ (R₀ + hs) := by
    rcases hj with rfl | rfl
    · intro r hr; exact ⟨hr.1, by have := hr.2; unfold hs; linarith⟩
    · intro r hr; exact ⟨by have := hr.1; linarith, hr.2⟩
  have e : Piece.b m j = contPolyC (V m R₀) (deriv (V m) R₀) (deriv (deriv (V m)) R₀) := by
    funext r
    rcases hj with rfl | rfl <;> simp [Piece.b, hm0, contPoly_eq]
  rw [e]
  have h := BJ_contPolyC (V m R₀) (deriv (V m) R₀) (deriv (deriv (V m)) R₀) univ hsub
  have hM : 0 ≤ 3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) := by positivity
  refine h.mono ?_ ?_ ?_ ?_ <;> nlinarith [abs_nonneg (V m R₀), abs_nonneg (deriv (V m) R₀),
    abs_nonneg (deriv (deriv (V m)) R₀)]

theorem BJ_b_seg5 {m : ℕ} (hm : 39 ≤ m) :
    BJ univ (seg 5) (Piece.b m 5) (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m))
      (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)) := by
  have hm0 : m ≠ 0 := by omega
  obtain ⟨a0, -, -⟩ := abs_V_derivs_R₀_le hm
  have e : Piece.b m 5 = fun _ => V m R₀ := by funext r; simp [Piece.b, hm0]
  rw [e]
  have hM : 0 ≤ 3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) := by positivity
  simpa using (BJ.const (V m R₀) univ (seg 5)).mono (by simpa using a0) hM hM hM

/-! ### The pieces `Piece.u`, `Piece.D` on each segment -/

theorem three_le_tB4 (m : ℕ) :
    3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) ≤ tB4 m := by
  unfold tB4
  have : 0 ≤ ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) := by positivity
  nlinarith

theorem cont_le_tB4 (m : ℕ) :
    205001 * (3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m)) ≤ tB4 m := by
  unfold tB4
  have : 0 ≤ ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) := by positivity
  nlinarith

/-- **Pieces of `u_m` and `D_m` as bounded jets.** Every `r ∈ seg j` (`j ≤ 5`) lies in a set `s ⊆ U` (`U` open)
on which `Piece.u m j` and `Piece.D m j` have jets bounded by `wk (k m)` in all orders `0, …, 3`. -/
theorem exists_BJ_uD {m j : ℕ} (hm : 39 ≤ m) (hj : j ≤ 5) {r : ℝ} (hr : r ∈ seg j) :
    ∃ U s : Set ℝ, IsOpen U ∧ s ⊆ U ∧ r ∈ s ∧
      BJ U s (Piece.u m j) (wk (k m)) (wk (k m)) (wk (k m)) (wk (k m)) ∧
      BJ U s (Piece.D m j) (wk (k m)) (wk (k m)) (wk (k m)) (wk (k m)) := by
  have h1 := tB1_nonneg m
  have h2 := tB2_nonneg m
  have h4 := tB4_nonneg m
  have hM : 0 ≤ 3000000 * ((k m : ℕ) : ℝ) ^ 2 * (289 / 500 : ℝ) ^ (k m) := by positivity
  interval_cases j
  · exact ⟨univ, seg 0, isOpen_univ, subset_univ _, hr,
      BJ_uD_of_b hm hj (subset_refl _) le_rfl (by linarith) (BJ_b_seg0 hm)⟩
  · exact ⟨univ, seg 1, isOpen_univ, subset_univ _, hr,
      BJ_uD_of_b hm hj (subset_refl _) h1 (by linarith) (BJ_b_seg1 hm)⟩
  · by_cases hr' : r ≤ p + 1 / 100
    · exact ⟨univ, Icc p (p + 1 / 100), isOpen_univ, subset_univ _, ⟨hr.1, hr'⟩,
        BJ_uD_of_b hm hj Icc_near_subset_seg2 h2 (by linarith) (BJ_b_seg2_near hm)⟩
    · exact ⟨Ioi p, Icc (p + 1 / 100) R₀, isOpen_Ioi, Icc_mid_subset_Ioi,
        ⟨by linarith [not_le.1 hr'], hr.2⟩,
        BJ_uD_of_b hm hj Icc_mid_subset_seg2 hM (by linarith [three_le_tB4 m]) (BJ_b_seg2_mid hm)⟩
  · exact ⟨univ, seg 3, isOpen_univ, subset_univ _, hr,
      BJ_uD_of_b hm hj (subset_refl _) (by positivity) (by linarith [cont_le_tB4 m])
        (BJ_b_seg34 hm (Or.inl rfl))⟩
  · exact ⟨univ, seg 4, isOpen_univ, subset_univ _, hr,
      BJ_uD_of_b hm hj (subset_refl _) (by positivity) (by linarith [cont_le_tB4 m])
        (BJ_b_seg34 hm (Or.inr rfl))⟩
  · exact ⟨univ, seg 5, isOpen_univ, subset_univ _, hr,
      BJ_uD_of_b hm hj (subset_refl _) hM (by linarith [three_le_tB4 m]) (BJ_b_seg5 hm)⟩

/-- **`tail:mode-derivative-bound` for the pieces** (paper `tail:mode-derivative-bound`, §6.2): for `m ≥ 39`, `j ≤ 5` and
`r ∈ seg j`, the derivatives `0, …, 3` of the piece `u_m` and `D_m` at `r` (one-sided at the knots) are at most
`w_{k_m}`. -/
theorem piece_derivs_le {m j : ℕ} (hm : 39 ≤ m) (hj : j ≤ 5) {r : ℝ} (hr : r ∈ seg j) :
    (|Piece.u m j r| ≤ wk (k m) ∧ |iteratedDeriv 1 (Piece.u m j) r| ≤ wk (k m) ∧
      |iteratedDeriv 2 (Piece.u m j) r| ≤ wk (k m) ∧ |iteratedDeriv 3 (Piece.u m j) r| ≤ wk (k m)) ∧
    (|Piece.D m j r| ≤ wk (k m) ∧ |iteratedDeriv 1 (Piece.D m j) r| ≤ wk (k m) ∧
      |iteratedDeriv 2 (Piece.D m j) r| ≤ wk (k m) ∧ |iteratedDeriv 3 (Piece.D m j) r| ≤ wk (k m)) := by
  obtain ⟨U, s, hU, hsU, hrs, hu, hD⟩ := exists_BJ_uD hm hj hr
  exact ⟨BJ.iteratedDeriv_le hU hsU hu hrs, BJ.iteratedDeriv_le hU hsU hD hrs⟩

/-! ### The splines `u_m`, `D_m` -/

/-- Every `r ∈ (0, l]` lies in one of the closed segments `seg 0, …, seg 5`. -/
theorem exists_seg_of_mem {r : ℝ} (hr : r ∈ Ioc 0 l) : ∃ j, j ≤ 5 ∧ r ∈ seg j := by
  have h1 := p_lt_R₀
  have h2 := c_pos
  have h3 := hs_pos
  have h4 := R₀_add_thousandth_lt_R₀_add_hs
  by_cases a1 : r ≤ p - c
  · exact ⟨0, by norm_num, hr.1, a1⟩
  by_cases a2 : r ≤ p
  · exact ⟨1, by norm_num, by linarith, a2⟩
  by_cases a3 : r ≤ R₀
  · exact ⟨2, by norm_num, by linarith, a3⟩
  by_cases a4 : r ≤ R₀ + 1 / 1000
  · exact ⟨3, by norm_num, by linarith, a4⟩
  by_cases a5 : r ≤ R₀ + hs
  · exact ⟨4, by norm_num, by linarith, a5⟩
  · exact ⟨5, by norm_num, by linarith, hr.2⟩

theorem contDiffAt_Piece_u (m j : ℕ) {r : ℝ} (hr : 0 < r) : ContDiffAt ℝ 3 (Piece.u m j) r :=
  ((contDiffOn_Piece_u m j).mono (subset_refl _)).contDiffAt (Ioi_mem_nhds hr) |>.of_le (by simp)

theorem contDiffAt_Piece_D (m j : ℕ) {r : ℝ} (hr : 0 < r) : ContDiffAt ℝ 3 (Piece.D m j) r :=
  ((contDiffOn_Piece_D m j).mono (subset_refl _)).contDiffAt (Ioi_mem_nhds hr) |>.of_le (by simp)

/-- **`tail:mode-derivative-bound`, orders `0, 1, 2`** (paper `tail:mode-derivative-bound`): for `m ≥ 39` and `0 < r ≤ l`,
`|u_m^{(j)}(r)|, |D_m^{(j)}(r)| ≤ w_{k_m}`, `j = 0, 1, 2` (the splines are `C²`, so no one-sided distinction). -/
theorem mode_derivative_bound_le_two {m : ℕ} (hm : 39 ≤ m) {r : ℝ} (hr : r ∈ Ioc 0 l) :
    (|u m r| ≤ wk (k m) ∧ |deriv (u m) r| ≤ wk (k m) ∧ |deriv (deriv (u m)) r| ≤ wk (k m)) ∧
    (|D m r| ≤ wk (k m) ∧ |deriv (D m) r| ≤ wk (k m) ∧ |deriv (deriv (D m)) r| ≤ wk (k m)) := by
  obtain ⟨j, hj, hrj⟩ := exists_seg_of_mem hr
  have hj6 : j ≤ 6 := by omega
  obtain ⟨⟨u0, u1, u2, -⟩, ⟨D0, D1, D2, -⟩⟩ := piece_derivs_le (m := m) hm hj hrj
  have eu := eqOn_u m hj6 hrj
  have eD := eqOn_D m hj6 hrj
  obtain ⟨du1, du2⟩ := deriv_u_eq_piece m hj6
  obtain ⟨dD1, dD2⟩ := deriv_D_eq_piece m hj6
  rw [iteratedDeriv_one] at u1 D1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at u2 D2
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rwa [eu]
  · rwa [du1 hrj]
  · rwa [du2 hrj]
  · rwa [eD]
  · rwa [dD1 hrj]
  · rwa [dD2 hrj]

/-- **`tail:mode-derivative-bound`, order `3`, one-sided** (paper §6.2: "at spline knots these inequalities mean
both one-sided derivatives"): the third derivative of the spline `u_m`, `D_m` relative to the closed segment
`seg j` is at most `w_{k_m}` at every point of `seg j`. -/
theorem mode_derivative_bound_three {m : ℕ} (hm : 39 ≤ m) {j : ℕ} (hj : j ≤ 5) {r : ℝ} (hr : r ∈ seg j) :
    |iteratedDerivWithin 3 (u m) (seg j) r| ≤ wk (k m) ∧
      |iteratedDerivWithin 3 (D m) (seg j) r| ≤ wk (k m) := by
  have hj6 : j ≤ 6 := by omega
  obtain ⟨⟨-, -, -, u3⟩, ⟨-, -, -, D3⟩⟩ := piece_derivs_le (m := m) hm hj hr
  have hpos : 0 < r := seg_subset_Ioi hr
  have hud := uniqueDiffOn_seg hj6
  have e1 : iteratedDerivWithin 3 (u m) (seg j) r = iteratedDeriv 3 (Piece.u m j) r := by
    rw [iteratedDerivWithin_congr (eqOn_u m hj6) hr,
      iteratedDerivWithin_eq_iteratedDeriv hud (contDiffAt_Piece_u m j hpos) hr]
  have e2 : iteratedDerivWithin 3 (D m) (seg j) r = iteratedDeriv 3 (Piece.D m j) r := by
    rw [iteratedDerivWithin_congr (eqOn_D m hj6) hr,
      iteratedDerivWithin_eq_iteratedDeriv hud (contDiffAt_Piece_D m j hpos) hr]
  exact ⟨by rwa [e1], by rwa [e2]⟩

/-- **`tail:mode-derivative-bound`** (paper `tail:mode-derivative-bound` and its proof in §6.2; all derivative orders
are proved). For every `m ≥ 39` (`k = 6 m ≥ 234`) and every `0 < r ≤ l`, `u_m` and `D_m` and their derivatives of
orders `1, 2` at `r` are bounded by `w_k` (`wk`, paper `tail:w-definition`), and the third derivative relative to each closed
spline segment `seg j` (`j ≤ 5`, together `(0, l]`; the one-sided third derivatives at the knots) is bounded by
`w_k` at every point of the segment. -/
theorem mode_derivative_bound {m : ℕ} (hm : 39 ≤ m) :
    (∀ r ∈ Ioc 0 l,
      (|u m r| ≤ wk (6 * m) ∧ |deriv (u m) r| ≤ wk (6 * m) ∧ |deriv (deriv (u m)) r| ≤ wk (6 * m)) ∧
      (|D m r| ≤ wk (6 * m) ∧ |deriv (D m) r| ≤ wk (6 * m) ∧ |deriv (deriv (D m)) r| ≤ wk (6 * m))) ∧
    (∀ j, j ≤ 5 → ∀ r ∈ seg j,
      |iteratedDerivWithin 3 (u m) (seg j) r| ≤ wk (6 * m) ∧
        |iteratedDerivWithin 3 (D m) (seg j) r| ≤ wk (6 * m)) := by
  have hk : k m = 6 * m := k_of_pos (by omega)
  rw [← hk]
  exact ⟨fun r hr => mode_derivative_bound_le_two hm hr, fun j hj r hr =>
    mode_derivative_bound_three hm hj hr⟩

end Tails

end SandierSerfaty

end
