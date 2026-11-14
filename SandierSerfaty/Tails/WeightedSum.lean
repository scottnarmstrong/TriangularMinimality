/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Weights
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# `tail:weighted-sum` (paper `tail:sum`, `tail:weighted-sum`)

With `k_j = 6 (j + 39)` (the omitted modes `m = j + 39 ≥ 39`, `k = 6m ≥ 234`), put
`𝔞 = ∑_j (k_j + 1)⁴ w_{k_j}` (`aa`) and `W_* = 4 ∑_j w_{k_j}` (`Wstar`). The paper's verification: the ratio
of consecutive terms of each of the four pieces of `(k+1)⁴ w_k` is below `1/10` from `k = 234` on, and the first
term is below `1.56·10⁻²¹`; hence `𝔞 ≤ (10/9) · 1.56·10⁻²¹ < 2·10⁻²¹` and `W_* ≤ 4 𝔞`.

* `wt_succ_le`: the ratio bound; `summable_wt`, `tsum_wt_le`: summability and the bound `∑_j (k_j+1)^s w_{k_j} ≤ 𝔞`
  for `s ≤ 4`;
* `aa_lt` (`𝔞 < 2·10⁻²¹`), `Wstar_le` (`W_* ≤ 4𝔞`).
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The exponent `k = 6 (j + 39)` of the `j`-th omitted mode. -/
@[expose] def kk (j : ℕ) : ℕ := 6 * (j + 39)

/-- `(k_j + 1)^s w_{k_j}`. -/
@[expose] noncomputable def wt (s j : ℕ) : ℝ := ((kk j : ℝ) + 1) ^ s * wk (kk j)

/-- `𝔞 = ∑_{k = 234, 240, …} (k + 1)⁴ w_k` (paper `tail:weighted-sum`). -/
@[expose] noncomputable def aa : ℝ := ∑' j, wt 4 j

/-- `∑_{k = 234, 240, …} w_k`. -/
@[expose] noncomputable def ww : ℝ := ∑' j, wk (kk j)

/-- `W_* = 4 ∑_{k = 234, 240, …} w_k` (paper `tail:weighted-sum`). -/
@[expose] noncomputable def Wstar : ℝ := 4 * ww

theorem kk_succ (j : ℕ) : kk (j + 1) = kk j + 6 := by unfold kk; ring

theorem kk_ge (j : ℕ) : 234 ≤ kk j := by unfold kk; omega

theorem wk_nonneg (k : ℕ) : 0 ≤ wk k := by unfold wk; positivity

theorem wt_nonneg (s j : ℕ) : 0 ≤ wt s j := by unfold wt; have := wk_nonneg (kk j); positivity

/-- One factor of the ratio estimate: `(k + 7)⁴ (k + 6)^p r^{k+6} ≤ (1/10) (k+1)⁴ k^p r^k` for `k ≥ 234`
as soon as `(241/235)⁴ (240/234)^p r⁶ ≤ 1/10`. -/
theorem ratio_le (p : ℕ) {r : ℝ} (hr : 0 ≤ r) (hq : (241 / 235 : ℝ) ^ 4 * (240 / 234) ^ p * r ^ 6 ≤ 1 / 10)
    {k : ℕ} (hk : 234 ≤ k) :
    ((k : ℝ) + 6 + 1) ^ 4 * (((k : ℝ) + 6) ^ p * r ^ (k + 6)) ≤
      1 / 10 * (((k : ℝ) + 1) ^ 4 * ((k : ℝ) ^ p * r ^ k)) := by
  have hk' : (234 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ((k : ℝ) + 6 + 1) ≤ 241 / 235 * ((k : ℝ) + 1) := by linarith
  have h2 : ((k : ℝ) + 6) ≤ 240 / 234 * (k : ℝ) := by linarith
  have h1' : ((k : ℝ) + 6 + 1) ^ 4 ≤ (241 / 235 : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 4 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 4
  have h2' : ((k : ℝ) + 6) ^ p ≤ (240 / 234 : ℝ) ^ p * (k : ℝ) ^ p := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 p
  have hP : 0 ≤ ((k : ℝ) + 1) ^ 4 * ((k : ℝ) ^ p * r ^ k) := by positivity
  have e : r ^ (k + 6) = r ^ 6 * r ^ k := by ring
  have h3 : ((k : ℝ) + 6 + 1) ^ 4 * (((k : ℝ) + 6) ^ p * r ^ (k + 6)) ≤
      ((241 / 235 : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 4) * (((240 / 234 : ℝ) ^ p * (k : ℝ) ^ p) * (r ^ 6 * r ^ k)) := by
    rw [e]
    exact mul_le_mul h1' (mul_le_mul_of_nonneg_right h2' (by positivity)) (by positivity) (by positivity)
  refine h3.trans ?_
  have h4 : ((241 / 235 : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 4) * (((240 / 234 : ℝ) ^ p * (k : ℝ) ^ p) * (r ^ 6 * r ^ k)) =
      ((241 / 235 : ℝ) ^ 4 * (240 / 234 : ℝ) ^ p * r ^ 6) * (((k : ℝ) + 1) ^ 4 * ((k : ℝ) ^ p * r ^ k)) := by
    ring
  rw [h4]
  exact mul_le_mul_of_nonneg_right hq hP

theorem wt_succ_le (j : ℕ) : wt 4 (j + 1) ≤ 1 / 10 * wt 4 j := by
  have hk := kk_ge j
  have hc : ((kk (j + 1) : ℕ) : ℝ) = (kk j : ℝ) + 6 := by rw [kk_succ]; push_cast; ring
  have a1 := ratio_le 2 (r := 13 / 20) (by norm_num) (by norm_num) hk
  have a2 := ratio_le 3 (r := 1 / 2) (by norm_num) (by norm_num) hk
  have a3 := ratio_le 5 (r := 3 / 5) (by norm_num) (by norm_num) hk
  have a4 := ratio_le 2 (r := 289 / 500) (by norm_num) (by norm_num) hk
  unfold wt wk
  rw [hc, kk_succ]
  have e2 : ∀ n : ℕ, ((2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := fun n => by rw [one_div, inv_pow]
  simp only [e2]
  linarith [a1, a2, a3, a4]

theorem wt_le_geom (j : ℕ) : wt 4 j ≤ wt 4 0 * (1 / 10 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ n ih =>
    calc wt 4 (n + 1) ≤ 1 / 10 * wt 4 n := wt_succ_le n
      _ ≤ 1 / 10 * (wt 4 0 * (1 / 10 : ℝ) ^ n) := by gcongr
      _ = wt 4 0 * (1 / 10 : ℝ) ^ (n + 1) := by ring

theorem wt_zero_lt : wt 4 0 < 156 / 100 / 10 ^ 21 := by
  unfold wt wk kk
  norm_num

theorem summable_wt4 : Summable (wt 4) :=
  Summable.of_nonneg_of_le (fun j => wt_nonneg 4 j) wt_le_geom
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

theorem wt_mono {s : ℕ} (hs : s ≤ 4) (j : ℕ) : wt s j ≤ wt 4 j := by
  unfold wt
  have := wk_nonneg (kk j)
  have h0 : (0 : ℝ) ≤ kk j := by positivity
  have h1 : (1 : ℝ) ≤ (kk j : ℝ) + 1 := by linarith
  have h2 : ((kk j : ℝ) + 1) ^ s ≤ ((kk j : ℝ) + 1) ^ 4 := pow_le_pow_right₀ h1 hs
  exact mul_le_mul_of_nonneg_right h2 this

theorem summable_wt {s : ℕ} (hs : s ≤ 4) : Summable (wt s) :=
  Summable.of_nonneg_of_le (fun j => wt_nonneg s j) (wt_mono hs) summable_wt4

theorem tsum_wt_le {s : ℕ} (hs : s ≤ 4) : ∑' j, wt s j ≤ aa :=
  Summable.tsum_le_tsum (wt_mono hs) (summable_wt hs) summable_wt4

theorem wt_zero_eq (j : ℕ) : wt 0 j = wk (kk j) := by unfold wt; simp

theorem summable_wk : Summable fun j => wk (kk j) :=
  (summable_wt (s := 0) (by norm_num)).congr fun j => wt_zero_eq j

theorem ww_le_aa : ww ≤ aa := by
  have := tsum_wt_le (s := 0) (by norm_num)
  simpa [ww, wt_zero_eq] using this

/-- **`tail:weighted-sum`**: `𝔞 < 2·10⁻²¹`. -/
theorem aa_lt : aa < 2 / 10 ^ 21 := by
  have hs : Summable fun j : ℕ => wt 4 0 * (1 / 10 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h : aa ≤ ∑' j : ℕ, wt 4 0 * (1 / 10 : ℝ) ^ j := Summable.tsum_le_tsum wt_le_geom summable_wt4 hs
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at h
  have h0 := wt_zero_lt
  have : wt 4 0 * (1 - 1 / 10 : ℝ)⁻¹ ≤ 156 / 100 / 10 ^ 21 * (1 - 1 / 10 : ℝ)⁻¹ := by
    gcongr
  have e : (156 / 100 / 10 ^ 21 * (1 - 1 / 10 : ℝ)⁻¹ : ℝ) < 2 / 10 ^ 21 := by norm_num
  linarith

theorem aa_nonneg : 0 ≤ aa := tsum_nonneg fun j => wt_nonneg 4 j

theorem ww_nonneg : 0 ≤ ww := tsum_nonneg fun j => wk_nonneg (kk j)

/-- `W_* ≤ 4 𝔞` (paper `tail:weighted-sum`). -/
theorem Wstar_le : Wstar ≤ 4 * aa := by
  unfold Wstar; linarith [ww_le_aa]

end Tails

end SandierSerfaty

end
