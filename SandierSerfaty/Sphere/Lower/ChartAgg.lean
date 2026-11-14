/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.CellSums
public import SandierSerfaty.Sphere.Lower.ChartAlgebra

/-!
# Aggregated bounds over the cells of a chart (sphere note, Theorem 6.14)

For `R = L²` and a family of cells with `CellSpec`, writing `V₀ = 121 π² m₊² R⁶ / s_n²`,
`N = #cells`, `Sⱼ = ` strip energy of `H_{1/4} - vⱼ` on the cell `j`, `pⱼ = #(Z ∩ Qⱼ)`:

* `Lower.agg_strip`: `∑ Sⱼ ≤ 48 (∫ G)/L + 2 N V₀`;
* `Lower.agg_V`: `∑ ∫_{Qⱼ}|∇vⱼ|² ≤ N V₀`;  `Lower.agg_t`: `∑ tⱼ ≤ N R`;
* `Lower.agg_p`: `∑ pⱼ ≤ n`;
* `Lower.bad_p`: a square with `S_j > L⁴/C_scr` contains at most `2 C_scr S_j` points.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem agg_V {n : ℕ} {ρ R : ℝ} {θ : ℝ × ℝ} {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ}
    (spec : CellSpec n R θ ρ t nb v) :
    ∑ j ∈ cellFin R θ ρ, ∫ x in sqAt (cellAt R θ j) (t j), ‖gradC (v j) x‖ ^ 2 ≤
      (cellFin R θ ρ).card * (121 * Real.pi ^ 2 * mPlus ^ 2 * R ^ 6 / blowupScale n ^ 2) := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun j hj => (spec j hj).2.2.2.2.2.1

theorem agg_t {n : ℕ} {ρ R : ℝ} {θ : ℝ × ℝ} {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ}
    (spec : CellSpec n R θ ρ t nb v) : ∑ j ∈ cellFin R θ ρ, t j ≤ (cellFin R θ ρ).card * R := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun j hj => by linarith [(spec j hj).2.1]

theorem agg_strip {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ} (h : ChartCtx n X ρ) {L : ℝ} (hL : 2 ≤ L) {θ : ℝ × ℝ}
    {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ} (spec : CellSpec n (L ^ 2) θ ρ t nb v)
    (hband : (∑ j ∈ cellFin (L ^ 2) θ ρ, ∫ z in stripSq (L ^ 2) θ (L / 2) (2 * L + 1) j, gradDensity X ρ z) *
        L ^ 2 ≤ 12 * (2 * L + 1 - L / 2) * ∫ z, gradDensity X ρ z) :
    ∑ j ∈ cellFin (L ^ 2) θ ρ, stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L ≤
      48 * (∫ z, gradDensity X ρ z) / L +
        2 * ((cellFin (L ^ 2) θ ρ).card * (121 * Real.pi ^ 2 * mPlus ^ 2 * (L ^ 2) ^ 6 / blowupScale n ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < L ^ 2 := by positivity
  set J := cellFin (L ^ 2) θ ρ with hJ
  set G0 := ∫ z, gradDensity X ρ z with hG0
  have hG00 : 0 ≤ G0 := integral_nonneg (gradDensity_nonneg X ρ)
  have hper : ∀ j ∈ J, stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L ≤
      2 * (∫ z in stripSq (L ^ 2) θ (L / 2) (2 * L + 1) j, gradDensity X ρ z) +
        2 * (121 * Real.pi ^ 2 * mPlus ^ 2 * (L ^ 2) ^ 6 / blowupScale n ^ 2) := by
    intro j hj
    obtain ⟨ht1, ht2, -, hv, -, hV, -⟩ := spec j hj
    have := cell_strip_energy_le h hR0 hj ht1 ht2 (L := L) hL0.le hv
    linarith
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have hs2 : (∑ j ∈ J, ∫ z in stripSq (L ^ 2) θ (L / 2) (2 * L + 1) j, gradDensity X ρ z) ≤ 24 * G0 / L := by
    have h1 : (∑ j ∈ J, ∫ z in stripSq (L ^ 2) θ (L / 2) (2 * L + 1) j, gradDensity X ρ z) * L ^ 2 ≤
        24 * L * G0 := by
      refine hband.trans ?_
      nlinarith
    rw [le_div_iff₀ hL0]
    nlinarith
  have e : 2 * (24 * G0 / L) = 48 * G0 / L := by ring
  linarith [mul_le_mul_of_nonneg_left hs2 (by norm_num : (0 : ℝ) ≤ 2)]

theorem agg_p {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (h : ChartCtx n X ρ) (hR : 0 < R)
    {t : ℤ × ℤ → ℝ} (ht : ∀ j ∈ cellFin R θ ρ, t j ≤ R - 1 / 2) :
    ∑ j ∈ cellFin R θ ρ, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) ≤ n := by
  have h1 := sum_card_ptsIn_add_card_rest X h.injz hR h.one_le t ht (cellFin R θ ρ) (Finset.Subset.refl _)
  have h2 : ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) ≤ n := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i => ‖blowupScale n • X i‖ < ρ
    simpa using (Nat.cast_le (α := ℝ)).2 this
  have h3 : (0 : ℝ) ≤ ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
      ¬ ∃ j ∈ cellFin R θ ρ, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)).card : ℝ) := Nat.cast_nonneg _
  linarith

theorem bad_p {n : ℕ} {X : Fin n → ℂ} {ρ L Cscr S : ℝ} (h : ChartCtx n X ρ) (hL : 10 ≤ L) (hCscr : 1 ≤ Cscr)
    {a : ℂ} {t : ℝ} (ht : t ≤ L ^ 2) (ht0 : 0 ≤ t) (hbad : ¬ S ≤ L ^ 3 * L / Cscr) :
    ((ptsIn X a t).card : ℝ) ≤ 2 * Cscr * S := by
  have hL0 : 0 < L := by linarith
  have hS : L ^ 3 * L / Cscr < S := not_le.1 hbad
  have h1 : L ^ 4 < Cscr * S := by
    have := (div_lt_iff₀ (by linarith : 0 < Cscr)).1 hS
    linarith
  have h2 := card_filter_sqAt_le (separated_allPts X h.sep) a ht0
  have h3 : ((ptsIn X a t).card : ℝ) = (((allPts X).filter (· ∈ sqAt a t)).card : ℝ) := by
    rw [card_ptsIn X h.injz, card_filter_index X h.injz (fun w => w ∈ sqAt a t)]
  rw [← h3] at h2
  have hpi := Real.pi_gt_three
  have h4 : ((ptsIn X a t).card : ℝ) ≤ 2 * L ^ 4 := by
    have hc0 : (0 : ℝ) ≤ (ptsIn X a t).card := Nat.cast_nonneg _
    have h5 : (t + 1) ^ 2 ≤ (L ^ 2 + 1) ^ 2 := by nlinarith
    have hy : 100 ≤ L ^ 2 := by nlinarith
    have h6 : (L ^ 2 + 1) ^ 2 ≤ 3 / 2 * L ^ 4 := by
      have e : L ^ 4 = (L ^ 2) ^ 2 := by ring
      rw [e]; nlinarith [hy]
    nlinarith
  linarith

end Lower

end Sphere

end SandierSerfaty

end
