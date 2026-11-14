/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GoodCell
public import SandierSerfaty.Sphere.Lower.ChartAgg

/-!
# The grid argument for one chart, first half (sphere note, Theorem 6.14)

`Lower.large_chart_pre`: for a chart with a `CellSpec` family, split the cells into good and bad ones, apply the
good-square bound on the good ones, and bound the number of the remaining points by `2 C_scr ∑ S_j + 7 R N + 16 ρ (R+1)`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem large_chart_pre {Cscr ℓ₀ C : ℝ} (hCscr : 1 ≤ Cscr) (hC : 0 ≤ C) (hGS : GoodSquareSpec Cscr ℓ₀ C)
    {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ} (h : ChartCtx n X ρ) {L : ℝ} {θ : ℝ × ℝ} {t : ℤ × ℤ → ℝ}
    {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ} (spec : CellSpec n (L ^ 2) θ ρ t nb v) (hL100 : 100 ≤ L)
    (hLℓ : ℓ₀ ≤ L) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ rest : ℝ, 0 ≤ rest ∧
      rest ≤ 2 * Cscr * (∑ j ∈ cellFin (L ^ 2) θ ρ,
          stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L) +
        7 * (L ^ 2 * (cellFin (L ^ 2) θ ρ).card) + 16 * ρ * (L ^ 2 + 1) ∧
      cStar * ((innerBlown X ρ).card : ℝ) - (constC1 + |cStar|) * rest -
        ∑ j ∈ cellFin (L ^ 2) θ ρ, cellErr X L C ε (4 * mPlus * L ^ 2 / blowupScale n)
          (cellAt (L ^ 2) θ j) (t j) (nb j) (v j) -
        Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
      punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
        Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ), Real.log (lam (X i)) := by
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < L ^ 2 := by positivity
  have hR2 : 2 ≤ L ^ 2 := by nlinarith
  have hδ0 : 0 ≤ 4 * mPlus * L ^ 2 / blowupScale n := by
    have := blowupScale_pos h.pos
    have := mPlus_pos
    positivity
  have ht1 : ∀ j ∈ cellFin (L ^ 2) θ ρ, 0 ≤ t j := fun j hj => by
    have := (spec j hj).1
    nlinarith
  have ht1' : ∀ j ∈ cellFin (L ^ 2) θ ρ, L ^ 2 - 1 ≤ t j := fun j hj => (spec j hj).1
  have ht2 : ∀ j ∈ cellFin (L ^ 2) θ ρ, t j ≤ L ^ 2 - 1 / 2 := fun j hj => (spec j hj).2.1
  set Good : Finset (ℤ × ℤ) := (cellFin (L ^ 2) θ ρ).filter (fun j =>
    stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L ≤ L ^ 3 * L / Cscr)
    with hGood
  have hGoodJ : Good ⊆ cellFin (L ^ 2) θ ρ := Finset.filter_subset _ _
  have hgood : ∀ j ∈ Good, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ) * cStar ≤
      fnQ X (cellAt (L ^ 2) θ j) (t j) + chartSum X (cellAt (L ^ 2) θ j) (t j) +
        cellErr X L C ε (4 * mPlus * L ^ 2 / blowupScale n) (cellAt (L ^ 2) θ j) (t j) (nb j) (v j) :=
    fun j hj => good_cell_bound hGS h spec hL100 hLℓ hε0 hε1 (Finset.mem_filter.1 hj).1
      (Finset.mem_filter.1 hj).2
  have hstep := chart_lower_step h hR0 ht1 ht2 hGoodJ hL0.le hC hε0 hδ0 hgood
  refine ⟨_, Nat.cast_nonneg _, ?_, hstep⟩
  -- the number of remaining points
  have hcr := card_rest_le X h.injz h.sep hR2 h.one_le t ht1' ht2 Good hGoodJ
  have hbad : ∀ j ∈ cellFin (L ^ 2) θ ρ \ Good, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ) ≤
      2 * Cscr * stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L := by
    intro j hj
    have hjJ := (Finset.mem_sdiff.1 hj).1
    have hjG := (Finset.mem_sdiff.1 hj).2
    have hnot : ¬ stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L ≤
        L ^ 3 * L / Cscr := fun hle => hjG (Finset.mem_filter.2 ⟨hjJ, hle⟩)
    exact bad_p h (by linarith) hCscr (by linarith [ht2 j hjJ]) (ht1 j hjJ) hnot
  have hsum : ∑ j ∈ cellFin (L ^ 2) θ ρ \ Good, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ) ≤
      2 * Cscr * ∑ j ∈ cellFin (L ^ 2) θ ρ,
        stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L := by
    refine (Finset.sum_le_sum hbad).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun j _ _ => stripEnergy_nonneg _ _ _ _
  have hN : ((cellFin (L ^ 2) θ ρ).card : ℝ) * (7 * L ^ 2) = 7 * (L ^ 2 * (cellFin (L ^ 2) θ ρ).card) := by ring
  linarith

/-- The discrepancy sum bound of `Lower.exists_disc_sum`, as a named `Prop`. -/
@[expose] def DiscSumSpec (CD : ℝ) : Prop :=
  ∀ {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (_ : ChartCtx n X ρ), 3 ≤ R →
    ∀ {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ}, CellSpec n R θ ρ t nb v →
    (∑ j ∈ cellFin R θ ρ, ∫ z in stripSq R θ (1 / 2) 2 j, gradDensity X ρ z) * R ≤
      12 * (2 - 1 / 2) * ∫ z, gradDensity X ρ z →
    ∑ j ∈ cellFin R θ ρ, |(nb j : ℝ) - (ptsIn X (cellAt R θ j) (t j)).card| ≤
      CD * ((1 + mPlus) * ((cellFin R θ ρ).card * R) +
        Real.sqrt ((cellFin R θ ρ).card * R) *
          Real.sqrt (12 * (2 - 1 / 2) * (∫ z, gradDensity X ρ z) / R))

theorem exists_discSumSpec : ∃ CD : ℝ, 0 ≤ CD ∧ DiscSumSpec CD := exists_disc_sum

/-- The coefficient of `n / L` in the error of one chart. -/
@[expose] noncomputable def chartK₁ (CA Cscr C CD : ℝ) : ℝ :=
  (|cStar| + constC1) * (2 * Cscr * (48 * CA) + 7 * (4 * Real.pi * blowupKappa ^ 2)) +
    C * (48 * CA + 4 * Real.pi * blowupKappa ^ 2 +
      CD * ((1 + mPlus) * (4 * Real.pi * blowupKappa ^ 2) +
        Real.sqrt (18 * (4 * Real.pi * blowupKappa ^ 2) * CA)) + 4 * Real.pi * blowupKappa ^ 2)

/-- The coefficient of `L⁸ √n` in the error of one chart. -/
@[expose] noncomputable def chartK₂ (CA Cscr C : ℝ) : ℝ :=
  (|cStar| + constC1) * (2 * Cscr * (2 * (4 * Real.pi * blowupKappa ^ 2) *
      (121 * Real.pi ^ 2 * mPlus ^ 2 / blowupKappa ^ 2)) + 64 * blowupKappa) +
    C * (2 * (4 * Real.pi * blowupKappa ^ 2) * (121 * Real.pi ^ 2 * mPlus ^ 2 / blowupKappa ^ 2) +
      4 * mPlus / blowupKappa) + CA / 2 +
    C * (4 * Real.pi * blowupKappa ^ 2) * (121 * Real.pi ^ 2 * mPlus ^ 2 / blowupKappa ^ 2)

theorem chartK₁_nonneg {CA Cscr C CD : ℝ} (hCA : 0 ≤ CA) (hCscr : 0 ≤ Cscr) (hC : 0 ≤ C) (hCD : 0 ≤ CD) :
    0 ≤ chartK₁ CA Cscr C CD := by
  have hk := blowupKappa_pos
  have hmP := mPlus_pos
  have hC1' := constC1_nonneg
  unfold chartK₁
  positivity

theorem chartK₂_nonneg {CA Cscr C : ℝ} (hCA : 0 ≤ CA) (hCscr : 0 ≤ Cscr) (hC : 0 ≤ C) :
    0 ≤ chartK₂ CA Cscr C := by
  have hk := blowupKappa_pos
  have hmP := mPlus_pos
  have hC1' := constC1_nonneg
  unfold chartK₂
  positivity

theorem sum_cellErr_eq {n : ℕ} (X : Fin n → ℂ) (L C ε δ : ℝ) (J : Finset (ℤ × ℤ)) (a : ℤ × ℤ → ℂ)
    (t : ℤ × ℤ → ℝ) (nb : ℤ × ℤ → ℕ) (v : ℤ × ℤ → ℂ → ℝ) :
    ∑ j ∈ J, cellErr X L C ε δ (a j) (t j) (nb j) (v j) =
      C * (∑ j ∈ J, stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (a j) (t j) L +
          (∑ j ∈ J, t j) * L + ∑ j ∈ J, |(nb j : ℝ) - (ptsIn X (a j) (t j)).card| +
          (∑ j ∈ J, ((ptsIn X (a j) (t j)).card : ℝ)) * δ + ∑ j ∈ J, t j) +
        ε / 2 * (∑ j ∈ J, ∫ x in sqAt (a j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) +
        C / ε * ∑ j ∈ J, ∫ x in sqAt (a j) (t j), ‖gradC (v j) x‖ ^ 2 := by
  unfold cellErr
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

end Lower

end Sphere

end SandierSerfaty

end
