/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartLarge

/-!
# The grid argument for one chart, second half: the error is `O(n/L) + O(L⁸ √n)` (sphere note, Theorem 6.14)

`Lower.large_chart_error`: the aggregated error of the good-square argument, `(C₁ + |c_*|) · rest + ∑_cells err`, is at most
`K₁ n / L + K₂ L⁸ √n`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem large_chart_error {Cscr C CD CA : ℝ} (hCscr : 1 ≤ Cscr) (hC : 1 ≤ C) (hCD : 0 ≤ CD) (hCA : 0 ≤ CA)
    (hDS : DiscSumSpec CD) {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ} (h : ChartCtx n X ρ)
    (hCA' : truncDirichlet X ρ ≤ CA * n) {L : ℝ} (hL : 100 ≤ L) (_hlarge : L ^ 4 ≤ Real.sqrt n)
    {θ : ℝ × ℝ} {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ} (spec : CellSpec n (L ^ 2) θ ρ t nb v)
    (hb1 : (∑ j ∈ cellFin (L ^ 2) θ ρ, ∫ z in stripSq (L ^ 2) θ (L / 2) (2 * L + 1) j, gradDensity X ρ z) *
        L ^ 2 ≤ 12 * (2 * L + 1 - L / 2) * ∫ z, gradDensity X ρ z)
    (hb2 : (∑ j ∈ cellFin (L ^ 2) θ ρ, ∫ z in stripSq (L ^ 2) θ (1 / 2) 2 j, gradDensity X ρ z) * L ^ 2 ≤
        12 * (2 - 1 / 2) * ∫ z, gradDensity X ρ z)
    {rest : ℝ}
    (hrest : rest ≤ 2 * Cscr * (∑ j ∈ cellFin (L ^ 2) θ ρ,
          stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L) +
        7 * (L ^ 2 * (cellFin (L ^ 2) θ ρ).card) + 16 * ρ * (L ^ 2 + 1)) :
    (constC1 + |cStar|) * rest +
      ∑ j ∈ cellFin (L ^ 2) θ ρ, cellErr X L C (L ^ 4 / Real.sqrt n) (4 * mPlus * L ^ 2 / blowupScale n)
        (cellAt (L ^ 2) θ j) (t j) (nb j) (v j) ≤
    chartK₁ CA Cscr C CD * ((n : ℝ) / L) + chartK₂ CA Cscr C * (L ^ 8 * Real.sqrt n) := by
  have hk := blowupKappa_pos
  have hmP := mPlus_pos
  have hpi := Real.pi_pos
  have hC1' := constC1_nonneg
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.pos
  have hu1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
  have hu0 : 0 < Real.sqrt n := by linarith
  have hu2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hR0 : 0 < L ^ 2 := by positivity
  have hs : blowupScale n = blowupKappa * Real.sqrt n := rfl
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos h.one_le
  have hρ : ρ ≤ 2 * blowupKappa * Real.sqrt n :=
    calc ρ ≤ 2 * blowupScale n := h.le
      _ = 2 * blowupKappa * Real.sqrt n := by rw [hs]; ring
  have hcN : 0 ≤ 4 * Real.pi * blowupKappa ^ 2 := by positivity
  have hcV : 0 ≤ 121 * Real.pi ^ 2 * mPlus ^ 2 / blowupKappa ^ 2 := by positivity
  set J := cellFin (L ^ 2) θ ρ with hJ
  set u := Real.sqrt n with hu
  -- the number of cells
  have hN : (J.card : ℝ) * L ^ 4 ≤ 4 * Real.pi * blowupKappa ^ 2 * u ^ 2 := by
    have h1 := card_cellFin_mul_le hR0 (θ := θ) h.one_le
    have h2 : Real.pi * ρ ^ 2 ≤ Real.pi * (2 * blowupKappa * u) ^ 2 := by gcongr
    have e1 : (L ^ 2) ^ 2 = L ^ 4 := by ring
    rw [e1] at h1
    linarith
  have hV0 : (121 * Real.pi ^ 2 * mPlus ^ 2 * (L ^ 2) ^ 6 / blowupScale n ^ 2) * u ^ 2 ≤
      121 * Real.pi ^ 2 * mPlus ^ 2 / blowupKappa ^ 2 * L ^ 12 := by
    rw [hs]
    apply le_of_eq
    field_simp
  have hG0 : ∫ z, gradDensity X ρ z ≤ CA * u ^ 2 := by
    rw [hu2]
    exact (integral_gradDensity_le h.pos X h.inj h.sep h.ne).trans hCA'
  have hG00 : 0 ≤ ∫ z, gradDensity X ρ z := integral_nonneg (gradDensity_nonneg X ρ)
  have hSA : ∑ j ∈ J, ∫ x in sqAt (cellAt (L ^ 2) θ j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 ≤ CA * u ^ 2 := by
    rw [hu2]
    exact (sum_cell_energy_le h hR0 (fun j hj => (spec j hj).2.1) J (Finset.Subset.refl _)).trans hCA'
  have hSP : ∑ j ∈ J, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ) ≤ u ^ 2 := by
    rw [hu2]; exact agg_p h hR0 (fun j hj => (spec j hj).2.1)
  have hS := agg_strip h (by linarith : 2 ≤ L) spec hb1
  have hT := agg_t spec
  have hSV := agg_V spec
  have hD := hDS h (by nlinarith only [hL] : 3 ≤ L ^ 2) spec hb2
  have e18 : (12 * (2 - 1 / 2) : ℝ) = 18 := by norm_num
  rw [e18] at hD
  have hδ : 4 * mPlus * L ^ 2 / blowupScale n * (blowupKappa * u) = 4 * mPlus * L ^ 2 := by
    rw [← hs]; exact div_mul_cancel₀ _ (blowupScale_pos h.pos).ne'
  have hδ0 : 0 ≤ 4 * mPlus * L ^ 2 / blowupScale n := by
    have := blowupScale_pos h.pos; positivity
  have hSV0 : 0 ≤ ∑ j ∈ J, ∫ x in sqAt (cellAt (L ^ 2) θ j) (t j), ‖gradC (v j) x‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => setIntegral_nonneg (measurableSet_sqAt _ _) fun x _ => by positivity
  have herr := chart_error_le (|cStar| + constC1) C Cscr CD mPlus blowupKappa CA
    (4 * Real.pi * blowupKappa ^ 2) (121 * Real.pi ^ 2 * mPlus ^ 2 / blowupKappa ^ 2) u L (J.card : ℝ)
    (∑ j ∈ J, stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L)
    (∑ j ∈ J, t j) (∑ j ∈ J, |(nb j : ℝ) - (ptsIn X (cellAt (L ^ 2) θ j) (t j)).card|)
    (∑ j ∈ J, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ))
    (∑ j ∈ J, ∫ x in sqAt (cellAt (L ^ 2) θ j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2)
    (∑ j ∈ J, ∫ x in sqAt (cellAt (L ^ 2) θ j) (t j), ‖gradC (v j) x‖ ^ 2)
    (∫ z, gradDensity X ρ z) rest (121 * Real.pi ^ 2 * mPlus ^ 2 * (L ^ 2) ^ 6 / blowupScale n ^ 2) ρ
    (4 * mPlus * L ^ 2 / blowupScale n) (by positivity) hC hCscr hCD hmP hk hCA hcN hcV hu1 hL1
    (Nat.cast_nonneg _) hN (by have := blowupScale_pos h.pos; positivity) hV0 hS hG00 hG0
    (hT.trans (le_of_eq (by ring))) (by simpa using hD) hSP hSA hSV0 hSV hrest hρ0.le hρ hδ0 hδ
  have hsumE := sum_cellErr_eq X L C (L ^ 4 / u) (4 * mPlus * L ^ 2 / blowupScale n) J
    (fun j => cellAt (L ^ 2) θ j) t nb v
  rw [hsumE]
  have hu2' : u ^ 2 = n := hu2
  rw [hu2'] at herr
  unfold chartK₁ chartK₂
  have e1 : C * (∑ j ∈ J, stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L +
      (∑ j ∈ J, t j) * L + ∑ j ∈ J, |(nb j : ℝ) - (ptsIn X (cellAt (L ^ 2) θ j) (t j)).card| +
      (∑ j ∈ J, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ)) * (4 * mPlus * L ^ 2 / blowupScale n) +
      ∑ j ∈ J, t j) = C * (∑ j ∈ J, stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L +
      L * (∑ j ∈ J, t j) + ∑ j ∈ J, |(nb j : ℝ) - (ptsIn X (cellAt (L ^ 2) θ j) (t j)).card| +
      (4 * mPlus * L ^ 2 / blowupScale n) * (∑ j ∈ J, ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ)) +
      ∑ j ∈ J, t j) := by ring
  rw [e1]
  linarith [herr]

end Lower

end Sphere

end SandierSerfaty

end
