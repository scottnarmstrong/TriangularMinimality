/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartLowerBound

/-!
# The good-square bound for a grid cell (sphere note, Theorem 6.14, step "summing over good squares")

`Lower.GoodSquareSpec Cscr ℓ₀ C` is the conclusion of Proposition 6.13 (`Lower.good_square`) as a named `Prop`;
`Lower.good_cell_bound` applies it to a good cell of a chart, with `ℓ = ℓ̃ = L`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The conclusion of Proposition 6.13 for the constants `C_scr, ℓ₀, C`. -/
@[expose] def GoodSquareSpec (Cscr ℓ₀ C : ℝ) : Prop :=
  ∀ {n : ℕ} (_ : 0 < n) (X : Fin n → ℂ),
    (∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) →
    ∀ (a : ℂ) (t ℓ ℓt mb δ : ℝ) (nb : ℕ) (v : ℂ → ℝ),
      (∀ x ∈ sqAt a t, ‖x‖ ≤ 2 * blowupScale n) → (nb : ℝ) = mb * t ^ 2 → 1 ≤ nb →
      mMinus ≤ mb → mb ≤ mPlus → 0 ≤ δ → (∀ x ∈ sqAt a t, |blowupDens n x - mb| ≤ δ) →
      max 100 ℓ₀ ≤ ℓ → ℓ ≤ ℓt → ℓt ≤ t / 8 →
      ContDiff ℝ ∞ v → (∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - mb)) →
      stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt ≤ ℓ ^ 3 * ℓt / Cscr →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (ptsIn X a t).card * cStar ≤ fnQ X a t + chartSum X a t +
          C * (ℓ * stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt / ℓt + t * ℓt +
            |(nb : ℝ) - (ptsIn X a t).card| + (ptsIn X a t).card * δ + t) +
          ε / 2 * (∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) +
          C / ε * ∫ x in sqAt a t, ‖gradC v x‖ ^ 2

theorem exists_goodSquareSpec (hR1 : Assembly.TorusBoundStatement) (hI : Input63Statement) :
    ∃ Cscr ℓ₀ C : ℝ, 1 ≤ Cscr ∧ 1 ≤ ℓ₀ ∧ 1 ≤ C ∧ GoodSquareSpec Cscr ℓ₀ C :=
  good_square hR1 hI

theorem good_cell_bound {Cscr ℓ₀ C : ℝ} (hGS : GoodSquareSpec Cscr ℓ₀ C) {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ}
    (h : ChartCtx n X ρ) {L : ℝ} {θ : ℝ × ℝ} {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ}
    (spec : CellSpec n (L ^ 2) θ ρ t nb v) (hL100 : 100 ≤ L) (hLℓ : ℓ₀ ≤ L) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) {j : ℤ × ℤ} (hj : j ∈ cellFin (L ^ 2) θ ρ)
    (hjS : stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L ≤
      L ^ 3 * L / Cscr) :
    ((ptsIn X (cellAt (L ^ 2) θ j) (t j)).card : ℝ) * cStar ≤
      fnQ X (cellAt (L ^ 2) θ j) (t j) + chartSum X (cellAt (L ^ 2) θ j) (t j) +
        cellErr X L C ε (4 * mPlus * L ^ 2 / blowupScale n) (cellAt (L ^ 2) θ j) (t j) (nb j) (v j) := by
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < L ^ 2 := by positivity
  obtain ⟨hj1, hj2, hnb, hv, hΔ, hV, hmL, hmH, hδj, hnb1⟩ := spec j hj
  have hδ0 : 0 ≤ 4 * mPlus * L ^ 2 / blowupScale n := by
    have := blowupScale_pos h.pos
    have := mPlus_pos
    positivity
  have hL2 : 10000 ≤ L ^ 2 := by nlinarith
  have htj : 0 < t j := by linarith
  have h8 : L ≤ t j / 8 := by nlinarith
  have hQ : ∀ x ∈ sqAt (cellAt (L ^ 2) θ j) (t j), ‖x‖ ≤ 2 * blowupScale n := fun x hx => by
    have := sqAt_cell_norm_le h hR0 hj (by linarith) hx
    linarith [h.le]
  have hnbt : (nb j : ℝ) = nb j / t j ^ 2 * t j ^ 2 := by field_simp
  have key := hGS h.pos X h.sep (cellAt (L ^ 2) θ j) (t j) L L (nb j / t j ^ 2)
    (4 * mPlus * L ^ 2 / blowupScale n) (nb j) (v j) hQ hnbt hnb1 hmL hmH hδ0 hδj
    (max_le hL100 hLℓ) le_rfl h8 hv hΔ hjS ε hε0 hε1
  have e : L * stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L / L =
      stripEnergy (fun y => truncPot X (1 / 4) y - v j y) (cellAt (L ^ 2) θ j) (t j) L := by
    field_simp
  rw [e] at key
  unfold cellErr
  linarith

end Lower

end Sphere

end SandierSerfaty

end
