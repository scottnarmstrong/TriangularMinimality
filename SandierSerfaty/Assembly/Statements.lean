/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Defs
public import SandierSerfaty.Screening.SquareCell
public import SandierSerfaty.Statements.Jellium.Defs.ConfigEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import SandierSerfaty.Statements.Jellium.Defs.TruncField
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.SquareLattice

/-!
# The statements assumed by the conditional assembly of the jellium bounds

Three `Prop`s, written out:

* `ScreeningStatement`: **I4**, the screening theorem of the screening note's Theorem 4.1
  (`exists_screened_neumannChargeField`).
  The constants `ℓ₀ = 8 λ₀`, `C_scr = 512 C₁`, `C_S` are existential, fixed *before* the data (for
  the density window `[mLo, mHi]`); the hypothesis `S ≤ ℓc³ ℓt / C_scr` is an explicit inequality.
  `ScreeningData` is its body for fixed constants.
* `TorusBoundStatement`: the square-torus bound `mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2).
* `NeutralEnergyBoundStatement`: the neutral-energy bound `div_two_pi_triangularEnergy_le_neutralEnergy`.

`ScreeningStatement` (I4) is proved: `Assembly.screeningStatement` (`Assembly/JelliumBounds.lean`).
`TorusBoundStatement` is the hypothesis of `neutralEnergyBound_of_torusBound`, `triangularConfigEnergy_of_torusBound`, `wholeEnergyBound_of_torusBound` and `sphereAsymptotics_of_torusBound`; it is proved by the
certificate (`CertData.CertificateGoal`). `neutralEnergyBound_of_screening_torusBound` and `triangularConfigEnergy_of_neutralEnergyBound` are the conditional assemblies.
-/

open MeasureTheory Metric
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Assembly

/-- The conclusion of I4 for fixed constants and a fixed density window (the data of
`ScreeningStatement`): for all admissible `c, t, m, ℓc, ℓt, N, C, α, E` the screened field exists. -/
@[expose] def ScreeningData (mLo mHi ℓ₀ C_scr C_S : ℝ) : Prop :=
  ∀ (c : ℂ) (t m ℓc ℓt : ℝ) (N : ℕ) (C : Set ℂ) (α : ℂ → ℝ) (E : ℂ → ℂ),
    mLo ≤ m → m ≤ mHi → m * t ^ 2 = N → ℓ₀ ≤ ℓc → ℓc ≤ ℓt → 8 * ℓt ≤ t →
    (∀ R : ℝ, (C ∩ closedBall 0 R).Finite) →
    IsChargeField (interior (sq c (t - 1))) m C E →
    (∀ p ∈ C, 0 < α p ∧ α p ≤ 1 / 4) →
    (∀ p ∈ C, p ∉ sq c (t - 2) → α p = 1 / 4) →
    (∀ p ∈ C ∩ sq c (t - 2 * ℓt), ∀ q ∈ C ∩ sq c (t - 2 * ℓt), p ≠ q →
      α p + α q ≤ ‖p - q‖) →
    ∫⁻ x in sq c t, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≠ ⊤ →
    let S : ℝ := (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal
    (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)) ≠ ⊤ →
    S ≤ ℓc ^ 3 * ℓt / C_scr →
    ∃ (Y : Finset ℂ) (ρ : ℂ → ℝ) (E' : ℂ → ℂ),
      Y.card = N ∧ (∀ y ∈ Y, y ∈ interior (sq c t)) ∧
      (∀ y ∈ Y, 0 < ρ y ∧ ρ y ≤ 1 / 4 ∧ closedBall y (ρ y) ⊆ interior (sq c t)) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ρ y + ρ y' ≤ ‖y - y'‖) ∧
      IsNeumannChargeField (sq c t) m Y E' ∧
      locEnergy m (Y : Set ℂ) ρ E' (sq c t) ≤
        locEnergy m C α E (sq c t) +
          ((C_S * (ℓc * S / ℓt + t * ℓt +
            (C ∩ (sq c t \ sq c (t - 4 * ℓt))).ncard) : ℝ) : EReal)

/-- **I4: screening of fields on a square** (screening note, Theorem 4.1; replaces Prop. 7.18 / App. A).
For a density window `0 < mLo ≤ mHi` there are constants `ℓ₀, C_scr, C_S > 0`, depending only on the window,
such that every charge field `E` on `int (sq c (t-1))` with charges `C` and admissible truncation radii `α`,
whose quarter-truncated energy `S` in the strip `sq c (t-ℓt) ∖ sq c (t-4ℓt)` is at most `ℓc³ ℓt / C_scr`,
is replaced by a zero-flux field `E'` on `sq c t` with exactly `N = m t²` charges `Y` and disjoint
radii `ρ`, with the local energy bound `G_Q(ρ)[E'; Y] ≤ G_Q(α)[E; C] + C_S (ℓc S/ℓt + t ℓt + n_∂)`
(see `ScreeningData` for the body). -/
@[expose] def ScreeningStatement : Prop :=
  ∀ {mLo mHi : ℝ}, 0 < mLo → mLo ≤ mHi →
    ∃ ℓ₀ C_scr C_S : ℝ, 0 < ℓ₀ ∧ 0 < C_scr ∧ 0 < C_S ∧ ScreeningData mLo mHi ℓ₀ C_scr C_S

/-- The statement of `mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2), as a `Prop`. -/
@[expose] def TorusBoundStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : Fin n → ℂ, (∀ i j, a i - a j ∈ squareLattice n → i = j) →
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a

/-- The statement of `div_two_pi_triangularEnergy_le_neutralEnergy`, as a `Prop`. -/
@[expose] def NeutralEnergyBoundStatement : Prop :=
  ∀ (C : Set ℂ) (E : ℂ → ℂ), E ∈ elec C →
    ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ≤ neutralEnergy C E

end Assembly

end SandierSerfaty

end
