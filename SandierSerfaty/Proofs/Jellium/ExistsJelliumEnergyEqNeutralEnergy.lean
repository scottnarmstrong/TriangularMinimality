/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.NeutralBridge
public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.JelliumEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy

/-!
# Proof of `SandierSerfaty.exists_jelliumEnergy_eq_neutralEnergy`

`SandierSerfaty.Proofs.exists_jelliumEnergy_eq_neutralEnergy` proves the statement
`SandierSerfaty.exists_jelliumEnergy_eq_neutralEnergy` of the module
`SandierSerfaty.Statements.Jellium.Theorems.ExistsJelliumEnergyEqNeutralEnergy`.

The constant is `C0* = c₀(1)/(2π) = log 2 + π/32` (`cQuarter 1 / (2π)`), and the statement for each `C0 ≥ C0*`
is `SandierSerfaty.jelliumEnergy_eq_neutralEnergy`: the energy bound
`½∫_{□_ℓ}|E_{1/4}|² ≤ 2πF^{□_ℓ} + c₀ #(C ∩ □_ℓ)` and the density lemma
(`SandierSerfaty.tendsto_ncard_cube_div_sq`).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.exists_jelliumEnergy_eq_neutralEnergy`. -/
theorem exists_jelliumEnergy_eq_neutralEnergy :
    ∃ C0star : ℝ, ∀ C0 : ℝ, C0star ≤ C0 → ∀ (C : Set ℂ), ∀ E ∈ elec C,
      jelliumEnergy C0 C E = neutralEnergy C E :=
  ⟨cQuarter 1 / (2 * Real.pi), fun _ hC0 _ _ hE => jelliumEnergy_eq_neutralEnergy hC0 hE⟩

end SandierSerfaty.Proofs

end
