/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.JelliumEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import SandierSerfaty.Proofs.Jellium.ExistsJelliumEnergyEqNeutralEnergy

/-!
# The jellium energy of Definition 11.4 equals the neutral energy

`exists_jelliumEnergy_eq_neutralEnergy`: there is a constant `C0*` such that, for every `C0 ≥ C0*`, every
configuration `C` and every `E ∈ Elec(C, 1)`, the energy `W_{C0}(E, 1)` of S. Serfaty, *Lectures on Coulomb
and Riesz gases*, Definition 11.4, equals the neutral energy `W^neu(E, 1)`. So the lower bounds stated for
`neutralEnergy` hold for the energy of Definition 11.4 as well.

The proof is `SandierSerfaty.Proofs.exists_jelliumEnergy_eq_neutralEnergy`, in the module
`SandierSerfaty.Proofs.Jellium.ExistsJelliumEnergyEqNeutralEnergy`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **The energy of Definition 11.4 is the neutral energy for large `C0`**: there is `C0*` such that for every
`C0 ≥ C0*`, every configuration `C` and every `E ∈ Elec(C, 1)`, the energy `W_{C0}(E, 1)` of the *Lectures*
(Definition 11.4) equals `W^neu(E, 1)`. -/
theorem exists_jelliumEnergy_eq_neutralEnergy :
    ∃ C0star : ℝ, ∀ C0 : ℝ, C0star ≤ C0 → ∀ (C : Set ℂ), ∀ E ∈ elec C,
      jelliumEnergy C0 C E = neutralEnergy C E :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.exists_jelliumEnergy_eq_neutralEnergy
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
