/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
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
import SandierSerfaty.Proofs.Jellium.DivTwoPiTriangularEnergyLeNeutralEnergy

/-!
# The lower bound for the jellium energy of fields

`div_two_pi_triangularEnergy_le_neutralEnergy`: for every configuration `C` and every electric field
`E ∈ Elec(C, 1)`, the neutral energy satisfies `W^neu(E, 1) ≥ W_tri / (2π)`, in the extended reals. This is
the lower bound for the jellium energy of fields of S. Serfaty, *Lectures on Coulomb and Riesz gases*, Chapter
11, in dimension two with `s = 0` and `m = 1`. A configuration is a set of points, so it has no multiple
points.

The proof is `SandierSerfaty.Proofs.div_two_pi_triangularEnergy_le_neutralEnergy`, in the module
`SandierSerfaty.Proofs.Jellium.DivTwoPiTriangularEnergyLeNeutralEnergy`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **The lower bound for the jellium energy of fields** (*Lectures*, Chapter 11): for every configuration `C`
and every `E ∈ Elec(C, 1)`, `W^neu(E, 1) ≥ W_tri / (2π)`. -/
theorem div_two_pi_triangularEnergy_le_neutralEnergy (C : Set ℂ) (E : ℂ → ℂ) (hE : E ∈ elec C) :
    ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ≤ neutralEnergy C E :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.div_two_pi_triangularEnergy_le_neutralEnergy C E hE
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
