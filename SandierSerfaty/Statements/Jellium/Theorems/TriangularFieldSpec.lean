/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import SandierSerfaty.Statements.Jellium.Defs.TriangularField
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
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
import SandierSerfaty.Proofs.Jellium.TriangularFieldSpec

/-!
# The triangular field and its energy

`triangularField_spec`: the triangular field lies in `Elec(Λ_tri, 1)` and has neutral energy
`W^neu(E_tri, 1) = W_tri / (2π)` (S. Serfaty, *Lectures on Coulomb and Riesz gases*, Proposition 11.11, with
one point per period).

The proof is `SandierSerfaty.Proofs.triangularField_spec`, in the module
`SandierSerfaty.Proofs.Jellium.TriangularFieldSpec`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **The triangular field**: `E_tri ∈ Elec(Λ_tri, 1)` and
`W^neu(E_tri, 1) = W_tri / (2π)` (*Lectures*, Proposition 11.11 with `N = 1`). -/
theorem triangularField_spec :
    triangularField ∈ elec (triangularLattice : Set ℂ) ∧
      neutralEnergy (triangularLattice : Set ℂ) triangularField =
        ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.triangularField_spec
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
