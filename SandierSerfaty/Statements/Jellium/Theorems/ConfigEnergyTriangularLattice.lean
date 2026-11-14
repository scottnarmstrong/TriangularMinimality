/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Jellium.Defs.ConfigEnergy
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
import SandierSerfaty.Proofs.Jellium.ConfigEnergyTriangularLattice

/-!
# The triangular lattice minimizes the energy of configurations

`configEnergy_triangularLattice`: the triangular lattice has energy `𝕎(Λ_tri, 1) = W_tri / (2π)`, and every
configuration `C` has energy `𝕎(C, 1) ≥ 𝕎(Λ_tri, 1)`. This is the minimality of the triangular lattice for the
energy of configurations of S. Serfaty, *Lectures on Coulomb and Riesz gases*, Definition 11.6, in dimension
two with `s = 0` and `m = 1` (the conjecture discussed in §11.5 of the lectures).

The proof is `SandierSerfaty.Proofs.configEnergy_triangularLattice`, in the module
`SandierSerfaty.Proofs.Jellium.ConfigEnergyTriangularLattice`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **The triangular lattice minimizes the energy of configurations**: `𝕎(Λ_tri, 1) = W_tri / (2π)` and
`𝕎(C, 1) ≥ 𝕎(Λ_tri, 1)` for every `C`. -/
theorem configEnergy_triangularLattice :
    configEnergy (triangularLattice : Set ℂ) = ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ∧
      ∀ C : Set ℂ, configEnergy (triangularLattice : Set ℂ) ≤ configEnergy C :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.configEnergy_triangularLattice
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
