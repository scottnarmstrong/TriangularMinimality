/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
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
public import SandierSerfaty.Assembly.JelliumBounds
public import SandierSerfaty.Statements.Torus.Theorems.MulTriangularEnergyLeTorusEnergy

/-!
# Proof of `SandierSerfaty.configEnergy_triangularLattice`

`SandierSerfaty.Proofs.configEnergy_triangularLattice` proves the statement
`SandierSerfaty.configEnergy_triangularLattice` of the module
`SandierSerfaty.Statements.Jellium.Theorems.ConfigEnergyTriangularLattice`. It is
`Assembly.triangularConfigEnergy_of_torusBound` applied to the square-torus bound
`SandierSerfaty.mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

theorem configEnergy_triangularLattice :
    configEnergy (triangularLattice : Set ℂ) = ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ∧
      ∀ C : Set ℂ, configEnergy (triangularLattice : Set ℂ) ≤ configEnergy C :=
  Assembly.triangularConfigEnergy_of_torusBound @SandierSerfaty.mul_triangularEnergy_le_torusEnergy

end SandierSerfaty.Proofs

end
