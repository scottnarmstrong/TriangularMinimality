/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Sphere.Defs.BhsConstant
public import SandierSerfaty.Statements.Sphere.Defs.SphereLogEnergy
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import SandierSerfaty.Assembly.SphereAsymptotics
public import SandierSerfaty.Statements.Torus.Theorems.MulTriangularEnergyLeTorusEnergy

/-!
# Proof of `SandierSerfaty.sphereLogEnergy_asymptotics`

`SandierSerfaty.Proofs.sphereLogEnergy_asymptotics` proves the statement
`SandierSerfaty.sphereLogEnergy_asymptotics` of the module
`SandierSerfaty.Statements.Sphere.Theorems.SphereLogEnergyAsymptotics`. It is
`Assembly.sphereAsymptotics_of_torusBound` applied to the square-torus bound
`SandierSerfaty.mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

theorem sphereLogEnergy_asymptotics :
    ∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
      sphereLogEnergy n =
        ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + bhsConstant * n + r n : ℝ) :
          EReal) :=
  Assembly.sphereAsymptotics_of_torusBound @SandierSerfaty.mul_triangularEnergy_le_torusEnergy

end SandierSerfaty.Proofs

end
