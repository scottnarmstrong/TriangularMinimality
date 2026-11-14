/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.IsCutoffFamily
public import SandierSerfaty.Statements.Whole.Defs.WholeEnergy
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
public import SandierSerfaty.Assembly.WholeEnergyBound
public import SandierSerfaty.Statements.Torus.Theorems.MulTriangularEnergyLeTorusEnergy

/-!
# Proof of `SandierSerfaty.triangularEnergy_le_wholeEnergy`

`SandierSerfaty.Proofs.triangularEnergy_le_wholeEnergy` proves the statement
`SandierSerfaty.triangularEnergy_le_wholeEnergy` of the module
`SandierSerfaty.Statements.Whole.Theorems.TriangularEnergyLeWholeEnergy`. It is
`Assembly.wholeEnergyBound_of_torusBound` applied to the square-torus bound
`SandierSerfaty.mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

theorem triangularEnergy_le_wholeEnergy (χ : ℝ → ℂ → ℝ) (hχ : IsCutoffFamily χ)
    (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E) :
    (triangularEnergy : EReal) ≤ wholeEnergy χ Λ E :=
  Assembly.wholeEnergyBound_of_torusBound @SandierSerfaty.mul_triangularEnergy_le_torusEnergy χ hχ Λ E hE

end SandierSerfaty.Proofs

end
