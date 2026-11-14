/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

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

/-!
# The truncated logarithm

`truncLog η x = (-log|x| + log η)₊` is the function `f_η` of S. Serfaty, *Lectures on Coulomb and Riesz
gases*, (4.1.18), in dimension two.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `f_η(x) = (g(x) - g(η))₊ = (-log|x| + log η)₊` (*Lectures*, (4.1.18), `g = -log|·|`). -/
@[expose] noncomputable def truncLog (η : ℝ) (x : ℂ) : ℝ :=
  max (-Real.log ‖x‖ - -Real.log η) 0

end SandierSerfaty

end
