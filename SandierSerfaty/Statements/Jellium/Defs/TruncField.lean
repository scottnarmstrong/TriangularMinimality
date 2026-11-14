/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
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
# Truncated fields

`truncField C η E` is the field `E` truncated at the radii `η` around the points of `C` (S. Serfaty, *Lectures
on Coulomb and Riesz gases*, (11.2.4)).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The truncation `E_η(x) = E(x) - ∑_{p ∈ C} ∇f_{η_p}(x - p)` (*Lectures*, (11.2.4)), for a
radius family `η` indexed by the points (values off `C` are unused). The sum is finite at every `x` when
`C` is locally finite and `η` is bounded. -/
@[expose] noncomputable def truncField (C : Set ℂ) (η : ℂ → ℝ) (E : ℂ → ℂ) (x : ℂ) : ℂ :=
  E x - ∑ᶠ p ∈ C, gradient (truncLog (η p)) (x - p)

end SandierSerfaty

end
