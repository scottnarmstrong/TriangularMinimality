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
# The squares of Chapter 11

`cube ℓ` is the closed square `□_ℓ = [-ℓ/2, ℓ/2]²` centred at the origin, on which the energies of S. Serfaty,
*Lectures on Coulomb and Riesz gases*, §11.2.2, are computed.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The closed square `□_ℓ = [-ℓ/2, ℓ/2]²` of real side length `ℓ` centred at `0` (*Lectures*, §11.2.2). -/
@[expose] def cube (ℓ : ℝ) : Set ℂ :=
  Set.Icc (-(ℓ / 2)) (ℓ / 2) ×ℂ Set.Icc (-(ℓ / 2)) (ℓ / 2)

end SandierSerfaty

end
