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
# The nearest-neighbour radii

`nnRadius C p` is the radius `r_p = ¼ min(min_{q ∈ C, q ≠ p} |q - p|, 1)` of a point `p` of the configuration
`C` (S. Serfaty, *Lectures on Coulomb and Riesz gases*, (11.2.2), with `m = 1`).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `r_p = ¼ min(min_{q ∈ C, q ≠ p} |q - p|, 1)` (*Lectures*, (11.2.2), `m = 1`, simple
point; `min ∅ = +∞`, realized by inserting `1` into the set whose infimum is taken). -/
@[expose] noncomputable def nnRadius (C : Set ℂ) (p : ℂ) : ℝ :=
  (1 / 4) * sInf (insert 1 ((fun q ↦ ‖q - p‖) '' (C \ {p})))

end SandierSerfaty

end
