/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.Cube
public import SandierSerfaty.Statements.Jellium.Defs.NnRadius
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
# The truncation radii relative to a square

`cubeRadius C ℓ p` is the truncation radius `r̃_p` of a point `p` of `C` relative to the square `□_ℓ` (S.
Serfaty, *Lectures on Coulomb and Riesz gases*, (11.2.3), with `m = 1`): the nearest-neighbour radius `r_p`
well inside the square, `1/4` near its boundary and outside it, interpolated linearly in between.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `r̃_p`, the radius relative to `□_ℓ` (*Lectures*, (11.2.3), `m = 1`):
`r_p` if `p ∈ □_ℓ` and `dist(p, ∂□_ℓ) ≥ 2`; `¼` if `p ∉ □_ℓ` or `dist(p, ∂□_ℓ) ≤ 1`;
`t r_p + (1 - t) ¼` if `p ∈ □_ℓ` and `dist(p, ∂□_ℓ) = 1 + t`, `t ∈ [0, 1]`. -/
@[expose] noncomputable def cubeRadius (C : Set ℂ) (ℓ : ℝ) (p : ℂ) : ℝ :=
  open scoped Classical in
  if p ∈ cube ℓ ∧ 2 ≤ Metric.infDist p (frontier (cube ℓ)) then nnRadius C p
  else if p ∉ cube ℓ ∨ Metric.infDist p (frontier (cube ℓ)) ≤ 1 then 1 / 4
  else (Metric.infDist p (frontier (cube ℓ)) - 1) * nnRadius C p +
    (1 - (Metric.infDist p (frontier (cube ℓ)) - 1)) * (1 / 4)

end SandierSerfaty

end
