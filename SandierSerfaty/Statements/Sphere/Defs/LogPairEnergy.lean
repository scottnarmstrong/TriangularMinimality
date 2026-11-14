/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

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

/-!
# The logarithmic pair energy

`logPairEnergy x y` is `-log ‖x - y‖` for points of `ℝ³`, with value `+∞` when `x = y` (OpenAI, *Triangular
minimality for planar Coulomb renormalized energy*, Corollary 1.3: "a collision has energy `+∞`").
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The logarithmic pair energy `-log ‖x - y‖` on `ℝ³`, with `+∞` for a collision
(paper Corollary 1.3: "a collision has energy `+∞`"). -/
@[expose] noncomputable def logPairEnergy (x y : EuclideanSpace ℝ (Fin 3)) : EReal :=
  if x = y then ⊤ else ((-Real.log ‖x - y‖ : ℝ) : EReal)

end SandierSerfaty

end
