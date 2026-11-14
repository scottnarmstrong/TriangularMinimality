/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Whole.Defs.PunctureFunctional
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
# The local energy of a field

`localEnergy Λ E ξ` is the local energy `W(E, ξ)` of OpenAI, *Triangular minimality for planar Coulomb
renormalized energy*, `eq:local-energy`: the limit, as `η ↓ 0`, of the puncture functional
`punctureFunctional Λ E ξ η`, written as a `limsup` in `EReal`. The limit exists and is finite for admissible
fields by `tendsto_punctureFunctional`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The local puncture energy `W(E, ξ) = lim_{η↓0} [punctureFunctional Λ E ξ η]` (paper
`eq:local-energy`), written as the `limsup` in `EReal`; by
`tendsto_punctureFunctional` the limit exists and is finite for admissible `(Λ, E)`. -/
@[expose] noncomputable def localEnergy (Λ : Set ℂ) (E : ℂ → ℂ) (ξ : ℂ → ℝ) : EReal :=
  limsup (punctureFunctional Λ E ξ) (𝓝[>] 0)

end SandierSerfaty

end
