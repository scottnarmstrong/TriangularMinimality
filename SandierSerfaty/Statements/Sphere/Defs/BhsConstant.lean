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
# The Brauchart–Hardin–Saff constant

`bhsConstant` is `C_BHS = 2 log 2 + ½ log(2/3) + 3 log(√π / Γ(1/3))`, the constant in the linear term of the
minimal logarithmic energy on the sphere (OpenAI, *Triangular minimality for planar Coulomb renormalized
energy*, Corollary 1.3, `eq:bhs-constant`).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The Brauchart–Hardin–Saff constant `C_BHS = 2 log 2 + ½ log(2/3) + 3 log(√π/Γ(1/3))`
(paper `eq:bhs-constant`). -/
@[expose] noncomputable def bhsConstant : ℝ :=
  2 * Real.log 2 + (1 / 2) * Real.log (2 / 3) + 3 * Real.log (Real.sqrt Real.pi / Real.Gamma (1 / 3))

end SandierSerfaty

end
