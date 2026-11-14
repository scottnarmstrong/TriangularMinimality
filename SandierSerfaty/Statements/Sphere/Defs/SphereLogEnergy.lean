/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Sphere.Defs.LogConfigEnergy
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
# The minimal logarithmic energy on the sphere

`sphereLogEnergy n` is the minimal logarithmic energy `E_log(n)` of `n` points of the unit sphere `S²`
(OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, Corollary 1.3), defined as the
infimum, in `EReal`, of `logConfigEnergy` over `(S²)ⁿ`. The paper takes the minimum, which is attained; the
infimum has the same value.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `E_log(n) = min_{(S²)^n} E` (paper Corollary 1.3), as an infimum in `EReal`
(the paper's minimum, which is attained, has the same value). -/
@[expose] noncomputable def sphereLogEnergy (n : ℕ) : EReal :=
  ⨅ y : Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, logConfigEnergy y

end SandierSerfaty

end
