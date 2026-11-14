/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Sphere.Defs.LogPairEnergy
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
# The logarithmic energy of points on the sphere

`logConfigEnergy y` is the logarithmic energy `-∑_{i ≠ j} log ‖y i - y j‖` of `n` points of the unit sphere
`S² ⊂ ℝ³`, summed over ordered pairs, with value `+∞` for a collision (OpenAI, *Triangular minimality for
planar Coulomb renormalized energy*, Corollary 1.3).
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The logarithmic energy of `n` points of the unit sphere `S² ⊂ ℝ³`, summed over ordered pairs `i ≠ j`
(paper Corollary 1.3). -/
@[expose] noncomputable def logConfigEnergy {n : ℕ}
    (y : Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EReal :=
  ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, logPairEnergy (y p.1) (y p.2)

end SandierSerfaty

end
