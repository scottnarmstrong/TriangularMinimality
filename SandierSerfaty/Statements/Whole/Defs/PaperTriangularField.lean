/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
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
# The triangular field of Theorem 1.1

`paperTriangularField` is the field `E_△ = -∇h_△` of OpenAI, *Triangular minimality for planar Coulomb
renormalized energy*, Theorem 1.1, where `h_△` is the mean-zero periodic potential of the one-point triangular
torus. Its admissibility and energy are `paperTriangularField_spec`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The paper's `E_△ = -∇h_△` (before Theorem 1.1), `h_△` the mean-zero periodic solution of
`-Δh = 2π(δ₀ - 1)` on `ℂ/Λ_△` (`torusPotential`). (The field `triangularField` of the jellium statements is
`+∇h_△`.) -/
@[expose] noncomputable def paperTriangularField : ℂ → ℂ :=
  fun x ↦ -(gradient (torusPotential triangularLattice (fun _ : Fin 1 ↦ 0)) x)

end SandierSerfaty

end
