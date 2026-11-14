/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
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
# The triangular field of Chapter 11

`triangularField` is the field `E_tri = ∇h_tri` of the triangular lattice, where `h_tri` is the mean-zero
periodic potential of the one-point triangular torus; with the sign convention of S. Serfaty, *Lectures on
Coulomb and Riesz gases*, `-div E_tri = 2π(∑_{p ∈ Λ_tri} δ_p - 1)`. Its membership in `Elec(Λ_tri, 1)` and its
energy are `triangularField_spec`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `E_tri = ∇h_tri`, the gradient of the mean-zero periodic potential of the one-point triangular torus
(`torusPotential`, which solves `-Δh = 2π(δ - 1)`, so `-div E_tri = 2π(Λ_tri - 1)` with the sign convention
of the *Lectures*). -/
@[expose] noncomputable def triangularField : ℂ → ℂ :=
  gradient (torusPotential triangularLattice (fun _ : Fin 1 ↦ 0))

end SandierSerfaty

end
