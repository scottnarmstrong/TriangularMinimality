/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.Cube
public import SandierSerfaty.Statements.Jellium.Defs.CubeEnergy
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
# The jellium energy of Definition 11.4

`jelliumEnergy C0 C E` is the renormalized energy `W_{C0}(E, 1)` of an electric field with the constant `C0`
(S. Serfaty, *Lectures on Coulomb and Riesz gases*, Definition 11.4 and (11.2.12), with `s = 0` and `m = 1`).
By `exists_jelliumEnergy_eq_neutralEnergy` it equals the neutral energy `neutralEnergy C E` for every
sufficiently large `C0`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The jellium energy with constant `C0` of the *Lectures* (Definition 11.4, (11.2.12), at
`s = 0`, `m = 1`): `W_{C0}(E, 1) = limsup_{R → ∞} R⁻² [F^{□_R}(E, 1) + C0 (#(C ∩ □_R) - R²)]`. -/
@[expose] noncomputable def jelliumEnergy (C0 : ℝ) (C : Set ℂ) (E : ℂ → ℂ) : EReal :=
  limsup (fun R : ℝ ↦ (((R ^ 2)⁻¹ : ℝ) : EReal) *
    (cubeEnergy C E R + ((C0 * (((C ∩ cube R).ncard : ℝ) - R ^ 2) : ℝ) : EReal))) atTop

end SandierSerfaty

end
