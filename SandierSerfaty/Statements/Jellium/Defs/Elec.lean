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
# The electric fields of a configuration

`elec C` is the class `Elec(C, 1)` of electric fields compatible with the configuration `C` and background
density one (S. Serfaty, *Lectures on Coulomb and Riesz gases*, Definition 11.1 and (11.2.1), in dimension two
with `s = 0` and `m = 1`).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `Elec(C, 1)` (*Lectures*, Definition 11.1, (11.2.1), at `d = 2`, `s = 0`, `m = 1`):
`C` is locally finite, `E ∈ L¹_loc(ℂ; ℂ)`, and `-div E = 2π (∑_{p ∈ C} δ_p - 1)` in the weak sense:
`∫ ⟪E, ∇φ⟫ = 2π (∑_{p ∈ C} φ p - ∫ φ)` for every smooth compactly supported real `φ`. -/
@[expose] def elec (C : Set ℂ) : Set (ℂ → ℂ) :=
  {E | (∀ R : ℝ, (C ∩ Metric.closedBall 0 R).Finite) ∧ LocallyIntegrable E volume ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, inner ℝ (E x) (gradient φ x)) = 2 * Real.pi * ((∑ᶠ p ∈ C, φ p) - (∫ x, φ x))}

end SandierSerfaty

end
