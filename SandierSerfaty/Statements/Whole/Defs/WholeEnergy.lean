/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Whole.Defs.LocalEnergy
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
# The energy of a field in the whole plane

`wholeEnergy χ Λ E` is the renormalized energy `W(E) = limsup_{R→∞} W(E, χ R)/|K_R|` of OpenAI, *Triangular
minimality for planar Coulomb renormalized energy*, `eq:whole-energy`, in `EReal`, for the cutoff family `χ`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The whole-plane energy `W(E) = limsup_{R→∞} W(E, χ_R)/|K_R|`, `|K_R| = (2R)²`
(paper `eq:whole-energy`), in `EReal`; the puncture limit is taken first. -/
@[expose] noncomputable def wholeEnergy (χ : ℝ → ℂ → ℝ) (Λ : Set ℂ) (E : ℂ → ℂ) : EReal :=
  limsup (fun R : ℝ ↦ ((((2 * R) ^ 2)⁻¹ : ℝ) : EReal) * localEnergy Λ E (χ R)) atTop

end SandierSerfaty

end
