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
# The neutral jellium energy

`neutralEnergy C E` is the energy `W^neu(E, 1) = limsup_{ℓ → ∞} ℓ⁻² F^{□_ℓ}(E, 1)` of a field whose
configuration has density one, and `+∞` otherwise. It is the renormalized energy of S. Serfaty, *Lectures on
Coulomb and Riesz gases*, Definition 11.4, without the term with the constant `C0`; the two agree for every
sufficiently large `C0` (`exists_jelliumEnergy_eq_neutralEnergy`).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The neutral jellium energy: `W^neu(E, 1) = limsup_{ℓ → ∞} ℓ⁻² F^{□_ℓ}(E, 1)`
(real `ℓ`) if `#(C ∩ □_ℓ)/ℓ² → 1`, and `+∞` otherwise. -/
@[expose] noncomputable def neutralEnergy (C : Set ℂ) (E : ℂ → ℂ) : EReal :=
  open scoped Classical in
  if Tendsto (fun ℓ : ℝ ↦ ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) then
    limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ) atTop
  else ⊤

end SandierSerfaty

end
