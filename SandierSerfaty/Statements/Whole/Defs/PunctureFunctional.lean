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
# The puncture functional

`punctureFunctional Λ E ξ η` is the truncated energy `½ ∫_{ℂ∖⋃_{p∈Λ} B(p,η)} ξ |E|² + π log η ∑_{p∈Λ} ξ(p)` of
the field `E` with weight `ξ`, whose limit as `η ↓ 0` is the local energy of OpenAI, *Triangular minimality
for planar Coulomb renormalized energy*, `eq:local-energy`. It takes values in `EReal`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The `η`-truncated puncture functional
`½ ∫_{ℂ∖⋃_{p∈Λ} B(p,η)} ξ |E|² + π log η ∑_{p∈Λ} ξ(p)` of the paper's `eq:local-energy`
for a real weight `ξ` (the paper uses `ξ = χ R`), valued in `EReal`.
The integral is a lower Lebesgue integral (no Bochner junk value `0` for a non-integrable integrand;
`+∞` is then reported as `+∞`). -/
@[expose] noncomputable def punctureFunctional (Λ : Set ℂ) (E : ℂ → ℂ) (ξ : ℂ → ℝ) (η : ℝ) : EReal :=
  (((1 / 2 : ℝ)) : EReal) *
      (((∫⁻ x in (⋃ p ∈ Λ, Metric.ball p η)ᶜ, ENNReal.ofReal (ξ x * ‖E x‖ ^ 2) : ℝ≥0∞) : EReal) -
        ((∫⁻ x in (⋃ p ∈ Λ, Metric.ball p η)ᶜ, ENNReal.ofReal (-(ξ x * ‖E x‖ ^ 2)) : ℝ≥0∞) : EReal)) +
    ((Real.pi * Real.log η * ∑ᶠ p ∈ Λ, ξ p : ℝ) : EReal)

end SandierSerfaty

end
