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
# The admissible class

`IsAdmissibleField Λ E` says that the pair `(Λ, E)` belongs to the admissible class `𝒜₁` of OpenAI,
*Triangular minimality for planar Coulomb renormalized energy*, `eq:admissible`: `Λ` is locally finite, `E` is
locally integrable, `div E = 2π(ν_Λ - 1)` and `curl E = 0` in the sense of distributions, and `Λ` has bounded
density.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- The admissible class `𝒜₁` of the paper (`eq:admissible`), as a
predicate on the pair `(Λ, E)` (`Λ` is determined by `E`, as `ν_Λ = 1 + (2π)⁻¹ div E`): `Λ ⊆ ℂ` is locally
finite (a set, so simple), `E ∈ L¹_loc(ℂ; ℂ)`, and in the sense of distributions `div E = 2π(ν_Λ - 1)`
(tested against real `φ ∈ C_c^∞`: `∫ ⟪E, ∇φ⟫ = -2π(∑_{p∈Λ} φ p - ∫ φ)`), `curl E = 0`
(`∫ ⟪E, i∇φ⟫ = 0`), and `sup_{R>1} ν_Λ(B_R)/|B_R| < ∞` (`∃ Θ, ν_Λ(B_R) ≤ Θ π R²`).
Convention `ℂ = ℝ²`, `E = E₁ + i E₂`, `∇φ = ∂₁φ + i ∂₂φ`. -/
@[expose] def IsAdmissibleField (Λ : Set ℂ) (E : ℂ → ℂ) : Prop :=
  (∀ R : ℝ, (Λ ∩ Metric.closedBall 0 R).Finite) ∧ LocallyIntegrable E volume ∧
  (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, inner ℝ (E x) (gradient φ x)) = -(2 * Real.pi * ((∑ᶠ p ∈ Λ, φ p) - (∫ x, φ x)))) ∧
  (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, inner ℝ (E x) (Complex.I * gradient φ x)) = 0) ∧
  ∃ Θ : ℝ, ∀ R : ℝ, 1 < R → ((Λ ∩ Metric.ball 0 R).ncard : ℝ) ≤ Θ * (Real.pi * R ^ 2)

end SandierSerfaty

end
