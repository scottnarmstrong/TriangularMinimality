/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
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
# The energy of a configuration

`configEnergy C` is the energy `𝕎(C, 1)` of a configuration `C ⊂ ℂ` with background density one: the infimum
of the neutral energy `neutralEnergy C E` over the gradient fields `E ∈ Elec(C, 1)` (S. Serfaty, *Lectures on
Coulomb and Riesz gases*, Definition 11.6 and (11.2.14), with `neutralEnergy` in place of the energy of
Definition 11.4; the two energies agree for large `C0` by `exists_jelliumEnergy_eq_neutralEnergy`).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `𝕎(C, 1) = inf {W^neu(E, 1) : E ∈ Elec(C, 1), E a gradient}`, `inf ∅ = +∞` (*Lectures*, Definition 11.6,
(11.2.14), with the neutral energy `neutralEnergy` in place of the energy of Definition 11.4). "Gradient" is
distributional: `E = ∇H` for some `H ∈ L¹_loc`, i.e. `∫ H ∇φ = -∫ φ E` for every test function `φ`. -/
@[expose] noncomputable def configEnergy (C : Set ℂ) : EReal :=
  ⨅ (E : ℂ → ℂ) (_ : E ∈ elec C)
    (_ : ∃ H : ℂ → ℝ, LocallyIntegrable H volume ∧ ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ →
      HasCompactSupport φ → (∫ x, H x • gradient φ x) = -(∫ x, φ x • E x)),
    neutralEnergy C E

end SandierSerfaty

end
