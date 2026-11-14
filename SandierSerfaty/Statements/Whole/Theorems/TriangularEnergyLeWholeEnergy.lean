/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.IsCutoffFamily
public import SandierSerfaty.Statements.Whole.Defs.WholeEnergy
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
import SandierSerfaty.Proofs.Whole.TriangularEnergyLeWholeEnergy

/-!
# Minimality of the triangular field in the whole plane

`triangularEnergy_le_wholeEnergy` is the inequality of OpenAI, *Triangular minimality for planar Coulomb
renormalized energy*, Theorem 1.1 (`thm:main`): for every cutoff family and every field `E` of the admissible
class `𝒜₁`, `W(E) ≥ W_tri`, in the extended reals (so fields of infinite energy are included). Here
`W_tri = W(E_△)` by `paperTriangularField_spec`.

The proof is `SandierSerfaty.Proofs.triangularEnergy_le_wholeEnergy`, in the module
`SandierSerfaty.Proofs.Whole.TriangularEnergyLeWholeEnergy`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **Paper Theorem 1.1** (`thm:main`), lower bound: for every cutoff
family and every `E ∈ 𝒜₁`, `W(E) ≥ W_tri`, where `W_tri = W(E_△)` by `paperTriangularField_spec`.
In `[-∞, +∞]`: the cases `W(E) = ±∞` are covered. -/
theorem triangularEnergy_le_wholeEnergy (χ : ℝ → ℂ → ℝ) (hχ : IsCutoffFamily χ)
    (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E) :
    (triangularEnergy : EReal) ≤ wholeEnergy χ Λ E :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.triangularEnergy_le_wholeEnergy χ hχ Λ E hE
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
