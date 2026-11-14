/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.IsCutoffFamily
public import SandierSerfaty.Statements.Whole.Defs.PaperTriangularField
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
import SandierSerfaty.Proofs.Whole.PaperTriangularFieldSpec

/-!
# The triangular field is admissible, with energy `W_tri`

`paperTriangularField_spec`: the triangular field `E_△` lies in the admissible class `𝒜₁`, and for every
cutoff family its energy is `W(E_△) = W_tri`. With `triangularEnergy_le_wholeEnergy` this gives OpenAI,
*Triangular minimality for planar Coulomb renormalized energy*, Theorem 1.1: the triangular value is finite
and `inf_{𝒜₁} W = W(E_△)`, attained at `E_△`.

The proof is `SandierSerfaty.Proofs.paperTriangularField_spec`, in the module
`SandierSerfaty.Proofs.Whole.PaperTriangularFieldSpec`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **The triangular value** (paper Theorem 1.1, second and third sentences, and Lemma `red:periodic-average`):
`E_△ ∈ 𝒜₁` (so the infimum is attained) and, for every cutoff family, `W(E_△) = W_tri` (finite, and
independent of the family). -/
theorem paperTriangularField_spec :
    IsAdmissibleField (triangularLattice : Set ℂ) paperTriangularField ∧
      ∀ χ : ℝ → ℂ → ℝ, IsCutoffFamily χ →
        wholeEnergy χ (triangularLattice : Set ℂ) paperTriangularField = (triangularEnergy : EReal) :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.paperTriangularField_spec
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
