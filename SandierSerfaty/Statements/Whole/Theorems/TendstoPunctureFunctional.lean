/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.PunctureFunctional
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
import SandierSerfaty.Proofs.Whole.TendstoPunctureFunctional

/-!
# The local puncture limit

`tendsto_punctureFunctional`: for an admissible field and every smooth compactly supported real weight `ξ`, of
any sign, the puncture functional converges in `EReal` to a real number as `η ↓ 0` (OpenAI, *Triangular
minimality for planar Coulomb renormalized energy*, Lemma `red:local`, and the remark after `eq:whole-energy`
that the local puncture limit exists and is finite). So the `limsup` in `localEnergy` is a limit.

The proof is `SandierSerfaty.Proofs.tendsto_punctureFunctional`, in the module
`SandierSerfaty.Proofs.Whole.TendstoPunctureFunctional`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- The paper's remark "the local puncture limit exists and is finite" (after `eq:whole-energy`;
Lemma `red:local`): for admissible `(Λ, E)` and every real `ξ ∈ C_c^∞`, of any sign, the truncated
functionals converge in `EReal` to a real number as `η ↓ 0`. (So the `limsup` in `localEnergy` is a limit.) -/
theorem tendsto_punctureFunctional (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E)
    (ξ : ℂ → ℝ) (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    ∃ w : ℝ, Tendsto (punctureFunctional Λ E ξ) (𝓝[>] 0) (𝓝 (w : EReal)) :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.tendsto_punctureFunctional Λ E hE ξ hξ hc
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
