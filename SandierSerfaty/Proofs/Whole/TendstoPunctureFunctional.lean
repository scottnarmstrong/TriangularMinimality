/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.PunctureLimit
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.PunctureFunctional

/-!
# Proof of `SandierSerfaty.tendsto_punctureFunctional`

`SandierSerfaty.Proofs.tendsto_punctureFunctional` proves the statement
`SandierSerfaty.tendsto_punctureFunctional` of the module
`SandierSerfaty.Statements.Whole.Theorems.TendstoPunctureFunctional`.

The proof is `SandierSerfaty.Whole.exists_tendsto_punctureFunctional` (comparison note, Lemma
`lem:punct-limit`): the regularity of admissible fields (`Whole.IsAdmissibleField.exists_local_form`, by
Weyl's lemma) and dominated convergence.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.tendsto_punctureFunctional`. -/
theorem tendsto_punctureFunctional (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E)
    (ξ : ℂ → ℝ) (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    ∃ w : ℝ, Tendsto (punctureFunctional Λ E ξ) (𝓝[>] 0) (𝓝 (w : EReal)) :=
  Whole.exists_tendsto_punctureFunctional hE hξ hc

end SandierSerfaty.Proofs

end
