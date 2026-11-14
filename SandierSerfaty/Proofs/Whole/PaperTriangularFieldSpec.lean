/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.TriangularAverage
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.IsCutoffFamily
public import SandierSerfaty.Statements.Whole.Defs.PaperTriangularField
public import SandierSerfaty.Statements.Whole.Defs.WholeEnergy

/-!
# Proof of `SandierSerfaty.paperTriangularField_spec`

`SandierSerfaty.Proofs.paperTriangularField_spec` proves the statement
`SandierSerfaty.paperTriangularField_spec` of the module
`SandierSerfaty.Statements.Whole.Theorems.PaperTriangularFieldSpec`.

* `E_△ ∈ 𝒜₁`: `Whole.isAdmissibleField_paperTriangularField` (`E_△ = -∇h_△`: divergence from the torus
  potential, `Jellium/TorusElec.lean`; curl from the symmetry of second derivatives,
  `Whole/TorusCurl.lean`; growth bound from lattice counting).
* `W(E_△) = W_tri` for every cutoff family: `Whole.wholeEnergy_paperTriangularField` (comparison note,
  Lemmas `lem:periodic`, `lem:tri`; paper Lemma `red:periodic-average`), `Whole/TriangularAverage.lean`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.paperTriangularField_spec`. -/
theorem paperTriangularField_spec :
    IsAdmissibleField (triangularLattice : Set ℂ) paperTriangularField ∧
      ∀ χ : ℝ → ℂ → ℝ, IsCutoffFamily χ →
        wholeEnergy χ (triangularLattice : Set ℂ) paperTriangularField = (triangularEnergy : EReal) :=
  ⟨Whole.isAdmissibleField_paperTriangularField, fun _ hχ => Whole.wholeEnergy_paperTriangularField hχ⟩

end SandierSerfaty.Proofs

end
