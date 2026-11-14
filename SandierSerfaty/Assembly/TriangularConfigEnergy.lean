/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Assembly.Statements
public import SandierSerfaty.Assembly.TorusGradient
public import SandierSerfaty.Statements.Jellium.Theorems.TriangularFieldSpec

/-!
# The jellium energy of the triangular lattice from the neutral-energy bound (screening note, Theorem 6.5)

`triangularConfigEnergy_of_neutralEnergyBound : NeutralEnergyBoundStatement → TriangularConfigEnergyStatement` has *exactly* the conclusion of `configEnergy_triangularLattice`
(Serfaty's Chapter 11).

Route: every term of the infimum defining `𝕎(C, 1)` is `≥ W_△/2π` by the neutral-energy bound
`div_two_pi_triangularEnergy_le_neutralEnergy` (and `inf ∅ = +∞`); for `Λ_△` the field `E_△` is admissible
(`triangularField_spec` and `triangularField_isDistGradient`, screening note, Lemma 6.4), so
`𝕎(Λ_△, 1) ≤ W^neu(E_△, 1) = W_△/2π`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Assembly

/-- The statement of `configEnergy_triangularLattice`, as a `Prop`. -/
@[expose] def TriangularConfigEnergyStatement : Prop :=
  configEnergy (triangularLattice : Set ℂ) = ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ∧
    ∀ C : Set ℂ, configEnergy (triangularLattice : Set ℂ) ≤ configEnergy C

/-- **The jellium energy of the triangular lattice from the neutral-energy bound** (screening note, Theorem 6.5;
exactly the statement of `configEnergy_triangularLattice`). -/
theorem triangularConfigEnergy_of_neutralEnergyBound : NeutralEnergyBoundStatement → TriangularConfigEnergyStatement := by
  intro hR2
  have hlower : ∀ C : Set ℂ, ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ≤ configEnergy C :=
    fun C => le_iInf fun E => le_iInf fun hE => le_iInf fun _ => hR2 C E hE
  obtain ⟨hmem, hW⟩ := triangularField_spec
  have hupper : configEnergy (triangularLattice : Set ℂ) ≤
      ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) := by
    unfold configEnergy
    refine (iInf_le _ triangularField).trans ((iInf_le _ hmem).trans
      ((iInf_le _ triangularField_isDistGradient).trans (le_of_eq hW)))
  have heq : configEnergy (triangularLattice : Set ℂ) =
      ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) :=
    le_antisymm hupper (hlower _)
  exact ⟨heq, fun C => heq ▸ hlower C⟩

end Assembly

end SandierSerfaty

end
