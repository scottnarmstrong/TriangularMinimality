/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.Comparison
public import SandierSerfaty.Assembly.JelliumBounds
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy

/-!
# The lower bound of paper Theorem 1.1 from the neutral-energy bound, and from the square-torus bound

`wholeEnergyBound_of_neutralEnergyBound`: the neutral-energy bound (`NeutralEnergyBoundStatement`, the statement of
`div_two_pi_triangularEnergy_le_neutralEnergy`) implies the exact statement of the lower bound
`triangularEnergy_le_wholeEnergy` (paper Theorem 1.1): for every cutoff family and every `E ∈ 𝒜₁`,
`W_tri ≤ W(E)` in `[-∞, +∞]`.

Route (comparison note, Theorem `thm:main-deduced`): `-E ∈ Elec(Λ, 1)` (`Whole.neg_mem_elec`), so the
neutral-energy bound gives `W_tri / (2π) ≤ W^neu(-E, 1)`, and the comparison inequality
(`Whole.twoPi_mul_neutralEnergy_neg_le_wholeEnergy`) gives `2π W^neu(-E, 1) ≤ W(E)`.

`wholeEnergyBound_of_torusBound`: the same from the square-torus bound (paper Theorem 1.2), through `neutralEnergyBound_of_torusBound` (the screening theorem
I4).
-/

open MeasureTheory Filter Topology

public section

namespace SandierSerfaty.Assembly

/-- **Paper Theorem 1.1 (lower bound) from the neutral-energy bound** (comparison note, Theorem `thm:main-deduced`). -/
theorem wholeEnergyBound_of_neutralEnergyBound (h : NeutralEnergyBoundStatement) :
    ∀ (χ : ℝ → ℂ → ℝ), IsCutoffFamily χ → ∀ (Λ : Set ℂ) (E : ℂ → ℂ), IsAdmissibleField Λ E →
      (triangularEnergy : EReal) ≤ wholeEnergy χ Λ E := by
  intro χ hχ Λ E hE
  have h2 := h Λ (fun x => -E x) (Whole.neg_mem_elec hE)
  have hcmp := Whole.twoPi_mul_neutralEnergy_neg_le_wholeEnergy hχ hE
  refine le_trans ?_ hcmp
  calc (triangularEnergy : EReal)
      = ((2 * Real.pi : ℝ) : EReal) * ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) := by
        rw [← EReal.coe_mul]
        congr 1
        field_simp
    _ ≤ ((2 * Real.pi : ℝ) : EReal) * neutralEnergy Λ (fun x => -E x) := by
        gcongr

/-- **Paper Theorem 1.1 (lower bound) from the square-torus bound**, through `neutralEnergyBound_of_torusBound`. -/
theorem wholeEnergyBound_of_torusBound (h : TorusBoundStatement) :
    ∀ (χ : ℝ → ℂ → ℝ), IsCutoffFamily χ → ∀ (Λ : Set ℂ) (E : ℂ → ℂ), IsAdmissibleField Λ E →
      (triangularEnergy : EReal) ≤ wholeEnergy χ Λ E :=
  wholeEnergyBound_of_neutralEnergyBound (neutralEnergyBound_of_torusBound h)

end SandierSerfaty.Assembly

end
