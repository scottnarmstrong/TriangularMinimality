/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import SandierSerfaty.Torus.Lattice

/-!
# Proof of `SandierSerfaty.torusDomain_spec`

`SandierSerfaty.Proofs.torusDomain_spec` proves the statement `SandierSerfaty.torusDomain_spec` of the module
`SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec`. The domain is chosen by `Classical.epsilon` among
the fundamental domains, which exist (`ZLattice.isAddFundamentalDomain`), and the integrals of a periodic
function over two fundamental domains agree (`MeasureTheory.IsAddFundamentalDomain.setIntegral_eq`).
-/

open MeasureTheory

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.torusDomain_spec`. -/
theorem torusDomain_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    IsAddFundamentalDomain Γ (torusDomain Γ) volume ∧
      ∀ (F : Set ℂ), IsAddFundamentalDomain Γ F volume → ∀ f : ℂ → ℝ,
        (∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) → ∫ x in torusDomain Γ, f x = ∫ x in F, f x := by
  have hex : IsAddFundamentalDomain Γ (torusDomain Γ) volume :=
    Classical.epsilon_spec
      (p := fun F : Set ℂ => IsAddFundamentalDomain Γ F volume)
      ⟨_, ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ Γ) volume⟩
  refine ⟨hex, fun F hF f hf => ?_⟩
  exact hex.setIntegral_eq hF (fun γ x => by show f ((γ : ℂ) + x) = f x; rw [add_comm]; exact hf γ γ.2 x)

end SandierSerfaty.Proofs

end
