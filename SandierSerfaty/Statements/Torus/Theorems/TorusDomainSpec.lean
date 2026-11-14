/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import Mathlib.Algebra.Module.ZLattice.Covolume
import SandierSerfaty.Proofs.Torus.TorusDomainSpec

/-!
# The fundamental domain of a lattice

`torusDomain_spec`: for a lattice `Γ`, `torusDomain Γ` is a fundamental domain, and the integral of a
`Γ`-periodic function over it equals its integral over any other fundamental domain.

The proof is `SandierSerfaty.Proofs.torusDomain_spec`, in the module
`SandierSerfaty.Proofs.Torus.TorusDomainSpec`.
-/

open MeasureTheory

@[expose] public section

namespace SandierSerfaty

/-- For a lattice, `torusDomain Γ` is a fundamental domain, and integrals of `Γ`-periodic functions
over it agree with integrals over any other fundamental domain. -/
theorem torusDomain_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    IsAddFundamentalDomain Γ (torusDomain Γ) volume ∧
      ∀ (F : Set ℂ), IsAddFundamentalDomain Γ F volume → ∀ f : ℂ → ℝ,
        (∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) → ∫ x in torusDomain Γ, f x = ∫ x in F, f x :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.torusDomain_spec Γ
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
