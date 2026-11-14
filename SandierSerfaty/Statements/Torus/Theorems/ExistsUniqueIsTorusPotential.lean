/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import Mathlib.Algebra.Module.ZLattice.Covolume
import SandierSerfaty.Proofs.Torus.ExistsUniqueIsTorusPotential

/-!
# Existence and uniqueness of torus potentials

`existsUnique_isTorusPotential`: on a lattice torus of area `N`, every `N` charges with pairwise distinct
classes modulo the lattice have exactly one torus potential (`IsTorusPotential`).

The proof is `SandierSerfaty.Proofs.existsUnique_isTorusPotential`, in the module
`SandierSerfaty.Proofs.Torus.ExistsUniqueIsTorusPotential`.
-/

@[expose] public section

namespace SandierSerfaty

/-- Existence and uniqueness of the torus potential on a lattice torus of area `N`, for `N` charges
with pairwise distinct classes modulo `Γ`. -/
theorem existsUnique_isTorusPotential (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    ∃! h : ℂ → ℝ, IsTorusPotential Γ a h :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.existsUnique_isTorusPotential Γ hΓ a ha
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
