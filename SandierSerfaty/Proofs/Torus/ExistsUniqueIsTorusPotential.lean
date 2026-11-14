/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import SandierSerfaty.Torus.PotentialExists
public import SandierSerfaty.Torus.PotentialUnique
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Proof of `SandierSerfaty.existsUnique_isTorusPotential`

`SandierSerfaty.Proofs.existsUnique_isTorusPotential` proves the statement
`SandierSerfaty.existsUnique_isTorusPotential` of the module
`SandierSerfaty.Statements.Torus.Theorems.ExistsUniqueIsTorusPotential`. Existence is
`SandierSerfaty.Torus.exists_isTorusPotential` (an explicit theta-product Green function,
`SandierSerfaty/Torus/PotentialExists.lean`) and uniqueness is `SandierSerfaty.Torus.isTorusPotential_unique`
(`SandierSerfaty/Torus/PotentialUnique.lean`).
-/

public section

namespace SandierSerfaty

namespace Proofs

/-- Existence and uniqueness of the torus potential on a lattice torus of area `N`, for `N` charges
with pairwise distinct classes modulo `Γ`. -/
theorem existsUnique_isTorusPotential (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    ∃! h : ℂ → ℝ, IsTorusPotential Γ a h := by
  obtain ⟨h, hh⟩ := Torus.exists_isTorusPotential Γ hΓ a ha
  exact ⟨h, hh, fun h' hh' => Torus.isTorusPotential_unique Γ hΓ a ha hh' hh⟩

end Proofs

end SandierSerfaty

end
