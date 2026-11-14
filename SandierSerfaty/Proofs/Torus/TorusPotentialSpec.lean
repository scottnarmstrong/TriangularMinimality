/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Theorems.ExistsUniqueIsTorusPotential
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Proof of `SandierSerfaty.torusPotential_spec`

`SandierSerfaty.Proofs.torusPotential_spec` proves the statement `SandierSerfaty.torusPotential_spec` of the
module `SandierSerfaty.Statements.Torus.Theorems.TorusPotentialSpec`. It follows from
`SandierSerfaty.existsUnique_isTorusPotential` (existence and uniqueness) and `Classical.epsilon_spec`, since
`torusPotential Γ a` is `Classical.epsilon (IsTorusPotential Γ a)`.
-/

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.torusPotential_spec`: characterization of `torusPotential`. -/
theorem torusPotential_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IsTorusPotential Γ a (torusPotential Γ a) ∧
      ∀ h : ℂ → ℝ, IsTorusPotential Γ a h → h = torusPotential Γ a := by
  obtain ⟨h₀, hh₀, huniq⟩ := SandierSerfaty.existsUnique_isTorusPotential Γ hΓ a ha
  have hspec : IsTorusPotential Γ a (torusPotential Γ a) :=
    Classical.epsilon_spec (p := IsTorusPotential Γ a) ⟨h₀, hh₀⟩
  exact ⟨hspec, fun h hh => (huniq h hh).trans (huniq _ hspec).symm⟩

end SandierSerfaty.Proofs

end
