/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import Mathlib.Algebra.Module.ZLattice.Covolume
import SandierSerfaty.Proofs.Torus.TorusPotentialSpec

/-!
# The torus potential is the torus potential

`torusPotential_spec`: `torusPotential Γ a` is a torus potential of the charges `a`, and every torus potential
of `a` equals it.

The proof is `SandierSerfaty.Proofs.torusPotential_spec`, in the module
`SandierSerfaty.Proofs.Torus.TorusPotentialSpec`.
-/

@[expose] public section

namespace SandierSerfaty

/-- Characterization of `torusPotential`: it is a torus potential, and every torus potential equals it. -/
theorem torusPotential_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IsTorusPotential Γ a (torusPotential Γ a) ∧
      ∀ h : ℂ → ℝ, IsTorusPotential Γ a h → h = torusPotential Γ a :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.torusPotential_spec Γ hΓ a ha
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
