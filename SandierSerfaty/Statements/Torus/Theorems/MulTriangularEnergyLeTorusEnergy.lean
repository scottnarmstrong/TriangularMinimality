/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.SquareLattice
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
import SandierSerfaty.Proofs.Torus.MulTriangularEnergyLeTorusEnergy

/-!
# The lower bound on square tori

`mul_triangularEnergy_le_torusEnergy` is OpenAI, *Triangular minimality for planar Coulomb renormalized
energy*, Theorem 1.2 (`thm:torus`): for every integer `n ≥ 2` and every `n` points of the square torus
`T_n = ℂ/(√n ℤ[i])` with pairwise distinct classes, the energy of their torus potential is at least `n W_tri`.
The paper states the bound with `W(E_△)`, which equals `W_tri` by `paperTriangularField_spec`.

The proof is `SandierSerfaty.Proofs.mul_triangularEnergy_le_torusEnergy`, in the module
`SandierSerfaty.Proofs.Torus.MulTriangularEnergyLeTorusEnergy`.
-/

@[expose] public section

namespace SandierSerfaty

/-- **Paper Theorem 1.2** (`thm:torus`). For every integer
`n ≥ 2` and every `n` points of `T_n = ℂ/(√n ℤ[i])` with pairwise distinct classes, the
puncture-first energy of their mean-zero torus potential is at least `n · W_tri`. -/
theorem mul_triangularEnergy_le_torusEnergy (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.mul_triangularEnergy_le_torusEnergy n hn a ha
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
