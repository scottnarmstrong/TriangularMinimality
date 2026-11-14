/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The square lattice

`squareLattice n` is the lattice `√n ℤ[i] ⊂ ℂ`, so that `ℂ / squareLattice n` is the square torus
`T_n = ℝ²/(√n ℤ²)` of area `n` of OpenAI, *Triangular minimality for planar Coulomb renormalized energy*,
Theorem 1.2.
-/

public section

namespace SandierSerfaty

/-- The square lattice `√n ℤ²` of `T_n = ℝ²/(√n ℤ²)`, as `√n ℤ[i] ⊂ ℂ`
(paper Theorem 1.2). -/
@[expose] noncomputable def squareLattice (n : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {(⟨√n, 0⟩ : ℂ), ⟨0, √n⟩}

end SandierSerfaty

end
