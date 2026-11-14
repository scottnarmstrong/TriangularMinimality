/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice

/-!
# The energy of the triangular lattice

`triangularEnergy` is `W_tri`, the energy `torusEnergy` of the one-point triangular torus `ℂ/Λ_△` with its
charge at `0` (OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, Lemma
`cal:energy-identity`). It equals the energy `W(E_△)` of the triangular field of Theorem 1.1
(`paperTriangularField_spec`).
-/

public section

namespace SandierSerfaty

/-- `W_tri`: the puncture energy of the one-point triangular torus `ℂ/Λ_△`, charge at `0`
(paper Lemma `cal:energy-identity`; equal to the field energy `W(E_△)` of Theorem 1.1
by Lemma `red:periodic-average`, which is `paperTriangularField_spec`). -/
@[expose] noncomputable def triangularEnergy : ℝ :=
  torusEnergy triangularLattice (fun _ : Fin 1 ↦ 0)

end SandierSerfaty

end
