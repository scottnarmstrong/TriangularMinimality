/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The triangular lattice

`triangularLattice` is the triangular lattice of covolume one, `Λ_△ = √(2/√3) (ℤ(1,0) + ℤ(1/2, √3/2))`
(OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, `eq:triangular-lattice`).
-/

public section

namespace SandierSerfaty

/-- The triangular lattice of covolume one, `Λ_△ = √(2/√3) (ℤ(1,0) + ℤ(1/2, √3/2))`
(paper `eq:triangular-lattice`). -/
@[expose] noncomputable def triangularLattice : Submodule ℤ ℂ :=
  Submodule.span ℤ {(√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ), (√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)}

end SandierSerfaty

end
