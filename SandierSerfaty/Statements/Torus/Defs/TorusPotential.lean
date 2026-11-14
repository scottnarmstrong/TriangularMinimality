/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential

/-!
# The torus potential

`torusPotential Γ a` is the torus potential of the charges `a` on `ℂ/Γ` (`IsTorusPotential`), chosen by unique
choice; `torusPotential_spec` characterizes it.
-/

public section

namespace SandierSerfaty

/-- The torus potential of the charges `a` on `ℂ/Γ`, by unique choice. -/
@[expose] noncomputable def torusPotential (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) : ℂ → ℝ :=
  Classical.epsilon (IsTorusPotential Γ a)

end SandierSerfaty

end
