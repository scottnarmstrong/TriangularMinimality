/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# A fundamental domain of a lattice

`torusDomain Γ` is a fundamental domain of the lattice `Γ` acting on `ℂ` by translation (an arbitrary choice);
`torusDomain_spec` states its properties.
-/

open MeasureTheory

public section

namespace SandierSerfaty

/-- A fundamental domain of `Γ` acting on `ℂ` by translation, for Lebesgue measure (an arbitrary
choice; see `torusDomain_spec`). -/
@[expose] noncomputable def torusDomain (Γ : Submodule ℤ ℂ) : Set ℂ :=
  Classical.epsilon fun F : Set ℂ => IsAddFundamentalDomain Γ F volume

end SandierSerfaty

end
