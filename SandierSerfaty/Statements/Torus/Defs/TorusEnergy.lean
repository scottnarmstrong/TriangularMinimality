/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The energy of points on a torus

`torusEnergy Γ a` is the energy `𝒲_Γ(a) = lim_{η↓0} [½ ∫_{T∖⋃ᵢ B(a i, η)} |∇h|² + πN log η]` of the torus
potential `h` of the charges `a`, the balls removed periodically (OpenAI, *Triangular minimality for planar
Coulomb renormalized energy*, `eq:torus-energy` and `dual:torus-energy`). The limit exists by
`tendsto_torusEnergy`.
-/

open MeasureTheory Filter Topology

public section

namespace SandierSerfaty

/-- The puncture-first energy `𝒲_Γ(a) = lim_{η↓0} [½ ∫_{T∖⋃ᵢ B(a i, η)} |∇h|² + πN log η]` of the
torus potential, the balls removed periodically (paper `eq:torus-energy`;
`dual:torus-energy`). The limit exists by `tendsto_torusEnergy`. -/
@[expose] noncomputable def torusEnergy (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) : ℝ :=
  limUnder (𝓝[>] 0) fun η : ℝ ↦
    (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
      ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η

end SandierSerfaty

end
