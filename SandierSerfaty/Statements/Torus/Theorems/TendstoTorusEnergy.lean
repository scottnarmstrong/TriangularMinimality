/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import Mathlib.Algebra.Module.ZLattice.Covolume
import SandierSerfaty.Proofs.Torus.TendstoTorusEnergy

/-!
# The puncture limit on a torus

`tendsto_torusEnergy`: the limit that defines `torusEnergy` exists and is finite (OpenAI, *Triangular
minimality for planar Coulomb renormalized energy*, the remark after `dual:torus-energy`).

The proof is `SandierSerfaty.Proofs.tendsto_torusEnergy`, in the module
`SandierSerfaty.Proofs.Torus.TendstoTorusEnergy`.
-/

open MeasureTheory Filter Topology

@[expose] public section

namespace SandierSerfaty

/-- The puncture limit exists and is finite (paper, the remark after `dual:torus-energy`). -/
theorem tendsto_torusEnergy (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    Tendsto (fun η : ℝ ↦
        (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
          ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η)
      (𝓝[>] 0) (𝓝 (torusEnergy Γ a)) :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.tendsto_torusEnergy Γ hΓ a ha
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
