/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Torus.PairEnergy
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Proof of `SandierSerfaty.tendsto_torusEnergy`

`SandierSerfaty.Proofs.tendsto_torusEnergy` proves the statement `SandierSerfaty.tendsto_torusEnergy` of the
module `SandierSerfaty.Statements.Torus.Theorems.TendstoTorusEnergy`. It combines the puncture limit
`SandierSerfaty.Torus.tendsto_pairEnergy` (paper Lemma `geo:existence`, `geo:pair-energy`;
`SandierSerfaty/Torus/PairEnergy.lean`) with `SandierSerfaty.torusEnergy_eq_pairEnergy`, which identifies the
value of `limUnder`.
-/

open MeasureTheory Filter Topology

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.tendsto_torusEnergy`: the puncture limit exists and is finite. -/
theorem tendsto_torusEnergy (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    Tendsto (fun η : ℝ ↦
        (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
          ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η)
      (𝓝[>] 0) (𝓝 (torusEnergy Γ a)) := by
  rw [torusEnergy_eq_pairEnergy hΓ a ha]
  exact Torus.tendsto_pairEnergy hΓ ha

end SandierSerfaty.Proofs

end
