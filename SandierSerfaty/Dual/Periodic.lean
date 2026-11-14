/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.SiteLipschitz
public import SandierSerfaty.Geometry.VoronoiIncidence

/-!
# Periodic sites and the glued potential

For the `Γ`-periodic sites `periodicSites Γ a`, with `2 d₀`-separated distinct sites, the standing
hypotheses `SepSites` hold (`sepSites_periodicSites`), and the glued potential `gluedH` is
`Γ`-periodic (`gluedH_add`): translating a site and a point by `γ ∈ Γ` preserves the gauge.
-/

open Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

variable {ι : Type*} {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ} {p z : ℂ} {γ : ℂ}

theorem gaugeLin_add_add (p q w γ : ℂ) : gaugeLin (p + γ) (q + γ) w = gaugeLin p q w := by
  simp [gaugeLin]

theorem gauge_add_add (hP : ∀ q, q + γ ∈ P ↔ q ∈ P) (p w : ℂ) :
    gauge P (p + γ) w = gauge P p w := by
  unfold gauge
  let e : P ≃ P :=
    { toFun := fun q => ⟨q.1 + γ, (hP q.1).2 q.2⟩
      invFun := fun q => ⟨q.1 - γ, by rw [← hP]; simp⟩
      left_inv := fun q => by ext; simp
      right_inv := fun q => by ext; simp }
  rw [← Equiv.iSup_comp e]
  refine iSup_congr fun q => ?_
  simp [e, gaugeLin_add_add]

theorem cellH_add (hP : ∀ q, q + γ ∈ P ↔ q ∈ P) (p z : ℂ) :
    cellH R P (p + γ) (z + γ) = cellH R P p z := by
  unfold cellH
  have : z + γ - (p + γ) = z - p := by ring
  rw [this, gauge_add_add hP]

/-- **Periodicity** of the glued potential. -/
theorem gluedH_add (hS : SepSites P d₀) (hP : ∀ q, q + γ ∈ P ↔ q ∈ P) (z : ℂ) :
    gluedH R P (z + γ) = gluedH R P z := by
  obtain ⟨p, hp, hz⟩ := exists_cell hS z
  have hz' : z + γ ∈ voronoiCell P (p + γ) := by
    rw [mem_voronoiCell_add_iff hP]; simpa using hz
  rw [gluedH_eq_cellH hS ((hP p).2 hp) hz', gluedH_eq_cellH hS hp hz, cellH_add hP]

theorem sepSites_periodicSites (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {n : ℕ}
    [NeZero n] (a : Fin n → ℂ) (hd : 0 < d₀)
    (hsep : ∀ p ∈ periodicSites Γ a, ∀ q ∈ periodicSites Γ a, p ≠ q → 2 * d₀ ≤ ‖p - q‖) :
    SepSites (periodicSites Γ a) d₀ :=
  { pos := hd
    nonempty := ⟨a 0, mem_periodicSites Γ a 0⟩
    locallyFinite := locallyFiniteSites_periodicSites Γ a
    sep := hsep
    bdd := ⟨latticeRadius Γ, fun _p hp => (voronoiCell_subset_ball Γ a hp).trans ball_subset_closedBall⟩ }

end Dual

end SandierSerfaty

end
