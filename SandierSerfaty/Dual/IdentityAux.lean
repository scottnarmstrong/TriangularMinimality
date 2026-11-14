/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.WExt
public import SandierSerfaty.Dual.SectorRen
public import SandierSerfaty.Dual.SectorSum
public import SandierSerfaty.Torus.PairEnergy

/-!
# Auxiliary facts for the dual identity

* `gradSq_decomp`: if `w = u - H` near `x` and `u`, `H` are differentiable at `x`, then
  `|∇u|² = 2 ⟨∇w, ∇u⟩ - |∇w|² + |∇H|²` at `x`.
* Points of an open sector are not sites, `gluedH` is differentiable there, and `wExt = greenSum - gluedH` near them.
* On a sector of the incidence `(i, q)`, `x ∈ punctureSet η ↔ ‖x - aᵢ‖ < η`.
* Periodicity of `gluedH`, `wExt`, `gradSq`, `gradDot` for the periodic sites of a lattice.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis Torus

variable {ι : Type*} {R : RadialData ι} {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]
  {N : ℕ} {a : Fin N → ℂ} {d₀ : ℝ} {P : Set ℂ} {p q z : ℂ}

/-- **Algebra of the dual identity.** -/
theorem gradSq_decomp {u H w : ℂ → ℝ} {x : ℂ} (hu : DifferentiableAt ℝ u x)
    (hH : DifferentiableAt ℝ H x) (hw : w =ᶠ[𝓝 x] fun y => u y - H y) :
    gradSq u x = 2 * gradDot w u x - gradSq w x + gradSq H x := by
  have h : fderiv ℝ w x = fderiv ℝ u x - fderiv ℝ H x := by
    rw [hw.fderiv_eq]; exact fderiv_sub hu hH
  simp only [gradSq, gradDot, pd₁, pd₂, h, sub_apply]
  ring

theorem notMem_of_mem_voronoiSector (hS : SepSites P d₀) (h : IsVoronoiNeighbor P p q)
    (hz : z ∈ voronoiSector P p q) : z ∉ P := fun hzP => by
  have := norm_sub_lt_of_mem_voronoiSector hS.isVoronoiSiteSet h hz hzP
    (ne_of_mem_voronoiSector h hz)
  rw [sub_self, norm_zero] at this
  exact absurd this (not_lt.2 (norm_nonneg _))

theorem differentiableAt_gluedH_of_mem_sector (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) (hz : z ∈ voronoiSector P p q) :
    DifferentiableAt ℝ (gluedH R P) z := by
  obtain ⟨R₁, T₀, M, hR₁, hT, -, hM⟩ := exists_bnd hR hS
  exact (hasFDerivAt_Hsec hR hS h hR₁ hT hM hz).differentiableAt.congr_of_eventuallyEq
    (eventuallyEq_gluedH_Hsec hS h hz)

omit [IsZLattice ℝ Γ] in
theorem eventuallyEq_wExt (hz : z ∉ chargeSet Γ a) :
    wExt R Γ a =ᶠ[𝓝 z] fun y => greenSum Γ a y - gluedH R (periodicSites Γ a) y := by
  filter_upwards [(isClosed_chargeSet Γ a).isOpen_compl.mem_nhds hz] with y hy
  exact wExt_of_notMem hy

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
/-- On a sector of the incidence `(i, q)`: nearest charge, and membership in the puncture set. -/
theorem mem_punctureSet_iff_of_mem_voronoiSector {i : Fin N} {η : ℝ}
    (hS : SepSites (periodicSites Γ a) d₀)
    (h : IsVoronoiNeighbor (periodicSites Γ a) (a i) q)
    (hz : z ∈ voronoiSector (periodicSites Γ a) (a i) q) :
    z ∈ punctureSet Γ a η ↔ ‖z - a i‖ < η := by
  rw [mem_punctureSet]
  constructor
  · rintro ⟨j, γ, hγ, hlt⟩
    have hc : a j + γ ∈ periodicSites Γ a := ⟨j, γ, hγ, rfl⟩
    by_cases hce : a j + γ = a i
    · rwa [hce] at hlt
    · have := norm_sub_lt_of_mem_voronoiSector hS.isVoronoiSiteSet h hz hc hce
      exact lt_trans this hlt
  · intro hlt
    exact ⟨i, 0, Γ.zero_mem, by simpa using hlt⟩

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
/-- `periodicSites` is invariant under lattice translation. -/
theorem periodicSites_add_iff {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    x + γ ∈ periodicSites Γ a ↔ x ∈ periodicSites Γ a :=
  add_mem_periodicSites_iff Γ a hγ

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem gluedH_periodic (hS : SepSites (periodicSites Γ a) d₀) :
    ∀ γ ∈ Γ, ∀ x, gluedH R (periodicSites Γ a) (x + γ) = gluedH R (periodicSites Γ a) x :=
  fun _ hγ x => gluedH_add hS (fun y => periodicSites_add_iff hγ y) x

end Dual

end SandierSerfaty

end
