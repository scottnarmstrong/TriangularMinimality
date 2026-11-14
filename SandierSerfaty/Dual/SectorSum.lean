/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiIncidence
public import SandierSerfaty.Geometry.VoronoiSectorCover
public import SandierSerfaty.Geometry.VoronoiSectorTotals
public import SandierSerfaty.Analysis.PeriodicIntegral

/-!
# Integrals over the torus as sums over the sectors

For a `Γ`-periodic integrable `F`, `∫_{torusDomain Γ} F = ∑_{(i,q) ∈ voronoiIncidences} ∫_{S(a i, q)} F`
(`integral_torusDomain_eq_sum_sector`): the representative Voronoi cells form an a.e. fundamental
domain, and the sectors of a cell are disjoint and cover it up to a null set.
This is "the punctured sectors partition `Ω_η` up to their boundaries" of the paper
(paper proof of `dual:identity`).
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty

section Sum

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {n : ℕ} [NeZero n]
  (a : Fin n → ℂ)

/-- The integral over a cell is the sum of the integrals over its sectors. -/
theorem setIntegral_voronoiCell_eq_sum_sector {P : Set ℂ} (hP : IsVoronoiSiteSet P) {p : ℂ}
    (hp : p ∈ P) {F : ℂ → ℝ} (hF : IntegrableOn F (voronoiCell P p)) :
    ∫ x in voronoiCell P p, F x =
      ∑ q ∈ (finite_isVoronoiNeighbor hP hp).toFinset, ∫ x in voronoiSector P p q, F x := by
  set Q := (finite_isVoronoiNeighbor hP hp).toFinset with hQdef
  have hQ : ∀ q, q ∈ Q ↔ IsVoronoiNeighbor P p q := fun q => Set.Finite.mem_toFinset _
  have hU : (⋃ q ∈ Q, voronoiSector P p q) =
      ⋃ q ∈ {q | IsVoronoiNeighbor P p q}, voronoiSector P p q := by
    ext z; simp only [mem_iUnion, hQ, mem_ofPred_eq]
  have hsub : (⋃ q ∈ Q, voronoiSector P p q) ⊆ voronoiCell P p :=
    iUnion₂_subset fun q hq => voronoiSector_subset_voronoiCell hP ((hQ q).1 hq)
  have hae : (⋃ q ∈ Q, voronoiSector P p q) =ᵐ[volume] voronoiCell P p := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 hsub]; exact measure_empty
    · rw [hU]; exact volume_voronoiCell_diff_iUnion_voronoiSector hP hp
  rw [← setIntegral_congr_set hae]
  refine integral_biUnion_finset Q (fun q hq => measurableSet_voronoiSector ((hQ q).1 hq))
    (fun q hq q' hq' hqq' => disjoint_voronoiSector hP ((hQ q).1 hq) ((hQ q').1 hq') (by simpa using hqq'))
    (fun q hq => hF.mono_set (voronoiSector_subset_voronoiCell hP ((hQ q).1 hq)))

/-- **The integral of a periodic function over the torus is the sum over the sectors.** -/
theorem integral_torusDomain_eq_sum_sector (ha : ∀ i j, a i - a j ∈ Γ → i = j) {F : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x)
    (hint : IntegrableOn F (torusDomain Γ)) :
    ∫ x in torusDomain Γ, F x = ∑ e ∈ voronoiIncidences Γ a,
      ∫ x in voronoiSector (periodicSites Γ a) (a e.1) e.2, F x := by
  have hFD := isAddFundamentalDomain_voronoiRepresentatives Γ a ha
  have hP := isVoronoiSiteSet_periodicSites Γ a
  have h1 : ∫ x in torusDomain Γ, F x = ∫ x in voronoiRepresentatives Γ a, F x :=
    (torusDomain_spec Γ).2 _ hFD F hper
  have hper' : ∀ (g : Γ) (x : ℂ), F (g +ᵥ x) = F x := fun g x => by
    have : g +ᵥ x = (g : ℂ) + x := rfl
    rw [this, add_comm]; exact hper g g.2 x
  have hint' : IntegrableOn F (voronoiRepresentatives Γ a) :=
    ((torusDomain_spec Γ).1.integrableOn_iff hFD hper').1 hint
  have hcell : ∀ i, IntegrableOn F (voronoiCell (periodicSites Γ a) (a i)) := fun i =>
    hint'.mono_set (subset_iUnion (fun i => voronoiCell (periodicSites Γ a) (a i)) i)
  have h2 : ∫ x in voronoiRepresentatives Γ a, F x =
      ∑ i, ∫ x in voronoiCell (periodicSites Γ a) (a i), F x := by
    rw [voronoiRepresentatives, integral_iUnion_ae, tsum_fintype]
    · exact fun i => (measurableSet_voronoiCell _ _).nullMeasurableSet
    · intro i j hij
      refine aedisjoint_voronoiCell (mem_periodicSites Γ a i) (mem_periodicSites Γ a j) fun h => hij ?_
      exact ha i j (by simp [h])
    · exact hint'
  rw [h1, h2, sum_voronoiIncidences_eq Γ a (fun p q => ∫ x in voronoiSector (periodicSites Γ a) p q, F x)]
  exact Finset.sum_congr rfl fun i _ =>
    setIntegral_voronoiCell_eq_sum_sector hP (mem_periodicSites Γ a i) (hcell i)

end Sum

end SandierSerfaty

end
