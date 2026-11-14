/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.ModelSector
public import SandierSerfaty.Dual.Separated

/-!
# From sector bounds to energy bounds (paper Proposition `dual:assembly`)

**Sector input** `(dual:sector-input)`: `SectorBound R d₀ K lam mu` says that for every `d ≥ d₀` and all
`|α|, |β| < π/2` with `α + β > 0`,
`K + lam · A(S(d, α, β)) + mu · (α + β) ≤ J(S(d, α, β))`, with `A = d² (tan α + tan β) / 2` (`sectorArea`) and
`J = modelSectorJ R d α β` (the paper's functional on the model sector, `Dual.ModelSector`).

* `sectorBound_torusEnergy` (**compatible tori**, `(dual:compatible-bound)`): for a lattice `Γ` of covolume `N`,
  `N` sites distinct mod `Γ` whose periodic site set is `2 d₀`-separated (`SepSites`), radial data admissible for
  `d₀`, `K ≤ 0` and the sector bound: `N (6K + lam + 2π mu) ≤ torusEnergy Γ a`. The proof sums
  `sectorJ ≥ K + lam · area + mu · angle` over `voronoiIncidences` (at most `6N` of them; total area `N`; total
  angle `2πN`), using `sum_sectorJ_le_torusEnergy`.
* `sectorBound_squareLattice` (**all square-torus configurations**, `(dual:all-configurations)`): `n ≥ 2`,
  `d₀ ≤ d_* = 1/(2√π)`: `n (6K + lam + 2π mu) ≤ torusEnergy (squareLattice n) a` for *every* configuration with
  distinct classes, by passing to a separated minimizer (`exists_isSeparatedConfig_isMin`).
* `mul_triangularEnergy_le_torusEnergy_of_sectorBound` (**corollary for the square-torus bound**): if moreover the
  calibration identity `6K + lam + 2π mu = triangularEnergy` holds, then
  `n · W_tri ≤ torusEnergy (squareLattice n) a`.

The last clause of the paper's proposition (fields `E` with `div E = 2π(∑ δ - 1)`, `curl E = 0`, and the energy
identity `E_T(E) = W_n(h) + (n/2)|c|²`) is the harmonic-component identity `(red:harmonic)` of §2; the
repository has no definition of the field energy `E_{T_n}`, so that clause is not part of this module.
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty

namespace Dual

open Torus

variable {ι : Type*}

/-- The area `A(S(d, α, β)) = d² (tan α + tan β) / 2` of the model sector. -/
@[expose] noncomputable def sectorArea (d α β : ℝ) : ℝ := d ^ 2 * (Real.tan α + Real.tan β) / 2

/-- **The sector input `(dual:sector-input)`**: `J(S(d, α, β)) ≥ K + lam · A(S) + mu · θ(S)` for every
`d ≥ d₀`, `|α|, |β| < π/2`, `α + β > 0`. -/
@[expose] def SectorBound (R : RadialData ι) (d₀ K lam mu : ℝ) : Prop :=
  ∀ d : ℝ, d₀ ≤ d → ∀ α β : ℝ, |α| < π / 2 → |β| < π / 2 → 0 < α + β →
    K + lam * sectorArea d α β + mu * (α + β) ≤ modelSectorJ R d α β

theorem SepSites.mono {P : Set ℂ} {d₀ d₁ : ℝ} (h : SepSites P d₁) (hd₀ : 0 < d₀) (hle : d₀ ≤ d₁) :
    SepSites P d₀ :=
  ⟨hd₀, h.nonempty, h.locallyFinite, fun p hp q hq hne => by linarith [h.sep p hp q hq hne], h.bdd⟩

/-- The area of the Voronoi sector of an incidence is `A(S(d, α, β))`. -/
theorem volume_real_voronoiSector {P : Set ℂ} {p q : ℂ} (hP : IsVoronoiSiteSet P)
    (h : IsVoronoiNeighbor P p q) :
    volume.real (voronoiSector P p q) =
      sectorArea (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) := by
  have hu := norm_pairAxis h.ne
  have hd := pairHalfDist_pos h.ne
  have h1 : volume.real (voronoiSector P p q) =
      volume.real (modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q)) := by
    have := integral_comp_affine_image hu p
      (modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q)) (fun _ => (1 : ℝ))
    simpa [voronoiSector, setIntegral_const] using this
  rw [h1, measureReal_def, volume_modelSector hd.le, ENNReal.toReal_ofReal]
  · rfl
  · have := tan_sectorAlpha_add_tan_sectorBeta_pos hP h
    positivity

/-- **Compatible tori** (`(dual:compatible-bound)`). -/
theorem sectorBound_torusEnergy {R : RadialData ι} {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {N : ℕ} [NeZero N] {a : Fin N → ℂ} {d₀ K lam mu : ℝ}
    (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    (hR : R.IsAdmissible d₀) (hS : SepSites (periodicSites Γ a) d₀) (hK : K ≤ 0)
    (hsec : SectorBound R d₀ K lam mu) :
    (N : ℝ) * (6 * K + lam + 2 * Real.pi * mu) ≤ torusEnergy Γ a := by
  refine le_trans ?_ (sum_sectorJ_le_torusEnergy hΓ ha hR hS)
  have hP := hS.isVoronoiSiteSet
  have hterm : ∀ e ∈ voronoiIncidences Γ a,
      K + lam * volume.real (voronoiSector (periodicSites Γ a) (a e.1) e.2) +
        mu * (sectorAlpha (periodicSites Γ a) (a e.1) e.2 +
          sectorBeta (periodicSites Γ a) (a e.1) e.2) ≤
      sectorJ R (periodicSites Γ a) (a e.1) e.2 := by
    intro e he
    have hn := (mem_voronoiIncidences Γ a).1 he
    rw [sectorJ_eq_modelSectorJ hS hn, volume_real_voronoiSector hP hn]
    exact hsec _ (pairHalfDist_ge hS hn) _ _ (abs_sectorAlpha_lt _ _ _) (abs_sectorBeta_lt _ _ _)
      (sectorAlpha_add_sectorBeta_pos hP hn)
  refine le_trans ?_ (Finset.sum_le_sum hterm)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, sum_volume_real_voronoiSector Γ a ha, hΓ,
    sum_sectorAngle_voronoiIncidences Γ a, nsmul_eq_mul]
  have hcard : ((voronoiIncidences Γ a).card : ℝ) ≤ 6 * N := by
    exact_mod_cast card_voronoiIncidences_le Γ a ha
  nlinarith

/-- **All square-torus configurations** (`(dual:all-configurations)`): `n ≥ 2`, `d₀ ≤ d_* = 1/(2√π)`. -/
theorem sectorBound_squareLattice {R : RadialData ι} {d₀ K lam mu : ℝ} (hd₀ : 0 < d₀)
    (hdle : d₀ ≤ dStar) (hR : R.IsAdmissible d₀) (hK : K ≤ 0) (hsec : SectorBound R d₀ K lam mu)
    (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ) (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    (n : ℝ) * (6 * K + lam + 2 * Real.pi * mu) ≤ torusEnergy (squareLattice n) a := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨b, hb, hmin⟩ := exists_isSeparatedConfig_isMin n hn
  refine le_trans ?_ (hmin a ha)
  exact sectorBound_torusEnergy (covolume_squareLattice n) hb.1 hR
    ((sepSites_of_isSeparatedConfig n b hb).mono hd₀ hdle) hK hsec

/-- **Corollary for the square-torus bound** (paper Theorem 1.2). With the calibration identity `6K + lam + 2π mu = W_tri`, the sector
bound gives `n · W_tri ≤ 𝒲_n` on every square torus with `n ≥ 2` points. -/
theorem mul_triangularEnergy_le_torusEnergy_of_sectorBound {R : RadialData ι} {d₀ K lam mu : ℝ}
    (hd₀ : 0 < d₀) (hdle : d₀ ≤ dStar) (hR : R.IsAdmissible d₀) (hK : K ≤ 0)
    (hsec : SectorBound R d₀ K lam mu) (hcal : 6 * K + lam + 2 * Real.pi * mu = triangularEnergy)
    (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ) (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    (n : ℝ) * triangularEnergy ≤ torusEnergy (squareLattice n) a := by
  rw [← hcal]
  exact sectorBound_squareLattice hd₀ hdle hR hK hsec n hn a ha

end Dual

end SandierSerfaty

end
