/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.HexTrial
public import SandierSerfaty.Calibration.AngleDensity
public import SandierSerfaty.Dual.DualIdentityMain
public import SandierSerfaty.Dual.SectorToEnergy

/-!
# The energy identity `6K + λ + 2πμ = W_△` (`cal:energy-identity`)

Apply the dual identity (`Dual.dual_identity`) to the triangular torus `ℂ/Λ_△` with one charge at `0`, the
calibration radial data (admissible at `d₀ = p`), and `d₀ = p`.

1. *Separation* (`sepSites_triSites`): distinct lattice points are `≥ a = 2p` apart (`a_le_norm_of_mem_tri`).
2. *The six sectors* (`HexSector.lean`): the incidences are among `(0, a ρ^j)`; each sector has `d = p`,
   `α = β = π/6`.
3. *The sector functional* (`sectorJ_triSites`): by `cal:sector-primitive` (`modelSectorJ_sub_eq`) and
   `p tan(π/6) = x₀`, `J(S_j) = K + λ A(S_j) + μ θ(S_j)` (`K = 2 g_p(x₀)`).
4. *The gradient term vanishes* (`gluedH_eq_hTri_sub`, `integral_gradSq_triSites`): on every sector the glued
   trial potential is `h_△ - C_△` (`HexTrial.modelH_hex` and the Green expansion; the six rotations
   leave `Re (w^{6m})` unchanged), so `∇(u - H) = 0` there; the sectors tile the torus.
5. Summing: six sectors of total area `1` and total angle `2π`.

**Answer to the "check carefully" question of the brief.** `gluedH` is *not* literally `h_△` (they differ by the
constant `C_△`, and `u = greenSum` is `h_△`), but `u - H = C_△` on every sector, so `∇(u - H) = 0` there; this is
what is proved.
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm SandierSerfaty.Torus SandierSerfaty.Dual SandierSerfaty.Analysis

/-- The single charge at `0`. -/
@[expose] def triCharge : Fin 1 → ℂ := fun _ => 0

theorem covolume_tri : ZLattice.covolume triangularLattice = ((1 : ℕ) : ℝ) := by
  simpa using Torus.covolume_triangularLattice

theorem injective_triCharge : ∀ i j : Fin 1, triCharge i - triCharge j ∈ triangularLattice → i = j :=
  fun i j _ => Subsingleton.elim i j

/-- **Separation of the triangular sites**: distinct sites are `≥ 2p = a` apart. -/
theorem sepSites_triSites : SepSites triSites p := by
  refine sepSites_periodicSites (Γ := triangularLattice) (a := triCharge) p_pos ?_
  intro x hx y hy hne
  rw [mem_periodicSites_iff] at hx hy
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  have h := triangularLattice.sub_mem hi hj
  have hxy : x - y = (x - triCharge i) - (y - triCharge j) := by simp [triCharge]
  rw [← hxy] at h
  have := a_le_norm_of_mem_tri h (sub_ne_zero.2 hne)
  rw [a_eq_two_mul_p] at this
  exact this

theorem hR_tri : radialData.IsAdmissible p := radialData_isAdmissible_p

/-- **The trial potential on a hexagon sector**: `H = h_△ - C_△` there; also the sector avoids the lattice. -/
theorem gluedH_eq_hTri_sub {q z : ℂ} (h : IsVoronoiNeighbor triSites 0 q)
    (hz : z ∈ voronoiSector triSites 0 q) :
    gluedH radialData triSites z = hTri z - CTri ∧ z ≠ 0 ∧ ‖z‖ < a := by
  obtain ⟨j, hj, rfl⟩ := exists_pow_of_isVoronoiNeighbor h
  obtain ⟨w, hw, rfl⟩ := hz
  rw [pairHalfDist_triSites, sectorAlpha_triSites, sectorBeta_triSites] at hw
  rw [pairAxis_triSites]
  obtain ⟨hX, hXp, hXn, h3⟩ := sector_facts hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hX
  have hnorm : ‖(0 : ℂ) + rho ^ j * w‖ = ‖w‖ := by
    rw [zero_add, norm_mul, norm_rho_pow, one_mul]
  have hz0 : (0 : ℂ) + rho ^ j * w ≠ 0 := by
    rw [zero_add]; exact mul_ne_zero (pow_ne_zero _ rho_ne_zero) hw0
  have hwR : ‖w‖ ≤ R₀ := by
    have hp := p_pos
    refine (sq_le_sq₀ (norm_nonneg _) R₀_pos.le).1 ?_
    rw [R₀_sq]
    nlinarith
  have hwa : ‖w‖ < a := lt_of_le_of_lt hwR R₀_lt_a
  refine ⟨?_, hz0, by rw [hnorm]; exact hwa⟩
  have hmem : (0 : ℂ) + rho ^ j * w ∈ voronoiSector triSites 0 ((a : ℂ) * rho ^ j) := by
    refine ⟨w, ?_, ?_⟩
    · rwa [pairHalfDist_triSites, sectorAlpha_triSites, sectorBeta_triSites]
    · rw [pairAxis_triSites]
  rw [gluedH_eq_Hsec sepSites_triSites h hmem]
  have hHsec : Hsec radialData 0 ((a : ℂ) * rho ^ j) (0 + rho ^ j * w) =
      modelH radialData p w := by
    have := Hsec_pairAxis_mul (R := radialData) h.ne w
    rwa [pairAxis_triSites, pairHalfDist_triSites] at this
  rw [hHsec, modelH_hex hw, green_expansion hz0 (by rw [hnorm]; exact hwa), hnorm]
  have hpow : ∀ m : ℕ, ((0 : ℂ) + rho ^ j * w) ^ (6 * (m + 1)) = w ^ (6 * (m + 1)) := by
    intro m
    rw [zero_add, mul_pow, pow_mul, rho_pow_six_mul, one_pow, one_mul]
  simp only [hpow]
  unfold gamma
  ring

/-- **The sector functional of a hexagon sector** (paper `cal:scalar-bounds`): `J(S) = K + λ A(S) + μ θ(S)`, since
`J - λ A - μ θ = g_p(p tan π/6) + g_p(p tan π/6) = 2 g_p(x₀) = K` (`cal:sector-primitive`). -/
theorem sectorJ_triSites {q : ℂ} (h : IsVoronoiNeighbor triSites 0 q) :
    sectorJ radialData triSites 0 q =
      K + lam * volume.real (voronoiSector triSites 0 q) +
        mu * (sectorAlpha triSites 0 q + sectorBeta triSites 0 q) := by
  have hP := sepSites_triSites.isVoronoiSiteSet
  rw [sectorJ_eq_modelSectorJ sepSites_triSites h, volume_real_voronoiSector hP h]
  obtain ⟨j, hj, rfl⟩ := exists_pow_of_isVoronoiNeighbor h
  rw [pairHalfDist_triSites, sectorAlpha_triSites, sectorBeta_triSites]
  have hpi := Real.pi_pos
  have hmain := modelSectorJ_sub_eq (d := p) (α := Real.pi / 6) (β := Real.pi / 6) p_pos
    (by rw [abs_of_pos (by positivity)]; linarith) (by rw [abs_of_pos (by positivity)]; linarith)
    (by positivity)
  have hx : p * Real.tan (Real.pi / 6) = x₀ := by
    rw [← x₀_div_p]; field_simp [p_pos.ne']
  rw [hx] at hmain
  unfold K
  linarith

theorem sectorJ_sum_triSites :
    ∑ e ∈ voronoiIncidences triangularLattice triCharge,
      sectorJ radialData (periodicSites triangularLattice triCharge) (triCharge e.1) e.2 =
      6 * K + lam + 2 * Real.pi * mu := by
  have hang : ∀ e ∈ voronoiIncidences triangularLattice triCharge,
      sectorAlpha triSites 0 e.2 + sectorBeta triSites 0 e.2 = Real.pi / 3 := by
    intro e he
    have hn : IsVoronoiNeighbor triSites 0 e.2 := (mem_voronoiIncidences _ _).1 he
    obtain ⟨j, hj, hq⟩ := exists_pow_of_isVoronoiNeighbor hn
    rw [hq, sectorAlpha_triSites, sectorBeta_triSites]; ring
  have hsum : ∑ e ∈ voronoiIncidences triangularLattice triCharge,
      (sectorAlpha triSites 0 e.2 + sectorBeta triSites 0 e.2) = 2 * Real.pi := by
    have h := sum_sectorAngle_voronoiIncidences triangularLattice triCharge
    rw [Nat.cast_one, mul_one] at h
    exact h
  have hvol : ∑ e ∈ voronoiIncidences triangularLattice triCharge,
      volume.real (voronoiSector triSites 0 e.2) = 1 := by
    have h := sum_volume_real_voronoiSector triangularLattice triCharge injective_triCharge
    rw [covolume_tri, Nat.cast_one] at h
    exact h
  have hcard : ((voronoiIncidences triangularLattice triCharge).card : ℝ) = 6 := by
    rw [Finset.sum_congr rfl hang, Finset.sum_const, nsmul_eq_mul] at hsum
    have := Real.pi_pos
    nlinarith
  calc ∑ e ∈ voronoiIncidences triangularLattice triCharge,
        sectorJ radialData (periodicSites triangularLattice triCharge) (triCharge e.1) e.2
      = ∑ e ∈ voronoiIncidences triangularLattice triCharge,
        (K + lam * volume.real (voronoiSector triSites 0 e.2) +
          mu * (sectorAlpha triSites 0 e.2 + sectorBeta triSites 0 e.2)) :=
        Finset.sum_congr rfl fun e he => sectorJ_triSites ((mem_voronoiIncidences _ _).1 he)
    _ = 6 * K + lam + 2 * Real.pi * mu := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hvol, hsum, Finset.sum_const, nsmul_eq_mul, hcard]
        ring

/-- On every hexagon sector `u - H = C_△`, so `∇(u - H) = 0`. -/
theorem gradSq_eq_zero_of_mem_sector {q z : ℂ} (h : IsVoronoiNeighbor triSites 0 q)
    (hz : z ∈ voronoiSector triSites 0 q) :
    gradSq (fun y => greenSum triangularLattice triCharge y -
      gluedH radialData (periodicSites triangularLattice triCharge) y) z = 0 := by
  have hev : (fun y => greenSum triangularLattice triCharge y -
      gluedH radialData (periodicSites triangularLattice triCharge) y) =ᶠ[𝓝 z] fun _ => CTri := by
    filter_upwards [(isOpen_voronoiSector h).mem_nhds hz] with y hy
    obtain ⟨hH, hy0, hya⟩ := gluedH_eq_hTri_sub h hy
    have hyl : y ∉ triangularLattice := notMem_triangularLattice_of_norm_lt hy0 hya
    have hG : greenSum triangularLattice triCharge y = hTri y := by
      rw [hTri_eq_torusGreen hyl]
      simp [greenSum, triCharge]
    rw [hG]
    show hTri y - gluedH radialData triSites y = CTri
    rw [hH]; ring
  simp only [gradSq, pd₁, pd₂, hev.fderiv_eq]
  simp

/-- **The gradient term of the dual identity vanishes** for the triangular torus. -/
theorem integral_gradSq_triSites :
    ∫ x in torusDomain triangularLattice, gradSq (fun y => greenSum triangularLattice triCharge y -
      gluedH radialData (periodicSites triangularLattice triCharge) y) x = 0 := by
  have hS : SepSites (periodicSites triangularLattice triCharge) p := sepSites_triSites
  obtain ⟨Kw, hw⟩ := exists_lipschitzWith_wExt (R := radialData) injective_triCharge hR_tri hS
  have hae : ∀ᵐ x ∂(volume.restrict (torusDomain triangularLattice)),
      x ∉ chargeSet triangularLattice triCharge :=
    ae_restrict_of_ae ((countable_chargeSet triangularLattice triCharge).ae_notMem volume)
  have hfw : (gradSq fun y => greenSum triangularLattice triCharge y -
      gluedH radialData (periodicSites triangularLattice triCharge) y) =ᵐ[volume.restrict
        (torusDomain triangularLattice)] gradSq (wExt radialData triangularLattice triCharge) := by
    filter_upwards [hae] with x hx
    simp only [gradSq, pd₁, pd₂, (eventuallyEq_wExt (R := radialData) hx).fderiv_eq]
  have hint := (integrableOn_gradSq_wExt hw).congr hfw.symm
  have hper : ∀ γ ∈ triangularLattice, ∀ x,
      (fun y => greenSum triangularLattice triCharge y -
        gluedH radialData (periodicSites triangularLattice triCharge) y) (x + γ) =
      (fun y => greenSum triangularLattice triCharge y -
        gluedH radialData (periodicSites triangularLattice triCharge) y) x := by
    intro γ hγ x
    simp only [greenSum_add_period hγ x, gluedH_periodic hS γ hγ x]
  rw [integral_torusDomain_eq_sum_sector triangularLattice triCharge injective_triCharge
    (gradSq_periodic' (Γ := triangularLattice) hper) hint]
  refine Finset.sum_eq_zero fun e he => ?_
  have hn : IsVoronoiNeighbor triSites 0 e.2 := (mem_voronoiIncidences _ _).1 he
  exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => gradSq_eq_zero_of_mem_sector hn hz

/-- **`cal:energy-identity`**: the calibrated constants satisfy
`6 K + λ + 2π μ = W_△` (the puncture energy of the triangular torus). -/
theorem energy_identity : 6 * K + lam + 2 * Real.pi * mu = triangularEnergy := by
  have h := dual_identity (R := radialData) (Γ := triangularLattice) (a := triCharge)
    covolume_tri injective_triCharge hR_tri sepSites_triSites
  rw [integral_gradSq_triSites, mul_zero, add_zero, sectorJ_sum_triSites] at h
  exact h.symm

end Calibration

end SandierSerfaty

end
