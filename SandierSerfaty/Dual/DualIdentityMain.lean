/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.DualIdentity
public import SandierSerfaty.Geometry.VoronoiSectorTotals

/-!
# The dual identity on the punctured torus (paper `dual:identity`)

**Setting.** `Γ` a lattice of covolume `N` (`hΓ`), `a : Fin N → ℂ` with distinct classes (`ha`), `P = periodicSites Γ a`
with `SepSites P d₀` (`hS`: `d₀ > 0`, distinct sites `2d₀`-apart, locally finite, bounded cells), radial data
`R : RadialData ι` with `R.IsAdmissible d₀` (`hR`: `kᵢ ≥ 6`, `B, Dᵢ ∈ C¹`, `(dual:radial-origin)`–`(dual:radial-sum)`).
`H = gluedH R P` is the glued trial potential, `u = greenSum Γ a` the mean-zero torus potential off the charges.

**Gluing lemma** (`dual:gluing`; modules `Glue`, `LipschitzGlue`, `SiteLipschitz`, `SectorDeriv`, `Periodic`, `WExt`):
`gluedH_add` (`Γ`-periodic), `exists_lipschitzOnWith_ball` (locally Lipschitz off the sites: continuous, `H¹_loc`),
`eventuallyEq_gluedH_Hsec` + `hasFDerivAt_Hsec` (`C¹` on every open sector, the gradient statement is sectorwise),
`abs_gradSq_sub_inv_sq_le` (`|∇H|² = r⁻² + O(1)` on sectors), `exists_lipschitzOnWith_H1` / `locallyLipschitz_wExt`
(`H + log r` is Lipschitz across a site with value `0`: the constant term of `H` is zero) and `exists_lipschitzWith_wExt`.

**Sector quantities** (functions of `(P, p, q)`, summed over `voronoiIncidences Γ a`):
```
sectorRen R P p q = lim_{η↓0} [∫_{S(p,q) ∩ {‖z - p‖ > η}} |∇H|² + (α + β) log η]      (dual:sector-ren)
sectorJ   R P p q = -2π ∫_{S(p,q)} H - (1/2) sectorRen R P p q                          (dual:sector-functional)
```
(`tendsto_sectorRen` : the limit exists.)

**Theorem `dual_identity`** (`dual:identity`, `dual:energy-bound`): for `N ≥ 1`,
```
torusEnergy Γ a = ∑ e ∈ voronoiIncidences Γ a, sectorJ R P (a e.1) e.2
                  + (1/2) ∫_{torusDomain Γ} |∇(u - H)|²,
```
hence `∑ e, sectorJ R P (a e.1) e.2 ≤ torusEnergy Γ a` (`sum_sectorJ_le_torusEnergy`). In Lean:
```
theorem dual_identity [NeZero N] (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    (hR : R.IsAdmissible d₀) (hS : SepSites (periodicSites Γ a) d₀) :
    torusEnergy Γ a = ∑ e ∈ voronoiIncidences Γ a, sectorJ R (periodicSites Γ a) (a e.1) e.2 +
      (1 / 2 : ℝ) * ∫ x in torusDomain Γ, gradSq (fun y => greenSum Γ a y - gluedH R (periodicSites Γ a) y) x
``` No incidence bound and no square-torus
separation is used; the square-torus minimizer supplies `hS` (see `Dual.Separated`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis Torus

variable {ι : Type*} {R : RadialData ι} {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]
  {N : ℕ} {a : Fin N → ℂ} {d₀ : ℝ} {P : Set ℂ} {p q : ℂ}

/-- The renormalized sector integral `∫_S^ren |∇H|²` of `(dual:sector-ren)`. -/
@[expose] noncomputable def sectorRen (R : RadialData ι) (P : Set ℂ) (p q : ℂ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ =>
    (∫ z in voronoiSector P p q ∩ {z | η < ‖z - p‖}, gradSq (gluedH R P) z) +
      (sectorAlpha P p q + sectorBeta P p q) * Real.log η

/-- The sector functional `J(S) = -2π ∫_S H - ½ ∫_S^ren |∇H|²` of `(dual:sector-functional)`. -/
@[expose] noncomputable def sectorJ (R : RadialData ι) (P : Set ℂ) (p q : ℂ) : ℝ :=
  -(2 * Real.pi) * (∫ z in voronoiSector P p q, gluedH R P z) - (1 / 2 : ℝ) * sectorRen R P p q

theorem tendsto_sectorRen (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) :
    Tendsto (fun η : ℝ =>
      (∫ z in voronoiSector P p q ∩ {z | η < ‖z - p‖}, gradSq (gluedH R P) z) +
        (sectorAlpha P p q + sectorBeta P p q) * Real.log η) (𝓝[>] 0)
      (𝓝 (sectorRen R P p q)) := by
  obtain ⟨L, hL⟩ := tendsto_sectorRenInt hR hS h
  rw [sectorRen, hL.limUnder_eq]
  exact hL

section Main

local notation "𝐮" => greenSum Γ a
local notation "𝐰" => wExt R Γ a
local notation "𝐇" => gluedH R (periodicSites Γ a)
local notation "𝐃" => torusDomain Γ

variable [NeZero N]

/-- The sector sum of the cut-off energy of `H`. -/
theorem integral_cut_gradSq_H_eq_sum (hS : SepSites (periodicSites Γ a) d₀)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) {η : ℝ} (_hη : 0 < η)
    (hint : IntegrableOn (cut Γ a η (gradSq (gluedH R (periodicSites Γ a)))) (torusDomain Γ)) :
    ∫ x in torusDomain Γ, cut Γ a η (gradSq (gluedH R (periodicSites Γ a))) x =
      ∑ e ∈ voronoiIncidences Γ a,
        ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2 ∩ {z | η < ‖z - a e.1‖},
          gradSq (gluedH R (periodicSites Γ a)) z := by
  have hper : ∀ γ ∈ Γ, ∀ x, cut Γ a η (gradSq (gluedH R (periodicSites Γ a))) (x + γ) =
      cut Γ a η (gradSq (gluedH R (periodicSites Γ a))) x :=
    cut_periodic (gradSq_periodic' (gluedH_periodic hS)) η
  rw [integral_torusDomain_eq_sum_sector Γ a ha hper hint]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := (mem_voronoiIncidences Γ a).1 he
  have hSm := measurableSet_voronoiSector h
  have h1 : ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2,
        cut Γ a η (gradSq (gluedH R (periodicSites Γ a))) z =
      ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2,
        {z : ℂ | η ≤ ‖z - a e.1‖}.indicator (gradSq (gluedH R (periodicSites Γ a))) z := by
    refine setIntegral_congr_fun hSm fun z hz => ?_
    have hmem := mem_punctureSet_iff_of_mem_voronoiSector (η := η) hS h hz
    by_cases hlt : ‖z - a e.1‖ < η
    · have : z ∈ punctureSet Γ a η := hmem.2 hlt
      have h2 : z ∉ {z : ℂ | η ≤ ‖z - a e.1‖} := fun h' => absurd hlt (not_lt.2 h')
      simp [cut, this, h2]
    · have : z ∉ punctureSet Γ a η := fun h' => hlt (hmem.1 h')
      have h2 : z ∈ {z : ℂ | η ≤ ‖z - a e.1‖} := not_lt.1 hlt
      simp [cut, this, h2]
  rw [h1, setIntegral_indicator (measurableSet_le measurable_const (by fun_prop))]
  refine setIntegral_congr_set ?_
  have hnull : volume (sphere (a e.1) η) = 0 := Measure.addHaar_sphere volume _ η
  have hae : ∀ᵐ z ∂volume, z ∉ sphere (a e.1) η := measure_eq_zero_iff_ae_notMem.1 hnull
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [hae] with z hz
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hs, hle⟩
    refine ⟨hs, lt_of_le_of_ne hle fun heq => hz ?_⟩
    rw [mem_sphere, dist_eq_norm]; exact heq.symm
  · rintro ⟨hs, hlt⟩
    exact ⟨hs, hlt.le⟩

/-- **The cut-off identity.** -/
theorem integral_energyDensity_eq (hR : R.IsAdmissible d₀) (hS : SepSites (periodicSites Γ a) d₀)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) {K : NNReal} (hw : LipschitzWith K (wExt R Γ a))
    (hwper : ∀ γ ∈ Γ, ∀ x, wExt R Γ a (x + γ) = wExt R Γ a x)
    {η : ℝ} (hη : 0 < η) (hed : IntegrableOn (energyDensity Γ a η) (torusDomain Γ))
    (hX : IntegrableOn (gradDot (wExt R Γ a) (greenSum Γ a)) (torusDomain Γ)) :
    ∫ x in torusDomain Γ, energyDensity Γ a η x =
      2 * (∫ x in torusDomain Γ, cut Γ a η (gradDot (wExt R Γ a) (greenSum Γ a)) x) -
        (∫ x in torusDomain Γ, cut Γ a η (gradSq (wExt R Γ a)) x) +
        ∫ x in torusDomain Γ, cut Γ a η (gradSq (gluedH R (periodicSites Γ a))) x := by
  have hmeas : MeasurableSet (punctureSet Γ a η)ᶜ := (isOpen_punctureSet η).isClosed_compl.measurableSet
  have hXc : IntegrableOn (cut Γ a η (gradDot 𝐰 𝐮)) (torusDomain Γ) := hX.indicator hmeas
  have hYc : IntegrableOn (cut Γ a η (gradSq 𝐰)) (torusDomain Γ) :=
    (integrableOn_gradSq_wExt hw).indicator hmeas
  have hHc := integrableOn_cut_gradSq_H hR hS hw hη hed
  set Φ : ℂ → ℝ := fun x => energyDensity Γ a η x - 2 * cut Γ a η (gradDot 𝐰 𝐮) x +
    cut Γ a η (gradSq 𝐰) x - cut Γ a η (gradSq 𝐇) x with hΦ
  have hΦint : IntegrableOn Φ (torusDomain Γ) := ((hed.sub (hXc.const_mul 2)).add hYc).sub hHc
  have hupar : ∀ γ ∈ Γ, ∀ x, 𝐮 (x + γ) = 𝐮 x := fun γ hγ x => greenSum_add_period hγ x
  have hΦper : ∀ γ ∈ Γ, ∀ x, Φ (x + γ) = Φ x := by
    intro γ hγ x
    simp only [hΦ, energyDensity_add_period η hγ x,
      cut_periodic (gradDot_periodic hwper hupar) η γ hγ x,
      cut_periodic (gradSq_periodic' hwper) η γ hγ x,
      cut_periodic (gradSq_periodic' (gluedH_periodic hS)) η γ hγ x]
  have hzero : ∫ x in torusDomain Γ, Φ x = 0 := by
    rw [integral_torusDomain_eq_sum_sector Γ a ha hΦper hΦint]
    refine Finset.sum_eq_zero fun e he => ?_
    have h := (mem_voronoiIncidences Γ a).1 he
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hzc : z ∉ chargeSet Γ a := by
      rw [← periodicSites_eq_chargeSet]; exact notMem_of_mem_voronoiSector hS h hz
    have hdu : DifferentiableAt ℝ 𝐮 z := (contDiffAt_greenSum hzc).differentiableAt (by simp)
    have hdH := differentiableAt_gluedH_of_mem_sector hR hS h hz
    have key := gradSq_decomp hdu hdH (eventuallyEq_wExt (R := R) hzc)
    by_cases hp : z ∈ punctureSet Γ a η
    · simp [hΦ, energyDensity, cut, hp]
    · simp only [hΦ, energyDensity, cut, indicator_of_mem, mem_compl_iff, hp, not_false_eq_true]
      linarith
  have i1 : IntegrableOn (fun x => energyDensity Γ a η x - 2 * cut Γ a η (gradDot 𝐰 𝐮) x)
      (torusDomain Γ) := hed.sub (hXc.const_mul 2)
  have i2 : IntegrableOn (fun x => energyDensity Γ a η x - 2 * cut Γ a η (gradDot 𝐰 𝐮) x +
      cut Γ a η (gradSq 𝐰) x) (torusDomain Γ) := i1.add hYc
  have e1 := integral_sub i2 hHc
  have e2 := integral_add i1 hYc
  have e3 := integral_sub hed (hXc.const_mul 2)
  have e4 := integral_const_mul (μ := volume.restrict (torusDomain Γ)) (2 : ℝ)
    (cut Γ a η (gradDot 𝐰 𝐮))
  have hz2 : ∫ x in torusDomain Γ, Φ x = 0 := hzero
  simp only [hΦ] at hz2
  linarith

omit [NeZero N] in
theorem tendsto_sector_sum (hR : R.IsAdmissible d₀) (hS : SepSites (periodicSites Γ a) d₀) :
    Tendsto (fun η : ℝ =>
      (∑ e ∈ voronoiIncidences Γ a,
        ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2 ∩ {z | η < ‖z - a e.1‖},
          gradSq (gluedH R (periodicSites Γ a)) z) + 2 * Real.pi * N * Real.log η)
      (𝓝[>] 0)
      (𝓝 (∑ e ∈ voronoiIncidences Γ a, sectorRen R (periodicSites Γ a) (a e.1) e.2)) := by
  have hsum : ∀ η : ℝ, (∑ e ∈ voronoiIncidences Γ a,
        ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2 ∩ {z | η < ‖z - a e.1‖},
          gradSq (gluedH R (periodicSites Γ a)) z) + 2 * Real.pi * N * Real.log η =
      ∑ e ∈ voronoiIncidences Γ a,
        ((∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2 ∩ {z | η < ‖z - a e.1‖},
          gradSq (gluedH R (periodicSites Γ a)) z) +
          (sectorAlpha (periodicSites Γ a) (a e.1) e.2 +
            sectorBeta (periodicSites Γ a) (a e.1) e.2) * Real.log η) := by
    intro η
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_sectorAngle_voronoiIncidences]
  simp only [hsum]
  exact tendsto_finsetSum _ fun e he => tendsto_sectorRen hR hS ((mem_voronoiIncidences Γ a).1 he)

/-- **The dual identity** (paper Proposition `dual:identity`). -/
theorem dual_identity (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    (hR : R.IsAdmissible d₀) (hS : SepSites (periodicSites Γ a) d₀) :
    torusEnergy Γ a = ∑ e ∈ voronoiIncidences Γ a, sectorJ R (periodicSites Γ a) (a e.1) e.2 +
      (1 / 2 : ℝ) * ∫ x in torusDomain Γ,
        gradSq (fun y => greenSum Γ a y - gluedH R (periodicSites Γ a) y) x := by
  classical
  obtain ⟨K, hw⟩ := exists_lipschitzWith_wExt ha hR hS
  have hwper : ∀ γ ∈ Γ, ∀ x, 𝐰 (x + γ) = 𝐰 x := fun γ hγ x => wExt_add_period ha hS hγ x
  obtain ⟨hXint, hX0⟩ := pairing_identity hΓ ha hw hwper
  -- the energy as `π ∑ 𝐰(aᵢ)`
  have hwa : ∀ i, 𝐰 (a i) = cval Γ a i := fun i => wExt_of_mem ha (by simp)
  have hW : torusEnergy Γ a = Real.pi * ∑ i, 𝐰 (a i) := by
    rw [torusEnergy_eq_pairEnergy hΓ a ha]
    simp only [hwa, cval, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the integrals of `𝐰` and `𝐇`
  have hwint : IntegrableOn 𝐰 𝐃 := integrableOn_torusDomain_of_periodic Γ hw.continuous hwper
  have hae : ∀ᵐ x ∂(volume.restrict 𝐃), x ∉ chargeSet Γ a :=
    ae_restrict_of_ae ((countable_chargeSet Γ a).ae_notMem volume)
  have hHae : 𝐇 =ᵐ[volume.restrict 𝐃] fun x => 𝐮 x - 𝐰 x := by
    filter_upwards [hae] with x hx
    rw [wExt_of_notMem hx]; ring
  have hHint : IntegrableOn 𝐇 𝐃 := (integrableOn_greenSum.sub hwint).congr hHae.symm
  have hintH : ∫ x in 𝐃, 𝐇 x = - ∫ x in 𝐃, 𝐰 x := by
    rw [integral_congr_ae hHae, integral_sub integrableOn_greenSum hwint, integral_greenSum]
    ring
  have hHsum : ∫ x in 𝐃, 𝐇 x = ∑ e ∈ voronoiIncidences Γ a,
      ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2, 𝐇 z :=
    integral_torusDomain_eq_sum_sector Γ a ha (gluedH_periodic hS) hHint
  -- limits as `η ↓ 0`
  have hU : Tendsto (fun η : ℝ => (1 / 2 : ℝ) * (∫ x in 𝐃, energyDensity Γ a η x) +
      Real.pi * N * Real.log η) (𝓝[>] 0) (𝓝 (torusEnergy Γ a)) := by
    rw [torusEnergy_eq_pairEnergy hΓ a ha]
    refine (Torus.tendsto_pairEnergy hΓ ha).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [integral_excised_eq hΓ ha hη]
  have hX := tendsto_integral_cut (a := a) hXint
  have hY := tendsto_integral_cut (a := a) (integrableOn_gradSq_wExt hw)
  have hZ := tendsto_sector_sum hR hS (a := a)
  have hcomb := (hX.sub (hY.const_mul (1 / 2 : ℝ))).add (hZ.const_mul (1 / 2 : ℝ))
  have heq : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      (1 / 2 : ℝ) * (∫ x in 𝐃, energyDensity Γ a η x) + Real.pi * N * Real.log η =
        ((∫ x in 𝐃, cut Γ a η (gradDot 𝐰 𝐮) x) - (1 / 2 : ℝ) * ∫ x in 𝐃, cut Γ a η (gradSq 𝐰) x) +
          (1 / 2 : ℝ) * ((∑ e ∈ voronoiIncidences Γ a,
            ∫ z in voronoiSector (periodicSites Γ a) (a e.1) e.2 ∩ {z | η < ‖z - a e.1‖},
              gradSq 𝐇 z) + 2 * Real.pi * N * Real.log η) := by
    filter_upwards [integrableOn_energyDensity hΓ ha, self_mem_nhdsWithin] with η hed hη
    have hη' : 0 < η := hη
    have h1 := integral_energyDensity_eq hR hS ha hw hwper hη' hed hXint
    have h2 := integral_cut_gradSq_H_eq_sum (R := R) hS ha hη'
      (integrableOn_cut_gradSq_H hR hS hw hη' hed)
    rw [h2] at h1
    linear_combination (1 / 2 : ℝ) * h1
  have hlim := tendsto_nhds_unique (hU.congr' heq) hcomb
  -- the algebra
  have hX0' : ∫ x in 𝐃, gradDot 𝐰 𝐮 x = 2 * torusEnergy Γ a + 2 * Real.pi * ∫ x in 𝐃, 𝐇 x := by
    rw [hX0, hintH, hW]; ring
  have hY0 : ∫ x in 𝐃, gradSq 𝐰 x = ∫ x in 𝐃, gradSq (fun y => 𝐮 y - 𝐇 y) x := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [gradSq, pd₁, pd₂, (eventuallyEq_wExt (R := R) hx).fderiv_eq]
  have hJ : ∑ e ∈ voronoiIncidences Γ a, sectorJ R (periodicSites Γ a) (a e.1) e.2 =
      -(2 * Real.pi) * (∫ x in 𝐃, 𝐇 x) -
        (1 / 2 : ℝ) * ∑ e ∈ voronoiIncidences Γ a, sectorRen R (periodicSites Γ a) (a e.1) e.2 := by
    rw [hHsum]
    simp only [sectorJ, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hJ, ← hY0]
  rw [hX0'] at hlim
  linarith

/-- **The energy bound** (`dual:energy-bound`). -/
theorem sum_sectorJ_le_torusEnergy (hΓ : ZLattice.covolume Γ = N)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) (hR : R.IsAdmissible d₀)
    (hS : SepSites (periodicSites Γ a) d₀) :
    ∑ e ∈ voronoiIncidences Γ a, sectorJ R (periodicSites Γ a) (a e.1) e.2 ≤ torusEnergy Γ a := by
  rw [dual_identity hΓ ha hR hS]
  have : 0 ≤ ∫ x in torusDomain Γ,
      gradSq (fun y => greenSum Γ a y - gluedH R (periodicSites Γ a) y) x :=
    integral_nonneg fun x => gradSq_nonneg' _ x
  linarith

end Main

end Dual

end SandierSerfaty

end
