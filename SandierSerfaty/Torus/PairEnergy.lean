/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Torus.PairEnergyIdentity
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The pair-energy identity for the torus potential

Paper Lemma `geo:existence`, `(geo:pair-energy)`: for a lattice `Γ`
of covolume `N` and `N` charges `a i` with distinct classes modulo `Γ`,
```
lim_{η → 0+} (½ ∫_{D ∖ ⋃ B(a i + γ, η)} |∇h|² + π N log η) = π N R_Γ + π ∑_{i ≠ j} G_Γ (a i - a j),
```
where `h = torusPotential Γ a`, `G_Γ = torusGreen Γ` and `R_Γ = torusRobin Γ`
(`SandierSerfaty.Torus.tendsto_torusEnergy_pairEnergy`); consequently
`torusEnergy Γ a = π N R_Γ + π ∑_{i ≠ j} G_Γ (a i - a j)` (`SandierSerfaty.torusEnergy_eq_pairEnergy`).
The case `N = 1` is the energy `π R_Γ` of one charge (`SandierSerfaty.torusEnergy_one`).
-/

open MeasureTheory Filter Topology Metric Laplacian
open scoped ContDiff ENNReal NNReal

public section

namespace SandierSerfaty

namespace Torus

open Analysis

/-- The integral of a locally integrable function over a shrinking ball tends to `0`. -/
theorem tendsto_setIntegral_ball {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (c : ℂ) :
    Tendsto (fun η : ℝ => ∫ x in ball c η, f x) (𝓝[>] 0) (𝓝 0) := by
  have hI : Integrable f (volume.restrict (closedBall c 1)) :=
    hf.integrableOn_isCompact (isCompact_closedBall c 1)
  have hμ : Tendsto (fun η : ℝ => (volume.restrict (closedBall c 1)) (ball c η)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun η : ℝ => volume (ball c η)) (𝓝[>] 0) (𝓝 0) := by
      simp only [Complex.volume_ball]
      have hc : Tendsto (fun η : ℝ => ENNReal.ofReal η ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have hc' : Continuous fun η : ℝ => ENNReal.ofReal η ^ 2 :=
          (ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal
        have := hc'.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const hc (Or.inr ENNReal.coe_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun η => bot_le) ?_
    intro η
    exact Measure.restrict_apply_le _ _
  have := hI.tendsto_setIntegral_nhds_zero hμ
  refine this.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with η hη
  have hsub : ball c η ⊆ closedBall c 1 :=
    (ball_subset_ball hη.2).trans ball_subset_closedBall
  rw [Measure.restrict_restrict measurableSet_ball, Set.inter_eq_left.2 hsub]

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ}

/-- Off the charges, the gradient of the torus potential is the gradient of `greenSum`. -/
theorem gradient_torusPotential_eq (hΓ : ZLattice.covolume Γ = N)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) {x : ℂ} (hx : x ∉ chargeSet Γ a) :
    ‖gradient (torusPotential Γ a) x‖ ^ 2 = gradSq (greenSum Γ a) x := by
  have hev : torusPotential Γ a =ᶠ[𝓝 x] greenSum Γ a := by
    rw [torusPotential_eq_sum hΓ ha]
    filter_upwards [(isClosed_chargeSet Γ a).isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ chargeSet Γ a := hy
    simp [hy']
  have : gradient (torusPotential Γ a) x = gradient (greenSum Γ a) x := by
    simp only [gradient, hev.fderiv_eq]
  rw [this, norm_gradient_sq]
  rfl

/-- The excised integral equals the integral of the truncated density. -/
theorem integral_excised_eq (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    {η : ℝ} (hη : 0 < η) :
    ∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
        ‖gradient (torusPotential Γ a) x‖ ^ 2 =
      ∫ x in torusDomain Γ, energyDensity Γ a η x := by
  have hD := (torusDomain_spec Γ).1
  have hU : MeasurableSet (punctureSet Γ a η)ᶜ := (isOpen_punctureSet η).isClosed_compl.measurableSet
  have hset : torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η =
      (punctureSet Γ a η)ᶜ ∩ torusDomain Γ := by
    ext x; simp [punctureSet, Set.sdiff_eq, and_comm]
  rw [hset]
  have hind : ∫ x in torusDomain Γ, energyDensity Γ a η x =
      ∫ x in (punctureSet Γ a η)ᶜ ∩ torusDomain Γ, gradSq (greenSum Γ a) x := by
    unfold energyDensity
    have := integral_indicator (μ := volume.restrict (torusDomain Γ)) (f := gradSq (greenSum Γ a)) hU
    rw [Measure.restrict_restrict hU] at this
    exact this
  rw [hind]
  refine setIntegral_congr_fun₀ ((hU.nullMeasurableSet).inter hD.nullMeasurableSet) fun x hx => ?_
  have hxU : x ∉ punctureSet Γ a η := hx.1
  have hxP : x ∉ chargeSet Γ a := by
    intro hP
    obtain ⟨i, hi⟩ := hP
    exact hxU (mem_punctureSet.2 ⟨i, x - a i, hi, by simpa using hη⟩)
  exact gradient_torusPotential_eq hΓ ha hxP

/-- **The puncture limit** (`(geo:pair-energy)`): the truncated energy converges to
`π N R_Γ + π ∑_{i ≠ j} G_Γ (a i - a j)`. -/
theorem tendsto_pairEnergy (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    Tendsto (fun η : ℝ =>
        (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
          ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η)
      (𝓝[>] 0)
      (𝓝 (Real.pi * N * torusRobin Γ +
        Real.pi * ∑ i, ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j))) := by
  classical
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep Γ a
  have hPD : PairData Γ a ρ := ⟨hΓ, ha, hsep, hρ⟩
  set u := greenSum Γ a with hu
  -- the circle terms
  have hcirc : ∀ i : Fin N, Tendsto (fun η => circleTerm u (a i) η - 2 * Real.pi * Real.log η)
      (𝓝[>] 0) (𝓝 (-(2 * Real.pi) *
        (torusRobin Γ + ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j)))) := by
    intro i
    obtain ⟨s, hs, hsi, hev⟩ := greenSum_localForm ha i
    have hdu : ∀ᶠ x in 𝓝[≠] (a i), DifferentiableAt ℝ u x := by
      filter_upwards [eventually_notMem_chargeSet Γ a (a i)] with x hx
      exact (contDiffAt_greenSum hx).differentiableAt (by simp)
    have := tendsto_circleTerm_sub_log (u := u) (s := s) (p := a i)
      (hs.of_le (by norm_cast)) hev hdu
    rwa [hsi] at this
  have hball : ∀ i : Fin N, Tendsto (fun η : ℝ => ∫ x in ball (a i) η, u x) (𝓝[>] 0) (𝓝 0) :=
    fun i => tendsto_setIntegral_ball (locallyIntegrable_greenSum (Γ := Γ) (a := a)) (a i)
  have hlim : Tendsto (fun η : ℝ => -(1 / 2 : ℝ) * ∑ i, (circleTerm u (a i) η - 2 * Real.pi * Real.log η) +
      Real.pi * ∑ i, ∫ x in ball (a i) η, u x) (𝓝[>] 0)
      (𝓝 (-(1 / 2 : ℝ) * ∑ i, (-(2 * Real.pi) *
        (torusRobin Γ + ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j))) + Real.pi * ∑ _i : Fin N, (0 : ℝ))) :=
    ((tendsto_finsetSum _ fun i _ => hcirc i).const_mul _).add
      ((tendsto_finsetSum _ fun i _ => hball i).const_mul _)
  have hval : -(1 / 2 : ℝ) * ∑ i, (-(2 * Real.pi) *
        (torusRobin Γ + ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j))) +
        Real.pi * ∑ _i : Fin N, (0 : ℝ) =
      Real.pi * N * torusRobin Γ + Real.pi * ∑ i, ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j) := by
    simp only [Finset.sum_const_zero, mul_zero, add_zero, ← Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hρ] with η hη
  have hη0 : 0 < η := hη.1
  rw [integral_excised_eq hΓ ha hη0, hPD.energy_identity hη0 hη.2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← hu]
  ring

end Torus

/-- **The pair-energy identity** (paper `(geo:pair-energy)`): `𝒲_Γ(a) = π N R_Γ + π ∑_{i ≠ j} G_Γ (aᵢ - aⱼ)`. -/
theorem torusEnergy_eq_pairEnergy {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}
    (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    torusEnergy Γ a = Real.pi * N * torusRobin Γ +
      Real.pi * ∑ i, ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j) :=
  (Torus.tendsto_pairEnergy hΓ ha).limUnder_eq

/-- **One charge** (`N = 1`, the closed-form note's Proposition A): on a lattice of covolume `1` the energy of a single
charge is `π` times the Robin constant `R_Γ`, wherever the charge sits. -/
theorem torusEnergy_one {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hΓ : ZLattice.covolume Γ = 1) (a : Fin 1 → ℂ) :
    torusEnergy Γ a = Real.pi * torusRobin Γ := by
  have h1 : ZLattice.covolume Γ = ((1 : ℕ) : ℝ) := by simpa using hΓ
  have ha : ∀ i j : Fin 1, a i - a j ∈ Γ → i = j := fun i j _ => Subsingleton.elim i j
  rw [torusEnergy_eq_pairEnergy h1 a ha]
  simp

end SandierSerfaty


end
