/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.HarmonicRemovable
public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
public import SandierSerfaty.Torus.ChargeSet
public import SandierSerfaty.Torus.PotentialIntegrable
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Uniqueness of the torus potential

`SandierSerfaty.Torus.isTorusPotential_unique`: two potentials `h₁`, `h₂` with the properties of
`SandierSerfaty.IsTorusPotential` coincide. This is the uniqueness half of the theorem
`SandierSerfaty.existsUnique_isTorusPotential`.

The difference `u = h₁ - h₂` is `Γ`-periodic, harmonic off the charges, and has a finite limit at each
charge (the logarithmic singularities cancel). Instead of a removable-singularity theorem (whose proof
needs a Dirichlet solver that Mathlib lacks) we use the maximum principle across punctures
(`SandierSerfaty.Analysis.HarmonicRemovable`): the continuous extension of `u` is periodic, hence
attains its maximum, hence is constant. The mean-zero normalization (which needs the integrability of
the potentials, `SandierSerfaty.Torus.PotentialIntegrable`) forces the constant to vanish, and the
convention `h = 0` at the charges gives equality there.
-/

open MeasureTheory Filter Topology Laplacian InnerProductSpace

public section

namespace SandierSerfaty

namespace Torus

/-- A periodic function, harmonic off the charges and with a finite limit at each charge, is
constant off the charges. -/
theorem exists_const_of_periodic_harmonic (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {N : ℕ} (a : Fin N → ℂ) {u : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, u (x + γ) = u x) (hharm : HarmonicOnNhd u (chargeSet Γ a)ᶜ)
    (hlim : ∀ p ∈ chargeSet Γ a, ∃ L : ℝ, Tendsto u (𝓝[≠] p) (𝓝 L)) :
    ∃ C : ℝ, ∀ x ∉ chargeSet Γ a, u x = C := by
  set P := chargeSet Γ a with hPdef
  have hPcl : IsClosed P := isClosed_chargeSet Γ a
  -- the continuous extension of `u`
  set v : ℂ → ℝ := fun x => limUnder (𝓝[≠] x) u with hv
  have hv_off : ∀ x ∉ P, v x = u x := by
    intro x hx
    have hc : ContinuousAt u x := (hharm x hx).1.continuousAt
    exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hv_tend : ∀ p ∈ P, Tendsto u (𝓝[≠] p) (𝓝 (v p)) := fun p hp =>
    tendsto_nhds_limUnder (hlim p hp)
  have hv_ev : ∀ x ∉ P, v =ᶠ[𝓝 x] u := fun x hx => by
    filter_upwards [hPcl.isOpen_compl.mem_nhds hx] with y hy using hv_off y hy
  have hvc : Continuous v := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ P
    · rw [continuousAt_iff_punctured_nhds]
      refine (hv_tend x hx).congr' ?_
      filter_upwards [eventually_notMem_chargeSet Γ a x] with y hy using (hv_off y hy).symm
    · exact ((hharm x hx).1.continuousAt).congr (hv_ev x hx).symm
  have hvper : ∀ z w, w ∈ Γ → v (z + w) = v z := by
    intro z w hw
    simp only [hv, limUnder]
    congr 1
    have h1 : 𝓝[≠] (z + w) = Filter.map (fun y : ℂ => y + w) (𝓝[≠] z) := by
      simp
    rw [h1, Filter.map_map]
    congr 1
    funext y
    exact hper w hw y
  have hvh : HarmonicOnNhd v Pᶜ := fun x hx =>
    (harmonicAt_congr_nhds (hv_ev x hx)).2 (hharm x hx)
  obtain ⟨m, ⟨x₀, rfl⟩, hm⟩ := (IsZLattice.isCompact_range_of_periodic Γ v hvc hvper).exists_isMaxOn
    (Set.range_nonempty v) continuousOn_id
  have hmax : ∀ x, v x ≤ v x₀ := fun x => hm (Set.mem_range_self x)
  have hconst := eq_of_isMaxOn_of_harmonicOnNhd_compl hPcl (countable_chargeSet Γ a)
    (fun p _ => eventually_notMem_chargeSet Γ a p) hvc hvh hmax
  exact ⟨v x₀, fun x hx => by rw [← hv_off x hx, hconst x]⟩

/-- **Uniqueness of the torus potential.** -/
theorem isTorusPotential_unique (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (_hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (_ha : ∀ i j, a i - a j ∈ Γ → i = j)
    {h₁ h₂ : ℂ → ℝ} (h₁P : IsTorusPotential Γ a h₁) (h₂P : IsTorusPotential Γ a h₂) :
    h₁ = h₂ := by
  set P := chargeSet Γ a with hPdef
  have hPo : IsOpen Pᶜ := (isClosed_chargeSet Γ a).isOpen_compl
  have hmemP : ∀ x, x ∉ P ↔ ∀ i, x - a i ∉ Γ := fun x => notMem_chargeSet_iff
  have hPo' : IsOpen {x : ℂ | ∀ i, x - a i ∉ Γ} := by
    have : {x : ℂ | ∀ i, x - a i ∉ Γ} = Pᶜ := by ext x; exact (hmemP x).symm
    rw [this]; exact hPo
  -- the difference is harmonic off the charges
  have hharm : HarmonicOnNhd (h₁ - h₂) Pᶜ := by
    intro x hx
    have hc₁ : ContDiffAt ℝ 2 h₁ x :=
      ((h₁P.2.1.contDiffAt (hPo'.mem_nhds ((hmemP x).1 hx))).of_le
        (by norm_cast))
    have hc₂ : ContDiffAt ℝ 2 h₂ x :=
      ((h₂P.2.1.contDiffAt (hPo'.mem_nhds ((hmemP x).1 hx))).of_le
        (by norm_cast))
    refine ⟨hc₁.sub hc₂, ?_⟩
    filter_upwards [hc₁.laplacian_sub_nhds hc₂, hPo.mem_nhds hx] with y hy hyP
    have hyP' : ∀ i, y - a i ∉ Γ := (hmemP y).1 hyP
    rw [hy, Pi.sub_apply, h₁P.2.2.1 y hyP', h₂P.2.2.1 y hyP']
    simp
  have hlim : ∀ p ∈ P, ∃ L : ℝ, Tendsto (h₁ - h₂) (𝓝[≠] p) (𝓝 L) := by
    intro p hp
    obtain ⟨c₁, hc₁⟩ := h₁P.exists_tendsto_of_mem_chargeSet hp
    obtain ⟨c₂, hc₂⟩ := h₂P.exists_tendsto_of_mem_chargeSet hp
    refine ⟨c₁ - c₂, (hc₁.sub hc₂).congr fun y => ?_⟩
    simp
  have hper : ∀ γ ∈ Γ, ∀ x, (h₁ - h₂) (x + γ) = (h₁ - h₂) x := fun γ hγ x => by
    simp [h₁P.1 γ hγ x, h₂P.1 γ hγ x]
  obtain ⟨C, hC⟩ := exists_const_of_periodic_harmonic Γ a hper hharm hlim
  -- the constant vanishes by the mean-zero normalization
  have hC0 : C = 0 := by
    have hfd := (torusDomain_spec Γ).1
    have hi₁ := h₁P.integrableOn_torusDomain
    have hi₂ := h₂P.integrableOn_torusDomain
    have hint : ∫ x in torusDomain Γ, (h₁ x - h₂ x) = 0 := by
      rw [integral_sub hi₁ hi₂, h₁P.2.2.2.2.1, h₂P.2.2.2.2.1, sub_self]
    have hae : ∀ᵐ x ∂(volume.restrict (torusDomain Γ)), h₁ x - h₂ x = C := by
      apply ae_restrict_of_ae
      filter_upwards [(countable_chargeSet Γ a).ae_notMem volume] with x hx
      exact hC x hx
    rw [integral_congr_ae hae, setIntegral_const] at hint
    have hcov : ZLattice.covolume Γ = volume.real (torusDomain Γ) :=
      ZLattice.covolume_eq_measure_fundamentalDomain Γ volume hfd
    have hpos : 0 < volume.real (torusDomain Γ) := by
      rw [← hcov]; exact ZLattice.covolume_pos Γ volume
    rw [smul_eq_mul] at hint
    exact (mul_eq_zero.1 hint).resolve_left hpos.ne'
  funext x
  by_cases hx : x ∈ P
  · rw [h₁P.2.2.2.2.2 x hx, h₂P.2.2.2.2.2 x hx]
  · have := hC x hx
    simp only [Pi.sub_apply] at this
    linarith

end Torus

end SandierSerfaty

end
