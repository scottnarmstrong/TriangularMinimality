/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
public import SandierSerfaty.Torus.ChargeSet
public import SandierSerfaty.Torus.GreenOne
public import SandierSerfaty.Torus.LatticePeriods
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Existence of the torus potential

`SandierSerfaty.Torus.exists_isTorusPotential`: for a lattice `Γ ⊆ ℂ` of covolume `N` and `N` charges
`a i` with pairwise distinct classes modulo `Γ`, there is a function `h` with
`SandierSerfaty.IsTorusPotential Γ a h`. This is the existence half of the theorem
`SandierSerfaty.existsUnique_isTorusPotential` (uniqueness is
`SandierSerfaty.Torus.isTorusPotential_unique`).

## Route

An explicit single-charge Green function, built from Jacobi's theta product (route (a) of the brief;
Weierstrass `σ`/`ζ` are not in Mathlib, and the theta product has *elementary* quasi-periodicity).
Write `Γ = p (ℤ + ℤ τ)` (`SandierSerfaty.Torus.exists_period_ratio`) and
`θ(w) = (1 - e(-w)) ∏ₙ (1 - Qⁿ⁺¹ e(w)) ∏ₙ (1 - Qⁿ⁺¹ e(-w))` with `e(w) = exp (2 π i w)`, `Q = e(τ)`
(`SandierSerfaty.Torus.theta`). Then `θ(w + 1) = θ(w)`, `θ(w + τ) = -Q⁻¹ e(-w) θ(w)`, the zeros of `θ` are
exactly `ℤ + ℤ τ`, and `0` is a simple zero. Hence
`g(w) = -log ‖θ(w)‖ + π (Im w)² / Im τ + π Im w` is `ℤ + ℤ τ`-periodic off the zeros, `Δ g = 2π / Im τ`,
and `g(w) + log ‖w‖` has a finite limit at `0`. Rescaling, `G(z) = g(z / p)` (`SandierSerfaty.Torus.greenOne`)
has `Δ G = 2π / covol Γ` and a `-log` singularity at each lattice point
(`SandierSerfaty.Torus.exists_green`). With `covol Γ = N`, `S(x) = ∑ᵢ G(x - a i)` has `Δ S = 2π` off the
charges; the potential is `S - mean` off the charges and `0` on them.

The mean-zero clause is arranged without knowing integrability of `S` on the fundamental domain
(if `S` were not integrable, `S - c` would not be either and both integrals vanish);
integrability does hold, by `SandierSerfaty.IsTorusPotential.integrableOn_torusDomain`.
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- The single-charge Green function of a lattice. -/
theorem exists_green (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ G : ℂ → ℝ, (∀ γ ∈ Γ, ∀ z, G (z + γ) = G z) ∧
      (∀ z, z ∉ Γ → ContDiffAt ℝ ∞ G z) ∧
      (∀ z, z ∉ Γ → Δ G z = 2 * Real.pi / ZLattice.covolume Γ) ∧
      ∃ c : ℝ, Tendsto (fun z => G z + Real.log ‖z‖) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨p, τ, hp, hτ, hmem, hcov⟩ := exists_period_ratio Γ
  have hnz : ∀ z, z ∉ Γ → theta τ (z / p) ≠ 0 := by
    intro z hz h
    obtain ⟨m, n, hmn⟩ := (theta_eq_zero_iff hτ _).1 h
    apply hz
    rw [hmem]
    exact ⟨m, n, by rw [← hmn]; field_simp⟩
  refine ⟨greenOne p τ, ?_, ?_, ?_, tendsto_greenOne_add_log hτ hp⟩
  · intro γ hγ z
    obtain ⟨m, n, rfl⟩ := (hmem γ).1 hγ
    exact greenOne_add_period hτ hp z m n
  · intro z hz
    exact contDiffAt_greenOne hτ (hnz z hz)
  · intro z hz
    rw [laplacian_greenOne hτ hp (hnz z hz), hcov]

theorem add_mem_chargeSet_iff {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} {γ : ℂ} (hγ : γ ∈ Γ)
    (x : ℂ) : x + γ ∈ chargeSet Γ a ↔ x ∈ chargeSet Γ a := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have e : x - a i = (x + γ - a i) - γ := by ring
    rw [e]
    exact Γ.sub_mem hi hγ
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have e : x + γ - a i = (x - a i) + γ := by ring
    rw [e]
    exact Γ.add_mem hi hγ

/-- **Existence of the torus potential.** -/
theorem exists_isTorusPotential (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) : ∃ h : ℂ → ℝ, IsTorusPotential Γ a h := by
  classical
  obtain ⟨G, hper, hsm, hΔ, c₁, hlim⟩ := exists_green Γ
  have hNpos : (0 : ℝ) < N := hΓ ▸ ZLattice.covolume_pos Γ
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  set P := chargeSet Γ a with hP
  have hPcl : IsClosed P := isClosed_chargeSet Γ a
  set S : ℂ → ℝ := fun x => ∑ i, G (x - a i) with hS
  have hsm' : ∀ x, x ∉ P → ∀ i, ContDiffAt ℝ ∞ (fun y => G (y - a i)) x := fun x hx i =>
    ContDiffAt.comp (g := G) (f := fun y => y - a i) x
      (hsm (x - a i) (notMem_chargeSet_iff.1 hx i)) (contDiffAt_id.sub contDiffAt_const)
  have hSsm : ∀ x, x ∉ P → ContDiffAt ℝ ∞ S x := fun x hx =>
    ContDiffAt.sum fun i _ => hsm' x hx i
  have hSΔ : ∀ x, x ∉ P → Δ S x = 2 * Real.pi := by
    intro x hx
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin N)), ContDiffAt ℝ 2 (fun y => G (y - a i)) x :=
      fun i _ => (hsm' x hx i).of_le (by simp)
    rw [hS, Analysis.laplacian_finset_sum _ _ x h2]
    have : ∀ i ∈ (Finset.univ : Finset (Fin N)), Δ (fun y => G (y - a i)) x = 2 * Real.pi / N := by
      intro i _
      rw [Analysis.laplacian_comp_sub, hΔ _ (notMem_chargeSet_iff.1 hx i), hΓ]
    rw [Finset.sum_congr rfl this]
    simp
    field_simp
  have hSper : ∀ γ ∈ Γ, ∀ x, S (x + γ) = S x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun i _ => ?_
    have : x + γ - a i = (x - a i) + γ := by ring
    rw [this, hper γ hγ]
  obtain ⟨hD, hDint⟩ := torusDomain_spec Γ
  set D := torusDomain Γ with hDdef
  set c : ℝ := (∫ x in D, S x) / N with hc
  refine ⟨fun x => if x ∈ P then 0 else S x - c, ?_⟩
  unfold IsTorusPotential
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ x
    by_cases hx : x ∈ P
    · have : x + γ ∈ P := (add_mem_chargeSet_iff (a := a) hγ x).2 hx
      simp [hx, this]
    · have : x + γ ∉ P := fun h => hx ((add_mem_chargeSet_iff (a := a) hγ x).1 h)
      simp [hx, this, hSper γ hγ x]
  · intro x hx
    have hxP : x ∉ P := notMem_chargeSet_iff.2 hx
    have h1 : ContDiffAt ℝ ∞ (fun y => S y - c) x := (hSsm x hxP).sub contDiffAt_const
    refine ContDiffAt.contDiffWithinAt (h1.congr_of_eventuallyEq ?_)
    filter_upwards [hPcl.isOpen_compl.mem_nhds hxP] with y hy
    simp only [Set.mem_compl_iff] at hy
    simp [hy]
  · intro x hx
    have hxP : x ∉ P := notMem_chargeSet_iff.2 hx
    have hev : (fun y => if y ∈ P then (0 : ℝ) else S y - c) =ᶠ[𝓝 x] (fun y => S y - c) := by
      filter_upwards [hPcl.isOpen_compl.mem_nhds hxP] with y hy
      simp only [Set.mem_compl_iff] at hy
      simp [hy]
    have hc2 := (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds
    rw [hc2]
    have hS2 : ContDiffAt ℝ 2 S x := (hSsm x hxP).of_le (by simp)
    have e : (fun y => S y - c) = S - fun _ => c := rfl
    rw [e, ContDiffAt.laplacian_sub hS2 contDiffAt_const, hSΔ x hxP, InnerProductSpace.laplacian_const]
    simp
  · intro i
    have hcont : ∀ j, j ≠ i → ContinuousAt (fun y => G (y - a j)) (a i) := by
      intro j hj
      have hne : a i - a j ∉ Γ := fun hm => hj (ha i j hm).symm
      exact (ContDiffAt.comp (g := G) (f := fun y => y - a j) (a i)
        (hsm (a i - a j) hne) (contDiffAt_id.sub contDiffAt_const)).continuousAt
    have hmap : Tendsto (fun y => y - a i) (𝓝[≠] (a i)) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℂ => y - a i) (𝓝 (a i)) (𝓝 (a i - a i)) :=
          (continuous_id.sub continuous_const).tendsto (a i)
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_ne_zero.2 hy
    have h1 : Tendsto (fun y => G (y - a i) + Real.log ‖y - a i‖) (𝓝[≠] (a i)) (𝓝 c₁) :=
      hlim.comp hmap
    have h2 : Tendsto (fun y => ∑ j ∈ Finset.univ.erase i, G (y - a j)) (𝓝[≠] (a i))
        (𝓝 (∑ j ∈ Finset.univ.erase i, G (a i - a j))) :=
      tendsto_finsetSum _ fun j hj =>
        (hcont j (Finset.ne_of_mem_erase hj)).tendsto.mono_left nhdsWithin_le_nhds
    refine ⟨c₁ + ∑ j ∈ Finset.univ.erase i, G (a i - a j) - c, ?_⟩
    refine ((h1.add h2).sub_const c).congr' ?_
    filter_upwards [eventually_notMem_chargeSet Γ a (a i)] with y hy
    have hy' : y ∉ P := hy
    simp only [hy', ↓reduceIte]
    rw [hS]
    beta_reduce
    rw [← Finset.add_sum_erase Finset.univ (fun j => G (y - a j)) (Finset.mem_univ i)]
    ring
  · have hae : (fun x => if x ∈ P then (0 : ℝ) else S x - c) =ᵐ[volume.restrict D]
        fun x => S x - c := by
      have : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ P := (countable_chargeSet Γ a).ae_notMem volume
      exact ae_restrict_of_ae (this.mono fun x hx => by simp [hx])
    rw [integral_congr_ae hae]
    have hvol : volume.real D = N := by
      rw [← hΓ]; exact (ZLattice.covolume_eq_measure_fundamentalDomain Γ volume hD).symm
    have hfin : volume D ≠ ⊤ := by
      intro h
      rw [measureReal_def, h] at hvol
      simp at hvol
      exact hN0 hvol.symm
    by_cases hint : IntegrableOn S D
    · rw [integral_sub hint (integrableOn_const hfin), setIntegral_const, hvol]
      simp only [smul_eq_mul, hc]
      field_simp
      ring
    · have : ¬ IntegrableOn (fun x => S x - c) D := fun h =>
        hint (by
          have := h.add (integrableOn_const hfin (C := c))
          convert this using 1
          funext x
          simp)
      exact integral_undef this
  · intro x hx
    have : x ∈ P := hx
    simp [this]

end Torus

end SandierSerfaty

end
