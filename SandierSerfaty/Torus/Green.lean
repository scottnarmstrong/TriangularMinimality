/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PeriodicIntegral
public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import SandierSerfaty.Torus.ChargeSet
public import SandierSerfaty.Torus.GreenLocal
public import SandierSerfaty.Torus.LatticePeriods
public import SandierSerfaty.Torus.PotentialIntegrable
public import SandierSerfaty.Torus.PotentialUnique
public import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# The mean-zero Green function of a lattice

For a lattice `Γ ⊆ ℂ`, `SandierSerfaty.torusGreen Γ` is the unique `Γ`-periodic function `G` with

* `G` smooth off `Γ` and `Δ G = 2π / covol Γ` there (so `-ΔG = 2π (δ₀ - 1/covol Γ)` on `ℂ/Γ`),
* a logarithmic singularity at `0` with smooth regular part: `G z = r z - log ‖z‖` near `0` with `r`
  of class `C^∞` at `0`,
* mean zero over a fundamental domain, and `G = 0` on `Γ` (the convention of the torus
  potential `IsTorusPotential`).

The Robin constant is `torusRobin Γ = lim_{x → 0} (G x + log ‖x‖) = r 0`.

Existence is the theta construction `SandierSerfaty.Torus.greenOne` shifted by its mean; uniqueness
is the maximum principle across punctures (`SandierSerfaty.Torus.exists_const_of_periodic_harmonic`).
-/

open MeasureTheory Filter Topology Laplacian Metric
open scoped ContDiff

public section

namespace SandierSerfaty

/-- The characterization of the mean-zero Green function `G` of the lattice `Γ`: see the module
docstring. -/
@[expose] def IsTorusGreen (Γ : Submodule ℤ ℂ) (G : ℂ → ℝ) : Prop :=
  (∀ γ ∈ Γ, ∀ x, G (x + γ) = G x) ∧
  (∀ x, x ∉ Γ → ContDiffAt ℝ ∞ G x) ∧
  (∀ x, x ∉ Γ → Δ G x = 2 * Real.pi / ZLattice.covolume Γ) ∧
  (∃ r : ℂ → ℝ, ContDiffAt ℝ ∞ r 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z = r z - Real.log ‖z‖) ∧
  (∫ x in torusDomain Γ, G x = 0) ∧
  (∀ x ∈ Γ, G x = 0)

namespace Torus

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem chargeSet_zero : chargeSet Γ (fun _ : Fin 1 => (0 : ℂ)) = (Γ : Set ℂ) := by
  ext x; simp [chargeSet]

omit [IsZLattice ℝ Γ] in
theorem eventually_notMem_lattice : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ Γ := by
  have := eventually_notMem_chargeSet Γ (fun _ : Fin 1 => (0 : ℂ)) 0
  rwa [chargeSet_zero] at this

omit [IsZLattice ℝ Γ] in
theorem isOpen_lattice_compl : IsOpen ((Γ : Set ℂ)ᶜ) := (isClosed_lattice Γ).isOpen_compl

theorem countable_lattice : (Γ : Set ℂ).Countable := by
  have := countable_chargeSet Γ (fun _ : Fin 1 => (0 : ℂ))
  rwa [chargeSet_zero] at this

/-- A periodic locally integrable function is integrable over the fundamental domain. -/
theorem integrableOn_torusDomain_of_locallyIntegrable {f : ℂ → ℝ}
    (hloc : LocallyIntegrable f volume) (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) :
    IntegrableOn f (torusDomain Γ) := by
  have := ZLattice.module_free ℝ Γ
  have := ZLattice.module_finite ℝ Γ
  set b := Module.Free.chooseBasis ℤ Γ with hb
  have hfdD := ZLattice.isAddFundamentalDomain b (volume : Measure ℂ)
  have hbd : Bornology.IsBounded (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_isBounded _
  have hDint : IntegrableOn f (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    (hloc.integrableOn_isCompact hbd.isCompact_closure).mono_set subset_closure
  have hper' : ∀ (g : Γ) (x : ℂ), f (g +ᵥ x) = f x := fun g x => by
    have : g +ᵥ x = (g : ℂ) + x := rfl
    rw [this, add_comm]; exact hper g g.2 x
  exact (hfdD.integrableOn_iff (torusDomain_spec Γ).1 hper').1 hDint

/-- A periodic function that is continuous off `Γ` and has a log singularity with continuous regular
part at `0` is integrable over the fundamental domain. -/
theorem locallyIntegrable_of_localForm {G : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x)
    (hcont' : ∀ z, z ∉ Γ → ContinuousAt G z) {r : ℂ → ℝ} (hr : ContinuousAt r 0)
    (hrev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z = r z - Real.log ‖z‖) :
    LocallyIntegrable G volume := by
  have hcont : ContinuousOn G ((Γ : Set ℂ)ᶜ) := fun z hz => (hcont' z hz).continuousWithinAt
  have hmeas : AEStronglyMeasurable G volume := by
    have h1 : AEStronglyMeasurable G (volume.restrict ((Γ : Set ℂ)ᶜ)) :=
      hcont.aestronglyMeasurable (isOpen_lattice_compl Γ).measurableSet
    have hae : ∀ᵐ x ∂(volume : Measure ℂ), x ∈ (Γ : Set ℂ)ᶜ :=
      (countable_lattice Γ).ae_notMem volume
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1
  · intro x
    by_cases hx : x ∈ Γ
    · have hlim : Tendsto (fun z => G z + Real.log ‖z‖) (𝓝[≠] 0) (𝓝 (r 0)) := by
        have hrc : Tendsto r (𝓝[≠] 0) (𝓝 (r 0)) := hr.tendsto.mono_left nhdsWithin_le_nhds
        refine hrc.congr' ?_
        filter_upwards [hrev] with z hz
        rw [hz]; ring
      have hbound : ∀ᶠ y in 𝓝[≠] x, |G y + Real.log ‖y - x‖| ≤ ‖r 0‖ + 1 := by
        have hmap : Tendsto (fun y => y - x) (𝓝[≠] x) (𝓝[≠] 0) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have : Tendsto (fun y : ℂ => y - x) (𝓝 x) (𝓝 (x - x)) :=
              (continuous_id.sub continuous_const).tendsto x
            rw [sub_self] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with y hy
            exact sub_ne_zero.2 hy
        have h1 := (hlim.comp hmap).norm.eventually
          (eventually_lt_nhds (a := ‖r 0‖) (b := ‖r 0‖ + 1) (by linarith))
        filter_upwards [h1] with y hy
        have e : G (y - x) = G y := by
          have := hper x hx (y - x)
          rw [sub_add_cancel] at this
          exact this.symm
        simp only [Function.comp, e] at hy
        exact hy.le
      exact integrableAtFilter_of_log_bound hmeas hbound
    · have hx' : x ∈ (Γ : Set ℂ)ᶜ := hx
      have := (hcont.locallyIntegrableOn (μ := volume) (isOpen_lattice_compl Γ).measurableSet) x hx'
      rwa [(isOpen_lattice_compl Γ).nhdsWithin_eq hx'] at this

theorem integrableOn_torusDomain_of_localForm {G : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x)
    (hcont' : ∀ z, z ∉ Γ → ContinuousAt G z) {r : ℂ → ℝ} (hr : ContinuousAt r 0)
    (hrev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z = r z - Real.log ‖z‖) :
    IntegrableOn G (torusDomain Γ) :=
  integrableOn_torusDomain_of_locallyIntegrable Γ
    (locallyIntegrable_of_localForm Γ hper hcont' hr hrev) hper

/-- Existence of a function with the properties of the mean-zero Green function. -/
theorem exists_isTorusGreen : ∃ G : ℂ → ℝ, IsTorusGreen Γ G ∧ ∀ x, G (-x) = G x := by
  classical
  obtain ⟨p, τ, hp, hτ, hmem, hcov⟩ := exists_period_ratio Γ
  set G₀ := greenOne p τ with hG₀
  have hnz : ∀ z, z ∉ Γ → theta τ (z / p) ≠ 0 := by
    intro z hz h
    obtain ⟨m, n, hmn⟩ := (theta_eq_zero_iff hτ _).1 h
    apply hz
    rw [hmem]
    exact ⟨m, n, by rw [← hmn]; field_simp⟩
  have hper : ∀ γ ∈ Γ, ∀ z, G₀ (z + γ) = G₀ z := by
    intro γ hγ z
    obtain ⟨m, n, rfl⟩ := (hmem γ).1 hγ
    exact greenOne_add_period hτ hp z m n
  have hsm : ∀ z, z ∉ Γ → ContDiffAt ℝ ∞ G₀ z := fun z hz => contDiffAt_greenOne hτ (hnz z hz)
  have hcovpos : 0 < ZLattice.covolume Γ := ZLattice.covolume_pos Γ volume
  have hΔ : ∀ z, z ∉ Γ → Δ G₀ z = 2 * Real.pi / ZLattice.covolume Γ := fun z hz => by
    rw [hG₀, laplacian_greenOne hτ hp (hnz z hz), hcov]
  have hzero : ∀ z ∈ Γ, G₀ z = 0 := by
    intro z hz
    obtain ⟨m, n, rfl⟩ := (hmem z).1 hz
    have : theta τ ((p * (m + n * τ)) / p) = 0 := by
      rw [mul_div_cancel_left₀ _ hp]
      exact (theta_eq_zero_iff hτ _).2 ⟨m, n, rfl⟩
    simp [hG₀, greenOne, thetaGreen0, this]
  obtain ⟨r, hr, hrev⟩ := greenOne_localForm hτ hp
  have hint : IntegrableOn G₀ (torusDomain Γ) :=
    integrableOn_torusDomain_of_localForm Γ hper (fun z hz => (hsm z hz).continuousAt)
      hr.continuousAt hrev
  set c : ℝ := (∫ x in torusDomain Γ, G₀ x) / ZLattice.covolume Γ with hc
  refine ⟨fun x => if x ∈ Γ then 0 else G₀ x - c, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ hγ x
    have : x + γ ∈ Γ ↔ x ∈ Γ := by
      constructor
      · intro h
        have := Γ.sub_mem h hγ
        simpa using this
      · intro h; exact Γ.add_mem h hγ
    by_cases hx : x ∈ Γ
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx, hper γ hγ x]
  · intro x hx
    have h1 : ContDiffAt ℝ ∞ (fun y => G₀ y - c) x := (hsm x hx).sub contDiffAt_const
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lattice_compl Γ).mem_nhds hx] with y hy
    have hy' : y ∉ Γ := hy
    simp [hy']
  · intro x hx
    have hev : (fun y => if y ∈ Γ then (0 : ℝ) else G₀ y - c) =ᶠ[𝓝 x] (fun y => G₀ y - c) := by
      filter_upwards [(isOpen_lattice_compl Γ).mem_nhds hx] with y hy
      have hy' : y ∉ Γ := hy
      simp [hy']
    rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
    have hS2 : ContDiffAt ℝ 2 G₀ x := (hsm x hx).of_le (by simp)
    have e : (fun y => G₀ y - c) = G₀ - fun _ => c := rfl
    rw [e, ContDiffAt.laplacian_sub hS2 contDiffAt_const, hΔ x hx, InnerProductSpace.laplacian_const]
    simp
  · refine ⟨fun z => r z - c, hr.sub contDiffAt_const, ?_⟩
    filter_upwards [hrev, eventually_notMem_lattice Γ] with z hz hzΓ
    have hz' : G₀ z = r z - Real.log ‖z‖ := hz
    simp only [hzΓ, ite_false, hz']
    ring
  · have hae : (fun x => if x ∈ Γ then (0 : ℝ) else G₀ x - c) =ᵐ[volume.restrict (torusDomain Γ)]
        fun x => G₀ x - c := by
      have : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ (Γ : Set ℂ) := (countable_lattice Γ).ae_notMem volume
      exact ae_restrict_of_ae (this.mono fun x hx => by
        have hx' : x ∉ Γ := hx
        simp [hx'])
    rw [integral_congr_ae hae]
    have hfin : volume (torusDomain Γ) ≠ ⊤ := volume_torusDomain_ne_top Γ
    rw [integral_sub hint (integrableOn_const hfin), setIntegral_const, volume_real_torusDomain Γ]
    simp only [smul_eq_mul, hc]
    field_simp
    ring
  · intro x hx
    simp [hx]
  · intro x
    have hneg : -x ∈ Γ ↔ x ∈ Γ := by
      constructor
      · intro h; simpa using Γ.neg_mem h
      · intro h; exact Γ.neg_mem h
    by_cases hx : x ∈ Γ
    · simp [hx, hneg.2 hx]
    · have : -x ∉ Γ := fun h => hx (hneg.1 h)
      simp [hx, this, hG₀, greenOne_neg]


/-- **Uniqueness of the mean-zero Green function.** -/
theorem IsTorusGreen.unique {G₁ G₂ : ℂ → ℝ} (h₁ : IsTorusGreen Γ G₁) (h₂ : IsTorusGreen Γ G₂) :
    G₁ = G₂ := by
  obtain ⟨hp₁, hs₁, hΔ₁, ⟨r₁, hr₁, hl₁⟩, hm₁, hz₁⟩ := h₁
  obtain ⟨hp₂, hs₂, hΔ₂, ⟨r₂, hr₂, hl₂⟩, hm₂, hz₂⟩ := h₂
  set a : Fin 1 → ℂ := fun _ => 0 with ha
  have hP : chargeSet Γ a = (Γ : Set ℂ) := chargeSet_zero Γ
  have hPc : (chargeSet Γ a)ᶜ = (Γ : Set ℂ)ᶜ := by rw [hP]
  have hper : ∀ γ ∈ Γ, ∀ x, (G₁ - G₂) (x + γ) = (G₁ - G₂) x := fun γ hγ x => by
    simp [hp₁ γ hγ x, hp₂ γ hγ x]
  have hharm : InnerProductSpace.HarmonicOnNhd (G₁ - G₂) (chargeSet Γ a)ᶜ := by
    rw [hPc]
    intro x hx
    have hx' : x ∉ Γ := hx
    have hc₁ : ContDiffAt ℝ 2 G₁ x := (hs₁ x hx').of_le (by norm_cast)
    have hc₂ : ContDiffAt ℝ 2 G₂ x := (hs₂ x hx').of_le (by norm_cast)
    refine ⟨hc₁.sub hc₂, ?_⟩
    filter_upwards [hc₁.laplacian_sub_nhds hc₂, (isOpen_lattice_compl Γ).mem_nhds hx] with y hy hyP
    have hy' : y ∉ Γ := hyP
    rw [hy, Pi.sub_apply, hΔ₁ y hy', hΔ₂ y hy']
    simp
  have hlim0 : Tendsto (G₁ - G₂) (𝓝[≠] 0) (𝓝 (r₁ 0 - r₂ 0)) := by
    have hrc : Tendsto (fun z => r₁ z - r₂ z) (𝓝[≠] 0) (𝓝 (r₁ 0 - r₂ 0)) :=
      ((hr₁.continuousAt.sub hr₂.continuousAt).tendsto).mono_left nhdsWithin_le_nhds
    refine hrc.congr' ?_
    filter_upwards [hl₁, hl₂] with z h1 h2
    simp [h1, h2]
  have hlim : ∀ p ∈ chargeSet Γ a, ∃ L : ℝ, Tendsto (G₁ - G₂) (𝓝[≠] p) (𝓝 L) := by
    intro p hp
    rw [hP] at hp
    have hmap : Tendsto (fun y => y - p) (𝓝[≠] p) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℂ => y - p) (𝓝 p) (𝓝 (p - p)) :=
          (continuous_id.sub continuous_const).tendsto p
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_ne_zero.2 hy
    refine ⟨r₁ 0 - r₂ 0, (hlim0.comp hmap).congr fun y => ?_⟩
    have := hper p hp (y - p)
    rw [sub_add_cancel] at this
    simpa [Function.comp] using this.symm
  obtain ⟨C, hC⟩ := exists_const_of_periodic_harmonic Γ a hper hharm hlim
  have hC0 : C = 0 := by
    have hfd := (torusDomain_spec Γ).1
    have hae : ∀ᵐ x ∂(volume.restrict (torusDomain Γ)), G₁ x - G₂ x = C := by
      apply ae_restrict_of_ae
      filter_upwards [(countable_lattice Γ).ae_notMem volume] with x hx
      have hx' : x ∉ chargeSet Γ a := by rw [hP]; exact hx
      exact hC x hx'
    have hint : ∫ x in torusDomain Γ, (G₁ x - G₂ x) = 0 := by
      have i₁ : IntegrableOn G₁ (torusDomain Γ) :=
        integrableOn_torusDomain_of_localForm Γ hp₁ (fun z hz => (hs₁ z hz).continuousAt)
          hr₁.continuousAt hl₁
      have i₂ : IntegrableOn G₂ (torusDomain Γ) :=
        integrableOn_torusDomain_of_localForm Γ hp₂ (fun z hz => (hs₂ z hz).continuousAt)
          hr₂.continuousAt hl₂
      rw [integral_sub i₁ i₂, hm₁, hm₂, sub_self]
    rw [integral_congr_ae hae, setIntegral_const, smul_eq_mul] at hint
    have hpos : 0 < volume.real (torusDomain Γ) := by
      rw [volume_real_torusDomain Γ]; exact ZLattice.covolume_pos Γ volume
    exact (mul_eq_zero.1 hint).resolve_left hpos.ne'
  funext x
  by_cases hx : x ∈ Γ
  · rw [hz₁ x hx, hz₂ x hx]
  · have hx' : x ∉ chargeSet Γ a := by rw [hP]; exact hx
    have := hC x hx'
    simp only [Pi.sub_apply] at this
    linarith

end Torus

/-- The mean-zero Green function `G_Γ` of the lattice `Γ`, by unique choice
(`SandierSerfaty.IsTorusGreen`; uniqueness is `SandierSerfaty.Torus.IsTorusGreen.unique`). -/
@[expose] noncomputable def torusGreen (Γ : Submodule ℤ ℂ) : ℂ → ℝ :=
  Classical.epsilon (IsTorusGreen Γ)

/-- The Robin constant `R_Γ = lim_{x → 0} (G_Γ x + log ‖x‖)` of the lattice `Γ`. -/
@[expose] noncomputable def torusRobin (Γ : Submodule ℤ ℂ) : ℝ :=
  limUnder (𝓝[≠] (0 : ℂ)) fun x => torusGreen Γ x + Real.log ‖x‖

section API

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem isTorusGreen_torusGreen : IsTorusGreen Γ (torusGreen Γ) :=
  (Classical.epsilon_spec (p := IsTorusGreen Γ)
    (let ⟨G, hG, _⟩ := Torus.exists_isTorusGreen Γ; ⟨G, hG⟩))

theorem torusGreen_eq_of_isTorusGreen {G : ℂ → ℝ} (hG : IsTorusGreen Γ G) : G = torusGreen Γ :=
  Torus.IsTorusGreen.unique Γ hG (isTorusGreen_torusGreen Γ)

/-- `G_Γ` is periodic. -/
theorem torusGreen_add_period {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    torusGreen Γ (x + γ) = torusGreen Γ x :=
  (isTorusGreen_torusGreen Γ).1 γ hγ x

/-- `G_Γ` is smooth off the lattice. -/
theorem contDiffAt_torusGreen {x : ℂ} (hx : x ∉ Γ) : ContDiffAt ℝ ∞ (torusGreen Γ) x :=
  (isTorusGreen_torusGreen Γ).2.1 x hx

/-- `Δ G_Γ = 2π / covol Γ` off the lattice. -/
theorem laplacian_torusGreen {x : ℂ} (hx : x ∉ Γ) :
    Δ (torusGreen Γ) x = 2 * Real.pi / ZLattice.covolume Γ :=
  (isTorusGreen_torusGreen Γ).2.2.1 x hx

/-- `G_Γ` has mean zero over the fundamental domain. -/
theorem integral_torusGreen : ∫ x in torusDomain Γ, torusGreen Γ x = 0 :=
  (isTorusGreen_torusGreen Γ).2.2.2.2.1

/-- `G_Γ = 0` on the lattice (convention). -/
theorem torusGreen_of_mem {x : ℂ} (hx : x ∈ Γ) : torusGreen Γ x = 0 :=
  (isTorusGreen_torusGreen Γ).2.2.2.2.2 x hx

/-- `G_Γ` is even. -/
theorem torusGreen_neg (x : ℂ) : torusGreen Γ (-x) = torusGreen Γ x := by
  obtain ⟨G, hG, hneg⟩ := Torus.exists_isTorusGreen Γ
  rw [← torusGreen_eq_of_isTorusGreen Γ hG]
  exact hneg x

/-- The local form of `G_Γ` at the lattice point `0`: `G_Γ z = r z - log ‖z‖` with `r` smooth at `0`
and `r 0 = R_Γ`. -/
theorem torusGreen_localForm :
    ∃ r : ℂ → ℝ, ContDiffAt ℝ ∞ r 0 ∧ r 0 = torusRobin Γ ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), torusGreen Γ z = r z - Real.log ‖z‖ := by
  obtain ⟨r, hr, hev⟩ := (isTorusGreen_torusGreen Γ).2.2.2.1
  have hlim : Tendsto (fun z => torusGreen Γ z + Real.log ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 (r 0)) := by
    have hrc : Tendsto r (𝓝[≠] (0 : ℂ)) (𝓝 (r 0)) := hr.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hrc.congr' ?_
    filter_upwards [hev] with z hz
    rw [hz]; ring
  exact ⟨r, hr, hlim.limUnder_eq.symm, hev⟩

/-- The Robin constant is the limit of `G_Γ x + log ‖x‖` at `0`. -/
theorem tendsto_torusGreen_add_log :
    Tendsto (fun x => torusGreen Γ x + Real.log ‖x‖) (𝓝[≠] (0 : ℂ)) (𝓝 (torusRobin Γ)) := by
  obtain ⟨r, hr, hr0, hev⟩ := torusGreen_localForm Γ
  rw [← hr0]
  have hrc : Tendsto r (𝓝[≠] (0 : ℂ)) (𝓝 (r 0)) := hr.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hrc.congr' ?_
  filter_upwards [hev] with z hz
  rw [hz]; ring

/-- `G_Γ` is integrable over the fundamental domain. -/
theorem integrableOn_torusGreen : IntegrableOn (torusGreen Γ) (torusDomain Γ) := by
  obtain ⟨r, hr, -, hev⟩ := torusGreen_localForm Γ
  exact Torus.integrableOn_torusDomain_of_localForm Γ (fun γ hγ x => torusGreen_add_period Γ hγ x)
    (fun z hz => (contDiffAt_torusGreen Γ hz).continuousAt) hr.continuousAt hev

end API

end SandierSerfaty

end
