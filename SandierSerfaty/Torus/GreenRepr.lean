/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Theorems.ExistsUniqueIsTorusPotential
public import SandierSerfaty.Torus.Green
public import SandierSerfaty.Torus.PotentialExists

/-!
# The torus potential as a sum of Green functions

For a lattice `Γ ⊆ ℂ` of covolume `N` and `N` charges `a i` with distinct classes modulo `Γ`
(paper Lemma `geo:existence`):

* `SandierSerfaty.Torus.torusPotential_eq_sum`: `torusPotential Γ a x = ∑ i, torusGreen Γ (x - a i)` off the
  charges (and `0` on them), by uniqueness of the torus potential;
* `SandierSerfaty.Torus.greenSum_localForm`: near the charge `a i`,
  `∑ j, G (x - a j) = s x - log ‖x - a i‖` with `s` smooth at `a i` and
  `s (a i) = R_Γ + ∑_{j ≠ i} G (a i - a j)`.
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff Pointwise Classical

public section

namespace SandierSerfaty

namespace Torus

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- The sum of the translated Green functions. -/
@[expose] noncomputable def greenSum {N : ℕ} (a : Fin N → ℂ) (x : ℂ) : ℝ :=
  ∑ i, torusGreen Γ (x - a i)

/-- Integrability of a translate of an integrable periodic function over the fundamental domain. -/
theorem integrableOn_torusDomain_translate {f : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x)
    (hint : IntegrableOn f (torusDomain Γ)) (c : ℂ) :
    IntegrableOn (fun x => f (c + x)) (torusDomain Γ) := by
  have hD := (torusDomain_spec Γ).1
  have hD' := isAddFundamentalDomain_vadd Γ c
  have hper' : ∀ (g : Γ) (x : ℂ), f (g +ᵥ x) = f x := fun g x => by
    have : g +ᵥ x = (g : ℂ) + x := rfl
    rw [this, add_comm]; exact hper g g.2 x
  have h1 : IntegrableOn f (c +ᵥ torusDomain Γ) := (hD.integrableOn_iff hD' hper').1 hint
  have hmp : MeasurePreserving (fun x : ℂ => c + x) volume volume := measurePreserving_add_left volume c
  have hpre : (fun x : ℂ => c + x) ⁻¹' (c +ᵥ torusDomain Γ) = torusDomain Γ := by
    ext y; simp [Set.mem_vadd_set]
  have := (hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft c)
    (f := f) (s := c +ᵥ torusDomain Γ)).2 h1
  rwa [hpre] at this

theorem integrableOn_torusGreen_sub (a : ℂ) :
    IntegrableOn (fun x => torusGreen Γ (x - a)) (torusDomain Γ) := by
  have := integrableOn_torusDomain_translate Γ (fun γ hγ x => torusGreen_add_period Γ hγ x)
    (integrableOn_torusGreen Γ) (-a)
  simpa [sub_eq_add_neg, add_comm] using this

theorem integral_torusGreen_sub (a : ℂ) : ∫ x in torusDomain Γ, torusGreen Γ (x - a) = 0 := by
  have := integral_torusDomain_add Γ (fun γ hγ x => torusGreen_add_period Γ hγ x) (-a)
  rw [← integral_torusGreen Γ]
  simpa [sub_eq_add_neg, add_comm] using this

variable {Γ} {N : ℕ} {a : Fin N → ℂ}

/-- **Local form at a charge.** Near `a i`, `∑ j, G (x - a j) = s x - log ‖x - a i‖` with `s` smooth at
`a i` and `s (a i) = R_Γ + ∑_{j ≠ i} G (a i - a j)`. -/
theorem greenSum_localForm (ha : ∀ i j, a i - a j ∈ Γ → i = j) (i : Fin N) :
    ∃ s : ℂ → ℝ, ContDiffAt ℝ ∞ s (a i) ∧
      s (a i) = torusRobin Γ + ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j) ∧
      ∀ᶠ x in 𝓝[≠] (a i), greenSum Γ a x = s x - Real.log ‖x - a i‖ := by
  classical
  obtain ⟨r, hr, hr0, hrev⟩ := torusGreen_localForm Γ
  have hsm : ∀ j ∈ Finset.univ.erase i, ContDiffAt ℝ ∞ (fun x => torusGreen Γ (x - a j)) (a i) := by
    intro j hj
    have hne : a i - a j ∉ Γ := fun hm => (Finset.ne_of_mem_erase hj) (ha i j hm).symm
    exact ContDiffAt.comp (g := torusGreen Γ) (f := fun y => y - a j) (a i)
      (contDiffAt_torusGreen Γ hne) (contDiffAt_id.sub contDiffAt_const)
  refine ⟨fun x => r (x - a i) + ∑ j ∈ Finset.univ.erase i, torusGreen Γ (x - a j), ?_, ?_, ?_⟩
  · refine ContDiffAt.add ?_ (ContDiffAt.sum hsm)
    have : ContDiffAt ℝ ∞ r ((fun x => x - a i) (a i)) := by simpa using hr
    exact ContDiffAt.comp (g := r) (f := fun y => y - a i) (a i) this
      (contDiffAt_id.sub contDiffAt_const)
  · simp [hr0]
  · have hmap : Tendsto (fun y => y - a i) (𝓝[≠] (a i)) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℂ => y - a i) (𝓝 (a i)) (𝓝 (a i - a i)) :=
          (continuous_id.sub continuous_const).tendsto (a i)
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_ne_zero.2 hy
    filter_upwards [hmap.eventually hrev] with x hx
    unfold greenSum
    rw [← Finset.add_sum_erase Finset.univ (fun j => torusGreen Γ (x - a j)) (Finset.mem_univ i), hx]
    ring

theorem greenSum_add_period {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    greenSum Γ a (x + γ) = greenSum Γ a x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have : x + γ - a i = (x - a i) + γ := by ring
  rw [this, torusGreen_add_period Γ hγ]

theorem contDiffAt_greenSum {x : ℂ} (hx : x ∉ chargeSet Γ a) : ContDiffAt ℝ ∞ (greenSum Γ a) x :=
  ContDiffAt.sum fun i _ =>
    ContDiffAt.comp (g := torusGreen Γ) (f := fun y => y - a i) x
      (contDiffAt_torusGreen Γ (notMem_chargeSet_iff.1 hx i)) (contDiffAt_id.sub contDiffAt_const)

theorem laplacian_greenSum (hΓ : ZLattice.covolume Γ = N) {x : ℂ} (hx : x ∉ chargeSet Γ a) :
    Δ (greenSum Γ a) x = 2 * Real.pi := by
  classical
  have hNpos : (0 : ℝ) < N := hΓ ▸ ZLattice.covolume_pos Γ
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      ContDiffAt ℝ 2 (fun y => torusGreen Γ (y - a i)) x := fun i _ =>
    (ContDiffAt.comp (g := torusGreen Γ) (f := fun y => y - a i) x
      (contDiffAt_torusGreen Γ (notMem_chargeSet_iff.1 hx i))
      (contDiffAt_id.sub contDiffAt_const)).of_le (by simp)
  have hSe : greenSum Γ a = fun y => ∑ i, torusGreen Γ (y - a i) := rfl
  rw [hSe, Analysis.laplacian_finset_sum _ _ x h2]
  have : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      Δ (fun y => torusGreen Γ (y - a i)) x = 2 * Real.pi / N := by
    intro i _
    rw [Analysis.laplacian_comp_sub, laplacian_torusGreen Γ (notMem_chargeSet_iff.1 hx i), hΓ]
  rw [Finset.sum_congr rfl this]
  simp
  field_simp

theorem locallyIntegrable_torusGreen : LocallyIntegrable (torusGreen Γ) volume := by
  obtain ⟨r, hr, -, hev⟩ := torusGreen_localForm Γ
  exact locallyIntegrable_of_localForm Γ (fun γ hγ x => torusGreen_add_period Γ hγ x)
    (fun z hz => (contDiffAt_torusGreen Γ hz).continuousAt) hr.continuousAt hev

theorem locallyIntegrable_comp_sub {f : ℂ → ℝ} (hf : LocallyIntegrable f volume) (c : ℂ) :
    LocallyIntegrable (fun x => f (x - c)) volume := by
  have h : LocallyIntegrable f (Measure.map (Homeomorph.subRight c) volume) := by
    have := (measurePreserving_sub_right (volume : Measure ℂ) c).map_eq
    rw [show (⇑(Homeomorph.subRight c) : ℂ → ℂ) = fun x => x - c from rfl, this]; exact hf
  exact (locallyIntegrable_map_homeomorph (Homeomorph.subRight c)).1 h

theorem locallyIntegrable_greenSum : LocallyIntegrable (greenSum Γ a) volume :=
  locallyIntegrable_finsetSum (s := Finset.univ) (f := fun i x => torusGreen Γ (x - a i))
    fun i _ => locallyIntegrable_comp_sub (locallyIntegrable_torusGreen (Γ := Γ)) (a i)

theorem integrableOn_greenSum : IntegrableOn (greenSum Γ a) (torusDomain Γ) :=
  integrable_finsetSum _ fun i _ => integrableOn_torusGreen_sub Γ (a i)

theorem integral_greenSum : ∫ x in torusDomain Γ, greenSum Γ a x = 0 := by
  have hSe : greenSum Γ a = fun y => ∑ i, torusGreen Γ (y - a i) := rfl
  rw [hSe, integral_finsetSum _ fun i _ => integrableOn_torusGreen_sub Γ (a i)]
  simp [integral_torusGreen_sub]

/-- The function `x ↦ if x ∈ charges then 0 else ∑ i, G (x - a i)` is a torus potential. -/
theorem isTorusPotential_greenSum (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IsTorusPotential Γ a (fun x => if x ∈ chargeSet Γ a then 0 else greenSum Γ a x) := by
  classical
  have hNpos : (0 : ℝ) < N := hΓ ▸ ZLattice.covolume_pos Γ
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  set P := chargeSet Γ a with hP
  have hPcl : IsClosed P := isClosed_chargeSet Γ a
  set S : ℂ → ℝ := greenSum Γ a with hS
  have hsm' : ∀ x, x ∉ P → ∀ i, ContDiffAt ℝ ∞ (fun y => torusGreen Γ (y - a i)) x := fun x hx i =>
    ContDiffAt.comp (g := torusGreen Γ) (f := fun y => y - a i) x
      (contDiffAt_torusGreen Γ (notMem_chargeSet_iff.1 hx i)) (contDiffAt_id.sub contDiffAt_const)
  have hSsm : ∀ x, x ∉ P → ContDiffAt ℝ ∞ S x := fun x hx =>
    ContDiffAt.sum fun i _ => hsm' x hx i
  have hSΔ : ∀ x, x ∉ P → Δ S x = 2 * Real.pi := by
    intro x hx
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        ContDiffAt ℝ 2 (fun y => torusGreen Γ (y - a i)) x :=
      fun i _ => (hsm' x hx i).of_le (by simp)
    have hSe : S = fun y => ∑ i, torusGreen Γ (y - a i) := rfl
    rw [hSe, Analysis.laplacian_finset_sum _ _ x h2]
    have : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        Δ (fun y => torusGreen Γ (y - a i)) x = 2 * Real.pi / N := by
      intro i _
      rw [Analysis.laplacian_comp_sub, laplacian_torusGreen Γ (notMem_chargeSet_iff.1 hx i), hΓ]
    rw [Finset.sum_congr rfl this]
    simp
    field_simp
  have hSper : ∀ γ ∈ Γ, ∀ x, S (x + γ) = S x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun i _ => ?_
    have : x + γ - a i = (x - a i) + γ := by ring
    rw [this, torusGreen_add_period Γ hγ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ x
    by_cases hx : x ∈ P
    · have : x + γ ∈ P := (add_mem_chargeSet_iff (a := a) hγ x).2 hx
      simp [hx, this]
    · have : x + γ ∉ P := fun h => hx ((add_mem_chargeSet_iff (a := a) hγ x).1 h)
      simp [hx, this, hSper γ hγ x]
  · intro x hx
    have hxP : x ∉ P := notMem_chargeSet_iff.2 hx
    refine ContDiffAt.contDiffWithinAt ((hSsm x hxP).congr_of_eventuallyEq ?_)
    filter_upwards [hPcl.isOpen_compl.mem_nhds hxP] with y hy
    simp only [Set.mem_compl_iff] at hy
    simp [hy]
  · intro x hx
    have hxP : x ∉ P := notMem_chargeSet_iff.2 hx
    have hev : (fun y => if y ∈ P then (0 : ℝ) else S y) =ᶠ[𝓝 x] S := by
      filter_upwards [hPcl.isOpen_compl.mem_nhds hxP] with y hy
      simp only [Set.mem_compl_iff] at hy
      simp [hy]
    rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
    exact hSΔ x hxP
  · intro i
    obtain ⟨s, hs, hsi, hev⟩ := greenSum_localForm ha i
    refine ⟨s (a i), ?_⟩
    have hs' : Tendsto s (𝓝[≠] (a i)) (𝓝 (s (a i))) := hs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hs'.congr' ?_
    filter_upwards [hev, eventually_notMem_chargeSet Γ a (a i)] with y hy hyP
    have hy' : y ∉ P := hyP
    simp only [hy', ↓reduceIte]
    have hy2 : S y = s y - Real.log ‖y - a i‖ := hy
    rw [hy2]; ring
  · have hae : (fun x => if x ∈ P then (0 : ℝ) else S x) =ᵐ[volume.restrict (torusDomain Γ)] S := by
      have : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ P := (countable_chargeSet Γ a).ae_notMem volume
      exact ae_restrict_of_ae (this.mono fun x hx => by simp [hx])
    have hSe : S = fun y => ∑ i, torusGreen Γ (y - a i) := rfl
    rw [integral_congr_ae hae, hSe, integral_finsetSum _ fun i _ => integrableOn_torusGreen_sub Γ (a i)]
    simp [integral_torusGreen_sub]
  · intro x hx
    have : x ∈ P := hx
    simp [this]


/-- **Representation of the torus potential** (Lemma `geo:existence`): off the charges it is
`∑ i, G_Γ (x - a i)`, and it is `0` on the charges. -/
theorem torusPotential_eq_sum (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    torusPotential Γ a = fun x => if x ∈ chargeSet Γ a then 0 else greenSum Γ a x := by
  obtain ⟨h₀, hh₀, huniq⟩ := existsUnique_isTorusPotential Γ hΓ a ha
  have hspec : IsTorusPotential Γ a (torusPotential Γ a) :=
    Classical.epsilon_spec (p := IsTorusPotential Γ a) ⟨h₀, hh₀⟩
  exact (huniq _ hspec).trans (huniq _ (isTorusPotential_greenSum hΓ ha)).symm

/-- Off the charges, the torus potential is `∑ i, G_Γ (x - a i)`. -/
theorem torusPotential_apply (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    {x : ℂ} (hx : ∀ i, x - a i ∉ Γ) : torusPotential Γ a x = ∑ i, torusGreen Γ (x - a i) := by
  rw [torusPotential_eq_sum hΓ ha]
  have : x ∉ chargeSet Γ a := notMem_chargeSet_iff.2 hx
  simp [this, greenSum]

end Torus

end SandierSerfaty

end
