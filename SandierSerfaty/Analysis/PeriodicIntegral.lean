/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
public import SandierSerfaty.Torus.Lattice
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Integrals of periodic functions over the fundamental domain

For a lattice `Γ ⊆ ℂ` and `D = torusDomain Γ`:

* `volume D` is finite (`volume_torusDomain_ne_top`);
* a continuous `Γ`-periodic function is integrable over `D`
  (`integrableOn_torusDomain_of_periodic`);
* a periodic integrand may be translated: `∫ x in D, f (x + c) = ∫ x in D, f x`
  (`integral_torusDomain_add`);
* **periodic integration of a derivative** (`integral_torusDomain_fderiv`): for a `C¹`
  `Γ`-periodic `F`, `∫ x in D, fderiv ℝ F x e = 0` for every direction `e`. The proof differentiates
  `t ↦ ∫ x in D, F (x + t e)`, which is constant because `D + t e` is again a fundamental domain;
* **unfolding** (`integral_torusDomain_tsum`): `∫ x in D, ∑' γ : Γ, f (x + γ) = ∫ f` for integrable `f`.

These replace boundary terms of the divergence theorem on the periodic cell.
-/

open MeasureTheory Filter Topology Set
open scoped Pointwise

public section

namespace SandierSerfaty

namespace Torus

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem volume_torusDomain_ne_top : volume (torusDomain Γ) ≠ ⊤ := by
  have hD := (torusDomain_spec Γ).1
  have h1 : volume.real (torusDomain Γ) = ZLattice.covolume Γ :=
    (ZLattice.covolume_eq_measure_fundamentalDomain Γ volume hD).symm
  intro h
  have hpos := ZLattice.covolume_pos Γ (volume : Measure ℂ)
  rw [measureReal_def, h] at h1
  simp at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos

theorem volume_real_torusDomain : volume.real (torusDomain Γ) = ZLattice.covolume Γ :=
  (ZLattice.covolume_eq_measure_fundamentalDomain Γ volume (torusDomain_spec Γ).1).symm

/-- A continuous periodic real function is bounded. -/
theorem exists_bound_of_periodic {f : ℂ → ℝ} (hf : Continuous f)
    (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) : ∃ M : ℝ, ∀ x, |f x| ≤ M := by
  have hc := IsZLattice.isCompact_range_of_periodic Γ f hf (fun z w hw => hper w hw z)
  obtain ⟨M, hM⟩ := hc.isBounded.exists_norm_le
  exact ⟨M, fun x => by simpa using hM (f x) (Set.mem_range_self x)⟩

/-- A continuous periodic function is integrable over the fundamental domain. -/
theorem integrableOn_torusDomain_of_periodic {f : ℂ → ℝ} (hf : Continuous f)
    (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) : IntegrableOn f (torusDomain Γ) := by
  obtain ⟨M, hM⟩ := exists_bound_of_periodic Γ hf hper
  refine Measure.integrableOn_of_bounded (volume_torusDomain_ne_top Γ) hf.aestronglyMeasurable
    (M := M) ?_
  exact Filter.Eventually.of_forall fun x => by simpa using hM x

/-- The translate of the fundamental domain is a fundamental domain. -/
theorem isAddFundamentalDomain_vadd (c : ℂ) :
    IsAddFundamentalDomain Γ (c +ᵥ torusDomain Γ) volume :=
  (torusDomain_spec Γ).1.vadd_of_comm c

/-- A periodic integrand can be translated inside the integral over the fundamental domain. -/
theorem integral_torusDomain_add {f : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) (c : ℂ) :
    ∫ x in torusDomain Γ, f (c + x) = ∫ x in torusDomain Γ, f x := by
  have h1 := (torusDomain_spec Γ).2 _ (isAddFundamentalDomain_vadd Γ c) f hper
  rw [h1]
  have := (measurePreserving_add_left (volume : Measure ℂ) c).setIntegral_image_emb
    (measurableEmbedding_addLeft c) f (torusDomain Γ)
  have e : (fun x : ℂ => c + x) '' torusDomain Γ = c +ᵥ torusDomain Γ := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
  rw [e] at this
  exact this.symm


omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem fderiv_periodic {F : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x) {γ : ℂ} (hγ : γ ∈ Γ)
    (x : ℂ) : fderiv ℝ F (x + γ) = fderiv ℝ F x := by
  have : (fun y => F (y + γ)) = F := funext fun y => hper γ hγ y
  rw [← fderiv_comp_add_right γ (f := F) (x := x), this]

/-- **Periodic integration of a derivative.** For a `C¹` periodic `F`, the integral of every
directional derivative over the fundamental domain vanishes. -/
theorem integral_torusDomain_fderiv {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x) (e : ℂ) :
    ∫ x in torusDomain Γ, fderiv ℝ F x e = 0 := by
  set D := torusDomain Γ with hD
  have hdc : Continuous fun x => fderiv ℝ F x e :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdper : ∀ γ ∈ Γ, ∀ x, fderiv ℝ F (x + γ) e = fderiv ℝ F x e := fun γ hγ x => by
    rw [fderiv_periodic Γ hper hγ]
  obtain ⟨M, hM⟩ := exists_bound_of_periodic Γ hdc (fun γ hγ x => hdper γ hγ x)
  have hconst : (fun t : ℝ => ∫ x in D, F (x + t • e)) = fun _ => ∫ x in D, F x := by
    funext t
    have := integral_torusDomain_add Γ hper (t • e)
    simpa [add_comm] using this
  have h0 : HasDerivAt (fun t : ℝ => ∫ x in D, F (x + t • e)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have hint : Integrable (fun x => F (x + (0 : ℝ) • e)) (volume.restrict D) := by
    have h := integrableOn_torusDomain_of_periodic Γ hF.continuous hper
    simp only [zero_smul, add_zero]
    exact h
  have hfin : IsFiniteMeasure (volume.restrict D) := ⟨by
    rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (volume_torusDomain_ne_top Γ)⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict D)
    (F := fun (t : ℝ) x => F (x + t • e)) (F' := fun (t : ℝ) x => fderiv ℝ F (x + t • e) e)
    (x₀ := 0) (bound := fun _ => M) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      (hF.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    hint
    (by simpa using hdc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x t _ => by
      have := hM (x + t • e)
      have h2 : fderiv ℝ F (x + t • e) e = fderiv ℝ F (x + t • e) e := rfl
      simpa [Real.norm_eq_abs] using this)
    (integrable_const M)
    (Filter.Eventually.of_forall fun x t _ => by
      have h1 : HasDerivAt (fun s : ℝ => x + s • e) e t := by
        simpa using ((hasDerivAt_id t).smul_const e).const_add x
      exact (hF.differentiable one_ne_zero (x + t • e)).hasFDerivAt.comp_hasDerivAt t h1)
  have := h0.unique key.2
  simpa using this.symm


/-- **Unfolding.** The integral over `ℂ` of an integrable function is the integral over the
fundamental domain of its periodization. -/
theorem integral_torusDomain_tsum {f : ℂ → ℝ} (hf : Integrable f volume) :
    ∫ x in torusDomain Γ, ∑' γ : Γ, f ((γ : ℂ) + x) = ∫ x, f x := by
  have hD := (torusDomain_spec Γ).1
  have hmp : ∀ γ : Γ, MeasurePreserving (fun x : ℂ => (γ : ℂ) + x) volume volume := fun γ =>
    measurePreserving_add_left volume (γ : ℂ)
  have hmeas : ∀ γ : Γ, AEStronglyMeasurable (fun x : ℂ => f ((γ : ℂ) + x))
      (volume.restrict (torusDomain Γ)) := fun γ =>
    ((hf.1.comp_measurePreserving (hmp γ))).mono_measure Measure.restrict_le_self
  have hsum : ∑' γ : Γ, ∫⁻ x in torusDomain Γ, ‖f ((γ : ℂ) + x)‖ₑ ≠ ⊤ := by
    have := hD.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
    have h2 : ∫⁻ x, ‖f x‖ₑ ≠ ⊤ := hf.2.ne
    rw [this] at h2
    exact h2
  rw [integral_tsum hmeas hsum]
  have := hD.integral_eq_tsum'' f hf
  rw [this]
  rfl

end Torus

end SandierSerfaty

end
