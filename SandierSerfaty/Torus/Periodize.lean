/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PeriodicIntegral
public import SandierSerfaty.Torus.ChargeSet
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Periodization of compactly supported functions

For `f : ℂ → ℝ` supported in a ball, `SandierSerfaty.Torus.periodize Γ f x = ∑' γ : Γ, f (γ + x)` is a
locally finite sum:

* `Γ`-periodic (`periodize_add_period`);
* smooth when `f` is (`contDiff_periodize`), with `fderiv` computed termwise (`fderiv_periodize`);
* unfolding: `∫ x in D, periodize f x * F x = ∫ f * F` for periodic `F` (`integral_periodize_mul`).

This is the smooth periodic partition of unity that replaces the boundary terms of the cell.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- The periodization `x ↦ ∑' γ ∈ Γ, f (γ + x)`. -/
@[expose] noncomputable def periodize (Γ : Submodule ℤ ℂ) (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∑' γ : Γ, f ((γ : ℂ) + x)

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ]

/-- Finitely many lattice translates meet a bounded set. -/
theorem finite_lattice_translates (c x : ℂ) (R : ℝ) :
    {γ : Γ | ‖(γ : ℂ) + x - c‖ ≤ R}.Finite := by
  have hfin : (closedBall (c - x) R ∩ (Γ : Set ℂ)).Finite :=
    Metric.finite_isBounded_inter_isClosed (K := closedBall (c - x) R) (s := (Γ : Set ℂ))
      (by exact DiscreteTopology.isDiscrete) isBounded_closedBall (isClosed_lattice Γ)
  refine (hfin.preimage (f := fun γ : Γ => (γ : ℂ)) (Subtype.val_injective.injOn)).subset ?_
  intro γ hγ
  refine ⟨?_, γ.2⟩
  rw [mem_closedBall, dist_eq_norm]
  have : (γ : ℂ) - (c - x) = (γ : ℂ) + x - c := by ring
  rw [this]; exact hγ

variable {Γ}

/-- Near `x`, the periodization is a finite sum. -/
theorem periodize_eventuallyEq_sum {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hsupp : ∀ y, ρ < ‖y - c‖ → f y = 0)
    (x : ℂ) : ∃ S : Finset Γ, (∀ γ : Γ, γ ∉ S → ρ + 1 < ‖(γ : ℂ) + x - c‖) ∧
      ∀ᶠ y in 𝓝 x, periodize Γ f y = ∑ γ ∈ S, f ((γ : ℂ) + y) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset Γ, ∀ γ : Γ, γ ∈ S ↔ ‖(γ : ℂ) + x - c‖ ≤ ρ + 1 :=
    ⟨(finite_lattice_translates Γ c x (ρ + 1)).toFinset, fun γ => by simp⟩
  refine ⟨S, fun γ hγ => not_le.1 fun h => hγ ((hS γ).2 h), ?_⟩
  filter_upwards [ball_mem_nhds x one_pos] with y hy
  unfold periodize
  refine tsum_eq_sum fun γ hγ => hsupp _ ?_
  have h1 : ρ + 1 < ‖(γ : ℂ) + x - c‖ := not_le.1 fun h => hγ ((hS γ).2 h)
  have h2 : ‖(γ : ℂ) + x - c‖ ≤ ‖(γ : ℂ) + y - c‖ + ‖y - x‖ := by
    have e : (γ : ℂ) + x - c = ((γ : ℂ) + y - c) + (x - y) := by ring
    calc ‖(γ : ℂ) + x - c‖ = ‖((γ : ℂ) + y - c) + (x - y)‖ := by rw [← e]
      _ ≤ ‖(γ : ℂ) + y - c‖ + ‖x - y‖ := norm_add_le _ _
      _ = ‖(γ : ℂ) + y - c‖ + ‖y - x‖ := by rw [norm_sub_rev x y]
  have h3 : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
  linarith

omit [DiscreteTopology Γ] in
theorem periodize_add_period (f : ℂ → ℝ) {δ : ℂ} (hδ : δ ∈ Γ) (x : ℂ) :
    periodize Γ f (x + δ) = periodize Γ f x := by
  unfold periodize
  have := (Equiv.addRight (⟨δ, hδ⟩ : Γ)).tsum_eq (fun γ : Γ => f ((γ : ℂ) + x))
  rw [← this]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addRight]
  congr 1
  push_cast
  ring

theorem contDiffAt_periodize {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hf : ContDiff ℝ ∞ f)
    (hsupp : ∀ y, ρ < ‖y - c‖ → f y = 0) (x : ℂ) : ContDiffAt ℝ ∞ (periodize Γ f) x := by
  obtain ⟨S, -, hS⟩ := periodize_eventuallyEq_sum (Γ := Γ) hsupp x
  refine ContDiffAt.congr_of_eventuallyEq ?_ hS
  exact ContDiffAt.sum fun γ _ => (hf.comp (contDiff_const.add contDiff_id)).contDiffAt

theorem contDiff_periodize {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hf : ContDiff ℝ ∞ f)
    (hsupp : ∀ y, ρ < ‖y - c‖ → f y = 0) : ContDiff ℝ ∞ (periodize Γ f) :=
  contDiff_iff_contDiffAt.2 fun x => contDiffAt_periodize hf hsupp x

omit [DiscreteTopology Γ] in
theorem summable_translates [DiscreteTopology Γ] {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ}
    (hsupp : ∀ y, ρ < ‖y - c‖ → f y = 0) (x : ℂ) :
    Summable (fun γ : Γ => f ((γ : ℂ) + x)) := by
  classical
  refine summable_of_ne_finset_zero (s := (finite_lattice_translates Γ c x ρ).toFinset) ?_
  intro γ hγ
  refine hsupp _ ?_
  by_contra hlt
  exact hγ (by simpa using not_lt.1 hlt)

/-- Far from `c`, the derivative of a function supported in `closedBall c ρ` vanishes. -/
theorem fderiv_eq_zero_of_far {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hsupp : ∀ y, ρ < ‖y - c‖ → f y = 0)
    {y : ℂ} (hy : ρ < ‖y - c‖) (v : ℂ) : fderiv ℝ f y v = 0 := by
  have hev : f =ᶠ[𝓝 y] fun _ => 0 := by
    have hopen : IsOpen {z : ℂ | ρ < ‖z - c‖} := isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact hsupp z hz
  rw [hev.fderiv_eq]; simp


/-- The derivative of the periodization is the periodization of the derivative. -/
theorem fderiv_periodize {f : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hf : ContDiff ℝ ∞ f)
    (hsupp : ∀ y, ρ < ‖y - c‖ → f y = 0) (x v : ℂ) :
    fderiv ℝ (periodize Γ f) x v = ∑' γ : Γ, fderiv ℝ f ((γ : ℂ) + x) v := by
  classical
  obtain ⟨S, hSout, hS⟩ := periodize_eventuallyEq_sum (Γ := Γ) hsupp x
  have h1 : fderiv ℝ (periodize Γ f) x = fderiv ℝ (fun y => ∑ γ ∈ S, f ((γ : ℂ) + y)) x :=
    Filter.EventuallyEq.fderiv_eq hS
  have hd : ∀ γ : Γ, fderiv ℝ (fun y => f ((γ : ℂ) + y)) x = fderiv ℝ f ((γ : ℂ) + x) := fun γ =>
    fderiv_comp_add_left (γ : ℂ)
  have hdiff : ∀ γ ∈ S, DifferentiableAt ℝ (fun y => f ((γ : ℂ) + y)) x := fun γ _ =>
    ((hf.differentiable (by simp)).comp (differentiable_const _ |>.add differentiable_id)) x
  rw [h1, fderiv_fun_sum hdiff]
  simp only [hd, sum_apply]
  symm
  refine tsum_eq_sum fun γ hγ => ?_
  have hout := hSout γ hγ
  have hev : f =ᶠ[𝓝 ((γ : ℂ) + x)] fun _ => 0 := by
    have hopen : IsOpen {y : ℂ | ρ < ‖y - c‖} := isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds (show ρ < ‖(γ : ℂ) + x - c‖ by linarith)] with y hy
    exact hsupp y hy
  rw [hev.fderiv_eq]
  simp

/-- **Unfolding for the periodization.** -/
theorem integral_periodize_mul [IsZLattice ℝ Γ] {f F : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x) (hint : Integrable (fun y => f y * F y) volume) :
    ∫ x in torusDomain Γ, periodize Γ f x * F x = ∫ y, f y * F y := by
  have h : ∀ x, periodize Γ f x * F x = ∑' γ : Γ, (f ((γ : ℂ) + x) * F ((γ : ℂ) + x)) := by
    intro x
    unfold periodize
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    rw [add_comm (γ : ℂ) x, hper γ γ.2 x]
  simp_rw [h]
  rw [integral_torusDomain_tsum Γ hint]

/-- The periodization of an integrable function times a periodic measurable function is integrable
over the fundamental domain. -/
theorem integrableOn_periodize_mul [IsZLattice ℝ Γ] {f F : ℂ → ℝ}
    (hfc : Continuous (periodize Γ f)) (hFm : AEStronglyMeasurable F volume)
    (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x) (hint : Integrable (fun y => f y * F y) volume) :
    IntegrableOn (fun x => periodize Γ f x * F x) (torusDomain Γ) := by
  have hD := (torusDomain_spec Γ).1
  have h : ∀ x, periodize Γ f x * F x = ∑' γ : Γ, (f ((γ : ℂ) + x) * F ((γ : ℂ) + x)) := by
    intro x
    unfold periodize
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    rw [add_comm (γ : ℂ) x, hper γ γ.2 x]
  have hmp : ∀ γ : Γ, MeasurePreserving (fun x : ℂ => (γ : ℂ) + x) volume volume := fun γ =>
    measurePreserving_add_left volume (γ : ℂ)
  refine ⟨(hfc.aestronglyMeasurable.mul hFm).mono_measure Measure.restrict_le_self, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [h]
  calc ∫⁻ x in torusDomain Γ, ‖∑' γ : Γ, (f ((γ : ℂ) + x) * F ((γ : ℂ) + x))‖ₑ
      ≤ ∫⁻ x in torusDomain Γ, ∑' γ : Γ, ‖f ((γ : ℂ) + x) * F ((γ : ℂ) + x)‖ₑ :=
        lintegral_mono fun x => enorm_tsum_le_tsum_enorm
    _ = ∑' γ : Γ, ∫⁻ x in torusDomain Γ, ‖f ((γ : ℂ) + x) * F ((γ : ℂ) + x)‖ₑ := by
        rw [lintegral_tsum]
        intro γ
        exact ((hint.1.comp_measurePreserving (hmp γ)).enorm).mono_measure Measure.restrict_le_self
    _ = ∫⁻ y, ‖f y * F y‖ₑ := (hD.lintegral_eq_tsum'' (fun y => ‖f y * F y‖ₑ)).symm
    _ < ⊤ := hint.2

end Torus

end SandierSerfaty

end
