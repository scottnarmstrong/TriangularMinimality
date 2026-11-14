/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
public import SandierSerfaty.Torus.ChargeSet
public import SandierSerfaty.Torus.Lattice
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Integrability of the torus potential

A function `h` satisfying `SandierSerfaty.IsTorusPotential` is integrable over the fundamental domain
`torusDomain Γ`: it is continuous off the (countable, closed) charge set, bounded by `C / ‖· - x‖`
near each charge `x` (as `h + log‖· - x‖` has a finite limit and `|log t| ≤ 1 / t` for `t ≤ 1`),
hence locally integrable on `ℂ`; periodicity transports the integrability from a bounded fundamental
domain to `torusDomain Γ`.

This shows that the mean-zero clause of `IsTorusPotential` is not vacuous.
-/

open MeasureTheory Filter Topology Metric Set

public section

namespace SandierSerfaty

namespace Torus

/-- `|log t| ≤ 1 / t` for `0 < t ≤ 1`. -/
theorem abs_log_le_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : |Real.log t| ≤ t⁻¹ := by
  rw [abs_of_nonpos (Real.log_nonpos ht.le ht1), ← Real.log_inv]
  have := Real.log_le_sub_one_of_pos (inv_pos.2 ht)
  linarith

/-- A measurable function with `|h y + log‖y - x‖| ≤ c` near `x` is integrable near `x`. -/
theorem integrableAtFilter_of_log_bound {h : ℂ → ℝ} {x : ℂ} {c : ℝ}
    (hmeas : AEStronglyMeasurable h volume)
    (hbound : ∀ᶠ y in 𝓝[≠] x, |h y + Real.log ‖y - x‖| ≤ c) :
    IntegrableAtFilter h (𝓝 x) volume := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 hbound
  set r : ℝ := min ε 1 with hr
  have hr0 : 0 < r := lt_min hε one_pos
  refine ⟨ball x r, ball_mem_nhds x hr0, ?_⟩
  have hmp : MeasurePreserving (fun y : ℂ => x + y) volume volume := measurePreserving_add_left volume x
  have hf : IntegrableOn (fun y => h (x + y)) (ball 0 r) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := |c| + 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex]) ?_
      (hmeas.comp_measurePreserving hmp)
    filter_upwards [ae_restrict_of_ae ((Set.countable_singleton (0 : ℂ)).ae_notMem volume),
      ae_restrict_mem measurableSet_ball] with y hy0 hyb
    have hy0' : y ≠ 0 := hy0
    have ht0 : 0 < ‖y‖ := norm_pos_iff.2 hy0'
    have ht1 : ‖y‖ < r := by simpa using hyb
    have hmem : x + y ∈ ball x ε ∩ {x}ᶜ := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left]
        exact ht1.trans_le (min_le_left _ _)
      · intro h'
        exact hy0' (by simpa using h')
    have hb := hεs hmem
    simp only [mem_ofPred_eq, add_sub_cancel_left] at hb
    have hlog := abs_log_le_inv ht0 (ht1.le.trans (min_le_right _ _))
    rw [Real.rpow_neg_one, Real.norm_eq_abs]
    have h1 : |h (x + y)| ≤ |c| + ‖y‖⁻¹ := by
      calc |h (x + y)| = |(h (x + y) + Real.log ‖y‖) - Real.log ‖y‖| := by ring_nf
        _ ≤ |h (x + y) + Real.log ‖y‖| + |Real.log ‖y‖| := abs_sub _ _
        _ ≤ |c| + ‖y‖⁻¹ := add_le_add (hb.trans (le_abs_self c)) hlog
    have h2 : |c| ≤ |c| * ‖y‖⁻¹ := by
      have : 1 ≤ ‖y‖⁻¹ := one_le_inv_iff₀.2 ⟨ht0, (ht1.le.trans (min_le_right _ _))⟩
      nlinarith [abs_nonneg c]
    calc |h (x + y)| ≤ |c| + ‖y‖⁻¹ := h1
      _ ≤ (|c| + 1) * ‖y‖⁻¹ := by nlinarith
  have hpre : (fun y : ℂ => x + y) ⁻¹' ball x r = ball 0 r := by
    ext y; simp [mem_ball, dist_eq_norm]
  have := (hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft x)
    (f := h) (s := ball x r)).1 (by rw [hpre]; exact hf)
  exact this

end Torus

/-- The limit of `h + log‖· - x‖` at a point `x` of the charge set. -/
theorem IsTorusPotential.exists_tendsto_of_mem_chargeSet {Γ : Submodule ℤ ℂ} {N : ℕ}
    {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {x : ℂ}
    (hx : x ∈ Torus.chargeSet Γ a) :
    ∃ c : ℝ, Tendsto (fun y => h y + Real.log ‖y - x‖) (𝓝[≠] x) (𝓝 c) := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨c, hc⟩ := hP.2.2.2.1 i
  refine ⟨c, ?_⟩
  set γ : ℂ := x - a i with hγ
  have hmap : Tendsto (fun y : ℂ => y - γ) (𝓝[≠] x) (𝓝[≠] (a i)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℂ => y - γ) (𝓝 x) (𝓝 (x - γ)) := (continuous_id.sub continuous_const).tendsto x
      have e : x - γ = a i := by rw [hγ]; ring
      rw [e] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro h'
      have h'' : y - γ = a i := h'
      rw [hγ] at h''
      exact hy (show y = x by linear_combination h'')
  refine (hc.comp hmap).congr' ?_
  filter_upwards with y
  simp only [Function.comp]
  have e1 : h (y - γ) = h y := by
    have := hP.1 γ hi (y - γ)
    rw [sub_add_cancel] at this
    exact this.symm
  have e2 : y - γ - a i = y - x := by rw [hγ]; ring
  rw [e1, e2]

/-- A torus potential is almost everywhere strongly measurable. -/
theorem IsTorusPotential.aestronglyMeasurable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) :
    AEStronglyMeasurable h volume := by
  have hPo : IsOpen (Torus.chargeSet Γ a)ᶜ := (Torus.isClosed_chargeSet Γ a).isOpen_compl
  have hPo' : IsOpen {x : ℂ | ∀ i, x - a i ∉ Γ} := by
    have : {x : ℂ | ∀ i, x - a i ∉ Γ} = (Torus.chargeSet Γ a)ᶜ := by
      ext x; exact Torus.notMem_chargeSet_iff.symm
    rw [this]; exact hPo
  have h1 : AEStronglyMeasurable h (volume.restrict {x : ℂ | ∀ i, x - a i ∉ Γ}) :=
    hP.2.1.continuousOn.aestronglyMeasurable hPo'.measurableSet
  have hae : ∀ᵐ x ∂(volume : Measure ℂ), x ∈ {x : ℂ | ∀ i, x - a i ∉ Γ} := by
    filter_upwards [(Torus.countable_chargeSet Γ a).ae_notMem volume] with x hx
    exact Torus.notMem_chargeSet_iff.1 hx
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

/-- A torus potential is locally integrable. -/
theorem IsTorusPotential.locallyIntegrable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) :
    LocallyIntegrable h volume := by
  have hPo' : IsOpen {x : ℂ | ∀ i, x - a i ∉ Γ} := by
    have : {x : ℂ | ∀ i, x - a i ∉ Γ} = (Torus.chargeSet Γ a)ᶜ := by
      ext x; exact Torus.notMem_chargeSet_iff.symm
    rw [this]; exact (Torus.isClosed_chargeSet Γ a).isOpen_compl
  intro x
  by_cases hx : x ∈ Torus.chargeSet Γ a
  · obtain ⟨c, hc⟩ := hP.exists_tendsto_of_mem_chargeSet hx
    refine Torus.integrableAtFilter_of_log_bound (c := ‖c‖ + 1) hP.aestronglyMeasurable ?_
    have := (hc.norm).eventually (eventually_lt_nhds (a := ‖c‖) (b := ‖c‖ + 1) (by linarith))
    filter_upwards [this] with y hy
    exact hy.le
  · have hx' : x ∈ {x : ℂ | ∀ i, x - a i ∉ Γ} := Torus.notMem_chargeSet_iff.1 hx
    have := (hP.2.1.continuousOn.locallyIntegrableOn (μ := volume) hPo'.measurableSet) x hx'
    rwa [hPo'.nhdsWithin_eq hx'] at this

/-- **A torus potential is integrable over the fundamental domain `torusDomain Γ`.** -/
theorem IsTorusPotential.integrableOn_torusDomain {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) :
    IntegrableOn h (torusDomain Γ) := by
  have := ZLattice.module_free ℝ Γ
  have := ZLattice.module_finite ℝ Γ
  set b := Module.Free.chooseBasis ℤ Γ with hb
  have hfdD := ZLattice.isAddFundamentalDomain b (volume : Measure ℂ)
  have hbd : Bornology.IsBounded (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    ZSpan.fundamentalDomain_isBounded _
  have hDint : IntegrableOn h (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) :=
    (hP.locallyIntegrable.integrableOn_isCompact hbd.isCompact_closure).mono_set subset_closure
  have hper : ∀ (g : Γ) (x : ℂ), h (g +ᵥ x) = h x := fun g x => by
    have : g +ᵥ x = (g : ℂ) + x := rfl
    rw [this, add_comm]; exact hP.1 g g.2 x
  exact (hfdD.integrableOn_iff (torusDomain_spec Γ).1 hper).1 hDint

end SandierSerfaty

end
