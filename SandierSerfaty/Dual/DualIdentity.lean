/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.IdentityAux
public import SandierSerfaty.Dual.Pairing
public import SandierSerfaty.Torus.PairEnergyIdentity

/-!
# The dual identity: limits and the pieces of the proof

For `0 < η` small and `cut η f = 1_{(punctureSet η)ᶜ} f`, with `u = greenSum`, `H = gluedH`,
`w = wExt = u - H`:
```
∫_D cut η |∇u|² = 2 ∫_D cut η ⟨∇w, ∇u⟩ - ∫_D cut η |∇w|² + ∫_D cut η |∇H|²
```
(`integral_energyDensity_eq`, from the pointwise identity `gradSq_decomp` on every open sector and the sector sum),
and each term has an `η ↓ 0` limit (`tendsto_integral_cut`, `tendsto_sector_sum`).
The final assembly is in `SandierSerfaty.Dual.DualIdentityMain`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis Torus

variable {ι : Type*} {R : RadialData ι} {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]
  {N : ℕ} {a : Fin N → ℂ} {d₀ : ℝ}

/-- The cut-off `1_{(punctureSet η)ᶜ} f`. -/
@[expose] noncomputable def cut (Γ : Submodule ℤ ℂ) (a : Fin N → ℂ) (η : ℝ) (f : ℂ → ℝ) : ℂ → ℝ :=
  (punctureSet Γ a η)ᶜ.indicator f

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem cut_periodic {f : ℂ → ℝ} (hf : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) (η : ℝ) :
    ∀ γ ∈ Γ, ∀ x, cut Γ a η f (x + γ) = cut Γ a η f x := by
  intro γ hγ x
  by_cases hx : x ∈ punctureSet Γ a η
  · have : x + γ ∈ punctureSet Γ a η := (punctureSet_add_period hγ x).2 hx
    simp [cut, hx, this]
  · have : x + γ ∉ punctureSet Γ a η := fun h => hx ((punctureSet_add_period hγ x).1 h)
    simp [cut, hx, this, hf γ hγ x]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem gradSq_periodic' {F : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x) :
    ∀ γ ∈ Γ, ∀ x, gradSq F (x + γ) = gradSq F x := by
  intro γ hγ x
  simp only [gradSq, pd₁, pd₂, fderiv_periodic Γ hper hγ x]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem gradDot_periodic {F G : ℂ → ℝ} (hF : ∀ γ ∈ Γ, ∀ x, F (x + γ) = F x)
    (hG : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x) :
    ∀ γ ∈ Γ, ∀ x, gradDot F G (x + γ) = gradDot F G x := by
  intro γ hγ x
  simp only [gradDot, pd₁, pd₂, fderiv_periodic Γ hF hγ x, fderiv_periodic Γ hG hγ x]

omit [IsZLattice ℝ Γ] in
theorem eventually_notMem_punctureSet {x : ℂ} (hx : x ∉ chargeSet Γ a) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), x ∉ punctureSet Γ a η := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_chargeSet Γ a).isOpen_compl x hx
  filter_upwards [Ioo_mem_nhdsGT hε] with η hη hxη
  obtain ⟨i, γ, hγ, hlt⟩ := mem_punctureSet.1 hxη
  have hc : a i + γ ∈ chargeSet Γ a := add_mem_chargeSet' hγ
  have : a i + γ ∈ ball x ε := by
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact lt_trans hlt hη.2
  exact hball this hc

omit [IsZLattice ℝ Γ] [DiscreteTopology Γ] in
theorem mem_chargeSet_of_mem_punctureSet {η : ℝ} (hη : 0 < η) {x : ℂ} (hx : x ∈ chargeSet Γ a) :
    x ∈ punctureSet Γ a η := by
  obtain ⟨i, hi⟩ := hx
  exact mem_punctureSet.2 ⟨i, x - a i, hi, by simpa using hη⟩

/-- **The cut-off integrals converge.** -/
theorem tendsto_integral_cut {f : ℂ → ℝ} (hf : IntegrableOn f (torusDomain Γ)) :
    Tendsto (fun η : ℝ => ∫ x in torusDomain Γ, cut Γ a η f x) (𝓝[>] 0)
      (𝓝 (∫ x in torusDomain Γ, f x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun η =>
      hf.aestronglyMeasurable.indicator (isOpen_punctureSet η).isClosed_compl.measurableSet
  · refine Eventually.of_forall fun η => Eventually.of_forall fun x => ?_
    exact norm_indicator_le_norm_self _ _
  · filter_upwards [ae_restrict_of_ae ((countable_chargeSet Γ a).ae_notMem volume)] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_notMem_punctureSet hx] with η hη
    simp [cut, hη]

/-- The truncated energy density of `u = greenSum` is integrable on the cell. -/
theorem integrableOn_energyDensity (hΓ : ZLattice.covolume Γ = N)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), IntegrableOn (energyDensity Γ a η) (torusDomain Γ) := by
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep Γ a
  have hPD : PairData Γ a ρ := ⟨hΓ, ha, hsep, hρ⟩
  filter_upwards [Ioc_mem_nhdsGT hρ] with η hη
  exact (hPD.integrableOn_oneSubB_gradSq.add (hPD.integrableOn_B_mul_density hη.1 hη.2)).congr
    (Eventually.of_forall fun x => (hPD.energyDensity_decomp hη.2 x).symm)

theorem gradSq_nonneg' (u : ℂ → ℝ) (x : ℂ) : 0 ≤ gradSq u x := by
  unfold gradSq; positivity

theorem gradSq_H_le {x : ℂ}
    (hx : x ∉ chargeSet Γ a) :
    gradSq (gluedH R (periodicSites Γ a)) x ≤
      2 * gradSq (greenSum Γ a) x + 2 * gradSq (wExt R Γ a) x := by
  have hu : DifferentiableAt ℝ (greenSum Γ a) x := (contDiffAt_greenSum hx).differentiableAt (by simp)
  by_cases hH : DifferentiableAt ℝ (gluedH R (periodicSites Γ a)) x
  · have hw : fderiv ℝ (wExt R Γ a) x =
        fderiv ℝ (greenSum Γ a) x - fderiv ℝ (gluedH R (periodicSites Γ a)) x := by
      rw [(eventuallyEq_wExt hx).fderiv_eq]; exact fderiv_sub hu hH
    have hH' : fderiv ℝ (gluedH R (periodicSites Γ a)) x =
        fderiv ℝ (greenSum Γ a) x - fderiv ℝ (wExt R Γ a) x := by rw [hw]; abel
    simp only [gradSq, pd₁, pd₂, hH', sub_apply]
    nlinarith [sq_nonneg (fderiv ℝ (greenSum Γ a) x 1 + fderiv ℝ (wExt R Γ a) x 1),
      sq_nonneg (fderiv ℝ (greenSum Γ a) x Complex.I + fderiv ℝ (wExt R Γ a) x Complex.I)]
  · have h1 := gradSq_nonneg' (greenSum Γ a) x
    have h2 := gradSq_nonneg' (wExt R Γ a) x
    simp only [gradSq, pd₁, pd₂] at h1 h2 ⊢
    rw [fderiv_zero_of_not_differentiableAt hH]
    simp only [zero_apply]
    linarith

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem gradSq_wExt_le {K : NNReal} (hw : LipschitzWith K (wExt R Γ a)) (x : ℂ) :
    gradSq (wExt R Γ a) x ≤ 2 * (K : ℝ) ^ 2 := by
  have hK : ‖fderiv ℝ (wExt R Γ a) x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hw
  have h1 := (abs_fderiv_one_le (wExt R Γ a) x).trans hK
  have h2 := (abs_fderiv_I_le (wExt R Γ a) x).trans hK
  have h1' : pd₁ (wExt R Γ a) x ^ 2 ≤ (K : ℝ) ^ 2 := by
    have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2; simpa [pd₁] using this
  have h2' : pd₂ (wExt R Γ a) x ^ 2 ≤ (K : ℝ) ^ 2 := by
    have := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2; simpa [pd₂] using this
  unfold gradSq; linarith

theorem integrableOn_gradSq_wExt {K : NNReal} (hw : LipschitzWith K (wExt R Γ a)) :
    IntegrableOn (gradSq (wExt R Γ a)) (torusDomain Γ) := by
  refine Measure.integrableOn_of_bounded (volume_torusDomain_ne_top Γ)
    (Torus.measurable_gradSq _).aestronglyMeasurable (M := 2 * (K : ℝ) ^ 2) ?_
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (gradSq_nonneg' _ x)]
  exact gradSq_wExt_le hw x

/-- The truncated energy density of `H` is integrable on the cell. -/
theorem integrableOn_cut_gradSq_H (_hR : R.IsAdmissible d₀) (_hS : SepSites (periodicSites Γ a) d₀)
    {K : NNReal} (hw : LipschitzWith K (wExt R Γ a)) {η : ℝ} (hη : 0 < η)
    (hed : IntegrableOn (energyDensity Γ a η) (torusDomain Γ)) :
    IntegrableOn (cut Γ a η (gradSq (gluedH R (periodicSites Γ a)))) (torusDomain Γ) := by
  have hY := (integrableOn_gradSq_wExt (a := a) hw).indicator
    (isOpen_punctureSet (Γ := Γ) (a := a) η).isClosed_compl.measurableSet
  have hb := (hed.const_mul 2).add (hY.const_mul 2)
  refine Integrable.mono' hb ?_ ?_
  · exact ((Torus.measurable_gradSq _).indicator
      (isOpen_punctureSet (Γ := Γ) (a := a) η).isClosed_compl.measurableSet).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ punctureSet Γ a η
    · simp [cut, energyDensity, hx]
    · have hxc : x ∉ chargeSet Γ a := fun h => hx (mem_chargeSet_of_mem_punctureSet hη h)
      have := gradSq_H_le (R := R) hxc
      simp only [cut, energyDensity, hx, not_false_eq_true, indicator_of_mem, mem_compl_iff,
        Real.norm_eq_abs, abs_of_nonneg (gradSq_nonneg' _ x), Pi.add_apply]
      linarith

end Dual

end SandierSerfaty

end
