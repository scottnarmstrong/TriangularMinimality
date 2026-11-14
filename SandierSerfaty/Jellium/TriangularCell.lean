/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TriangularLocal
public import SandierSerfaty.Geometry.LatticeAverage
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The cell integral of the truncated field

For a lattice `Γ` whose nonzero points have norm `≥ 1`, a torus potential `h` of the charge at `0`, and
the smooth part `v` of `h = v - log ‖·‖` near `0` (`IsLocalPart h v`), with `η = ¼` and the
truncated field `G = ‖E_η‖²` (`SandierSerfaty.Torus.tField`), for a fundamental domain `F`
of `Γ`:

* `∫⁻_F G = ∫⁻_{B(0,η)} ‖∇v‖² + ∫⁻_F 1_{far η} ‖∇h‖²`  (`lintegral_cell`);
* for `0 < ε < η`, `∫⁻_F 1_{far ε} ‖∇h‖² = ∫⁻_F 1_{far η} ‖∇h‖² + ∫⁻_{ε ≤ ‖x‖ < η} ‖∇h‖²`.

where `far ε = {x | ∀ γ ∈ Γ, ε ≤ ‖x - γ‖}`. Both rest on unfolding a periodized function over the
fundamental domain (`lintegral_periodize`).
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Torus

/-- `v` is a smooth extension of `h + log ‖·‖` to the unit ball, with `Δ v = 2π`. -/
@[expose] def IsLocalPart (h v : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ v (ball 0 1) ∧ (∀ x ∈ ball (0 : ℂ) 1, Δ v x = 2 * Real.pi) ∧
    ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → h x = v x - Real.log ‖x‖

/-- The set of points at distance `≥ ε` from the lattice. -/
@[expose] def farSet (Γ : Submodule ℤ ℂ) (ε : ℝ) : Set ℂ := {x | ∀ γ ∈ Γ, ε ≤ ‖x - γ‖}

/-! ### Unfolding a periodized function -/

section Periodize

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem lintegral_periodize {F : Set ℂ} (hF : IsAddFundamentalDomain Γ F volume)
    {ψ : ℂ → ℝ≥0∞} (hψ : Measurable ψ) :
    ∫⁻ x in F, ∑' g : Γ, ψ ((g : ℂ) + x) = ∫⁻ x, ψ x := by
  have hmeas : ∀ g : Γ, AEMeasurable (fun x : ℂ => ψ ((g : ℂ) + x)) (volume.restrict F) :=
    fun g => (hψ.comp (measurable_const.add measurable_id)).aemeasurable
  rw [hF.lintegral_eq_tsum'' ψ]
  exact lintegral_tsum hmeas

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem tsum_indicator_eq_of_mem (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {B : Set ℂ}
    (hB : B ⊆ ball 0 (1 / 2)) (Q : ℂ → ℝ≥0∞) {x : ℂ} {g0 : Γ} (h0 : (g0 : ℂ) + x ∈ B) :
    ∑' g : Γ, B.indicator Q ((g : ℂ) + x) = Q ((g0 : ℂ) + x) := by
  rw [tsum_eq_single g0]
  · rw [indicator_of_mem h0]
  · intro g hg
    refine indicator_of_notMem (fun hgB => hg ?_) _
    have h1 : ‖((g : ℂ) + x) - ((g0 : ℂ) + x)‖ < 1 := by
      have a1 := mem_ball_zero_iff.1 (hB hgB)
      have a2 := mem_ball_zero_iff.1 (hB h0)
      calc ‖((g : ℂ) + x) - ((g0 : ℂ) + x)‖ ≤ ‖(g : ℂ) + x‖ + ‖(g0 : ℂ) + x‖ := norm_sub_le _ _
        _ < 1 := by linarith
    have h2 : ((g : ℂ) + x) - ((g0 : ℂ) + x) = (g : ℂ) - g0 := by ring
    rw [h2] at h1
    by_contra hne
    have hne' : (g : ℂ) - g0 ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    have := hmin _ (Γ.sub_mem g.2 g0.2) hne'
    linarith

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem tsum_indicator_eq_zero {B : Set ℂ} (Q : ℂ → ℝ≥0∞) {x : ℂ}
    (h0 : ∀ g : Γ, (g : ℂ) + x ∉ B) : ∑' g : Γ, B.indicator Q ((g : ℂ) + x) = 0 := by
  simp [indicator_of_notMem (h0 _)]

end Periodize

/-! ### The squared gradient as an `ℝ≥0∞`-valued function -/

/-- `x ↦ ‖∇f x‖²` as an extended nonnegative real. -/
@[expose] noncomputable def cellGradSq (f : ℂ → ℝ) (x : ℂ) : ℝ≥0∞ := ENNReal.ofReal (‖gradient f x‖ ^ 2)

theorem measurable_gradient (f : ℂ → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem measurable_cellGradSq (f : ℂ → ℝ) : Measurable (cellGradSq f) :=
  ((measurable_gradient f).norm.pow_const 2).ennreal_ofReal

theorem cellGradSq_add_periodic {Γ : Submodule ℤ ℂ} {h : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    cellGradSq h (x + γ) = cellGradSq h x := by
  simp only [cellGradSq, gradient_add_periodic hper hγ x]

/-! ### Pointwise decomposition -/

section Decomposition

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- The exceptional null set: the lattice and the circles of radius `¼` around its points. -/
@[expose] def badSet (Γ : Submodule ℤ ℂ) : Set ℂ :=
  (Γ : Set ℂ) ∪ ⋃ γ ∈ (Γ : Set ℂ), sphere γ (1 / 4)

theorem volume_badSet : volume (badSet Γ) = 0 := by
  have hc0 : Countable (Γ : Set ℂ) := inferInstanceAs (Countable Γ)
  have hc : (Γ : Set ℂ).Countable := Set.countable_coe_iff.1 hc0
  refine measure_union_null (hc.measure_zero _) ?_
  exact (measure_biUnion_null_iff hc).2 fun γ _ => Measure.addHaar_sphere volume γ _

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem eq_of_norm_lt {x γ γ' : ℂ} (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ)
    (h1 : ‖x - γ‖ < 1 / 2) (h2 : ‖x - γ'‖ < 1 / 2) : γ = γ' := by
  by_contra hne
  have := hmin (γ - γ') (Γ.sub_mem hγ hγ') (sub_ne_zero.2 hne)
  have h3 : ‖γ - γ'‖ ≤ ‖x - γ‖ + ‖x - γ'‖ := by
    calc ‖γ - γ'‖ = ‖(x - γ') - (x - γ)‖ := by congr 1; ring
      _ ≤ ‖x - γ'‖ + ‖x - γ‖ := norm_sub_le _ _
      _ = ‖x - γ‖ + ‖x - γ'‖ := add_comm _ _
  linarith

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
/-- **Pointwise decomposition of the squared truncated field.** Off a null set,
`‖E_η‖² = ∑_g 1_{B(0,η)}(g + x) ‖∇v(g + x)‖² + 1_{far η}(x) ‖∇h(x)‖²`. -/
theorem tField_decomp (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h v : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) (hv : IsLocalPart h v) {x : ℂ} (hx : x ∉ badSet Γ) :
    ENNReal.ofReal (‖tField Γ h x‖ ^ 2) =
      ∑' g : Γ, (ball (0 : ℂ) (1 / 4)).indicator (cellGradSq v) ((g : ℂ) + x) +
        (farSet Γ (1 / 4)).indicator (cellGradSq h) x := by
  have hB : ball (0 : ℂ) (1 / 4) ⊆ ball 0 (1 / 2) := ball_subset_ball (by norm_num)
  have hxΓ : x ∉ (Γ : Set ℂ) := fun hh => hx (Or.inl hh)
  have hxS : ∀ γ ∈ Γ, ‖x - γ‖ ≠ 1 / 4 := fun γ hγ hh =>
    hx (Or.inr (mem_biUnion hγ (by simpa [mem_sphere, dist_eq_norm] using hh)))
  by_cases hnear : ∃ g : Γ, ‖(g : ℂ) + x‖ < 1 / 4
  · obtain ⟨g0, hg0⟩ := hnear
    have hmem : (g0 : ℂ) + x ∈ ball (0 : ℂ) (1 / 4) := by simpa using hg0
    rw [tsum_indicator_eq_of_mem hmin hB _ hmem]
    have hfar : x ∉ farSet Γ (1 / 4) := by
      intro hf
      have := hf (-(g0 : ℂ)) (Γ.neg_mem g0.2)
      have e : x - -(g0 : ℂ) = (g0 : ℂ) + x := by ring
      rw [e] at this
      linarith
    rw [indicator_of_notMem hfar, add_zero]
    have hy0 : (g0 : ℂ) + x ≠ 0 := by
      intro hy
      apply hxΓ
      have : x = -(g0 : ℂ) := by linear_combination hy
      rw [this]; exact Γ.neg_mem g0.2
    have h1 := tField_add hper g0.2 x
    have h2 := tField_eq_gradient hmin hv.1 hv.2.2 hy0 (by simpa using hg0)
    rw [add_comm] at h1
    rw [← h1, h2]
    rfl
  · push Not at hnear
    rw [tsum_indicator_eq_zero _ (fun g => by simpa using hnear g), zero_add]
    have hfar' : ∀ γ ∈ Γ, (1 / 4 : ℝ) < ‖x - γ‖ := by
      intro γ hγ
      have h1 := hnear ⟨-γ, Γ.neg_mem hγ⟩
      have e : ((-γ : ℂ)) + x = x - γ := by ring
      simp only [e] at h1
      exact lt_of_le_of_ne h1 (hxS γ hγ).symm
    have hfar : x ∈ farSet Γ (1 / 4) := fun γ hγ => (hfar' γ hγ).le
    rw [indicator_of_mem hfar, tField_of_far hfar']
    rfl

end Decomposition

/-! ### The cell integral -/

section CellIntegral

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem isClosed_farSet (Γ : Submodule ℤ ℂ) (ε : ℝ) : IsClosed (farSet Γ ε) := by
  have : farSet Γ ε = ⋂ γ ∈ (Γ : Set ℂ), {x : ℂ | ε ≤ ‖x - γ‖} := by
    ext x; simp [farSet]
  rw [this]
  exact isClosed_biInter fun γ _ =>
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))

theorem measurableSet_farSet (Γ : Submodule ℤ ℂ) (ε : ℝ) : MeasurableSet (farSet Γ ε) :=
  (isClosed_farSet Γ ε).measurableSet

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem farSet_add_periodic {ε : ℝ} {x γ : ℂ} (hγ : γ ∈ Γ) :
    x + γ ∈ farSet Γ ε ↔ x ∈ farSet Γ ε := by
  constructor
  · intro h γ' hγ'
    have := h (γ + γ') (Γ.add_mem hγ hγ')
    have e : x + γ - (γ + γ') = x - γ' := by ring
    rwa [e] at this
  · intro h γ' hγ'
    have := h (γ' - γ) (Γ.sub_mem hγ' hγ)
    have e : x - (γ' - γ) = x + γ - γ' := by ring
    rwa [e] at this

/-- **`∫⁻_F ‖E_η‖²`** splits into the near part (a ball integral of `‖∇v‖²`) and the far part. -/
theorem lintegral_cell (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h v : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) (hv : IsLocalPart h v) {F : Set ℂ}
    (hF : IsAddFundamentalDomain Γ F volume) :
    ∫⁻ x in F, ENNReal.ofReal (‖tField Γ h x‖ ^ 2) =
      (∫⁻ y in ball (0 : ℂ) (1 / 4), cellGradSq v y) +
        ∫⁻ x in F, (farSet Γ (1 / 4)).indicator (cellGradSq h) x := by
  have hψ : Measurable ((ball (0 : ℂ) (1 / 4)).indicator (cellGradSq v)) :=
    (measurable_cellGradSq v).indicator measurableSet_ball
  have hΨ : Measurable fun x : ℂ => ∑' g : Γ, (ball (0 : ℂ) (1 / 4)).indicator (cellGradSq v)
      ((g : ℂ) + x) :=
    Measurable.tsum fun g => hψ.comp (measurable_const.add measurable_id)
  have hae : ∀ᵐ x ∂(volume.restrict F), ENNReal.ofReal (‖tField Γ h x‖ ^ 2) =
      ∑' g : Γ, (ball (0 : ℂ) (1 / 4)).indicator (cellGradSq v) ((g : ℂ) + x) +
        (farSet Γ (1 / 4)).indicator (cellGradSq h) x :=
    ae_restrict_of_ae ((measure_eq_zero_iff_ae_notMem.1 volume_badSet).mono fun x hx =>
      tField_decomp hmin hper hv hx)
  rw [lintegral_congr_ae hae, lintegral_add_left hΨ, lintegral_periodize hF hψ,
    lintegral_indicator measurableSet_ball]

/-- Splitting the far part: the points at distance in `[ε, η)` from the lattice. -/
theorem lintegral_far_split (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) {F : Set ℂ} (hF : IsAddFundamentalDomain Γ F volume)
    {ε : ℝ} (hε : 0 < ε) (hεη : ε ≤ 1 / 4) :
    ∫⁻ x in F, (farSet Γ ε).indicator (cellGradSq h) x =
      (∫⁻ x in F, (farSet Γ (1 / 4)).indicator (cellGradSq h) x) +
        ∫⁻ y in {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4}, cellGradSq h y := by
  set A : Set ℂ := {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hAB : A ⊆ ball 0 (1 / 2) := fun y hy => by
    rw [mem_ball_zero_iff]; linarith [hy.2]
  have hψ : Measurable (A.indicator (cellGradSq h)) := (measurable_cellGradSq h).indicator hAm
  have hΨ : Measurable fun x : ℂ => ∑' g : Γ, A.indicator (cellGradSq h) ((g : ℂ) + x) :=
    Measurable.tsum fun g => hψ.comp (measurable_const.add measurable_id)
  have hpt : ∀ x : ℂ, (farSet Γ ε).indicator (cellGradSq h) x =
      (farSet Γ (1 / 4)).indicator (cellGradSq h) x + ∑' g : Γ, A.indicator (cellGradSq h) ((g : ℂ) + x) := by
    intro x
    by_cases hnear : ∃ g : Γ, (g : ℂ) + x ∈ A
    · obtain ⟨g0, hg0⟩ := hnear
      rw [tsum_indicator_eq_of_mem hmin hAB _ hg0]
      have hfarη : x ∉ farSet Γ (1 / 4) := by
        intro hf
        have := hf (-(g0 : ℂ)) (Γ.neg_mem g0.2)
        have e : x - -(g0 : ℂ) = (g0 : ℂ) + x := by ring
        rw [e] at this
        linarith [hg0.2]
      have hfarε : x ∈ farSet Γ ε := by
        intro γ hγ
        by_contra hlt
        push Not at hlt
        have := eq_of_norm_lt (x := x) (γ := γ) (γ' := -(g0 : ℂ)) hmin hγ (Γ.neg_mem g0.2)
          (by linarith) (by
            have e : x - -(g0 : ℂ) = (g0 : ℂ) + x := by ring
            rw [e]; linarith [hg0.2])
        have e : x - -(g0 : ℂ) = (g0 : ℂ) + x := by ring
        rw [this, e] at hlt
        linarith [hg0.1]
      rw [indicator_of_notMem hfarη, indicator_of_mem hfarε, zero_add]
      have := cellGradSq_add_periodic hper g0.2 x
      rw [add_comm] at this
      exact this.symm
    · push Not at hnear
      rw [tsum_indicator_eq_zero _ hnear, add_zero]
      by_cases hfarη : x ∈ farSet Γ (1 / 4)
      · rw [indicator_of_mem hfarη, indicator_of_mem]
        intro γ hγ
        exact hεη.trans (hfarη γ hγ)
      · have hfarε : x ∉ farSet Γ ε := by
          intro hf
          apply hfarη
          intro γ hγ
          by_contra hlt
          push Not at hlt
          apply hnear ⟨-γ, Γ.neg_mem hγ⟩
          have e : ((-γ : ℂ)) + x = x - γ := by ring
          show ((-γ : ℂ)) + x ∈ A
          rw [e]
          exact ⟨hf γ hγ, hlt⟩
        rw [indicator_of_notMem hfarη, indicator_of_notMem hfarε]
  have : ∫⁻ x in F, (farSet Γ ε).indicator (cellGradSq h) x =
      ∫⁻ x in F, ((farSet Γ (1 / 4)).indicator (cellGradSq h) x +
        ∑' g : Γ, A.indicator (cellGradSq h) ((g : ℂ) + x)) := lintegral_congr hpt
  rw [this, lintegral_add_right _ hΨ, lintegral_periodize hF hψ, lintegral_indicator hAm]

end CellIntegral

end Torus

end SandierSerfaty

end
