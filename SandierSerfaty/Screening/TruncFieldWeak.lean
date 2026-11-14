/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Defs
public import SandierSerfaty.Screening.TruncLogPairing
public import SandierSerfaty.Screening.Mollify

/-!
# The weak equation of a truncated field (smooth test functions)

Let `E` be a charge field of density `m` in `U` (`SandierSerfaty.IsChargeField`), `C` locally finite
and `α > 0` bounded on `C`. Then `E_α = truncField C α E` satisfies
`-div E_α = 2π (∑_{p ∈ C} δ_p^{(α_p)} - m)` weakly in `U` (comparison note, Lemma `lem:truncfield`(b)):
`integral_inner_truncField_of_contDiff`.

Bookkeeping for the locally finite sums: near a ball `B(0, R)` only the points of the finite set
`C ∩ B̄(0, R + M)` (`M ≥ sup α`) contribute (`truncField_eq_sum`, `finsum_mem_eq_finsetSum`);
`integrableOn_truncField`: `E_α` is integrable on compact subsets of `U`.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal ContDiff Real

public section

namespace SandierSerfaty

namespace Screening

/-! ### Locally finite sums -/

/-- A finite sum over `C` reduced to a finite subset carrying the support. -/
theorem finsum_mem_eq_finsetSum {β : Type*} [AddCommMonoid β] {C : Set ℂ} {S : Finset ℂ}
    (hS : (S : Set ℂ) ⊆ C) {g : ℂ → β} (hg : ∀ p ∈ C, p ∉ S → g p = 0) :
    ∑ᶠ p ∈ C, g p = ∑ p ∈ S, g p := by
  rw [← finsum_mem_coe_finset]
  apply finsum_mem_inter_support_eq
  ext p
  simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
  constructor
  · rintro ⟨hpC, hp⟩; exact ⟨by_contra fun h => hp (hg p hpC h), hp⟩
  · rintro ⟨hpS, hp⟩; exact ⟨hS hpS, hp⟩

theorem mem_of_mem_toFinset {C : Set ℂ} {r : ℝ} (h : (C ∩ closedBall 0 r).Finite) {p : ℂ}
    (hp : p ∈ h.toFinset) : p ∈ C :=
  ((Set.Finite.mem_toFinset h).1 hp).1

theorem lt_norm_of_notMem_toFinset {C : Set ℂ} {r : ℝ} (h : (C ∩ closedBall 0 r).Finite) {p : ℂ}
    (hpC : p ∈ C) (hp : p ∉ h.toFinset) : r < ‖p‖ := by
  by_contra h'
  exact hp ((Set.Finite.mem_toFinset h).2 ⟨hpC, mem_closedBall_zero_iff.2 (not_lt.1 h')⟩)

/-- Far points do not see `B̄(0, R)`. -/
theorem gradient_truncLog_far {r M R : ℝ} (hr : 0 < r) (hrM : r ≤ M) {x p : ℂ} (hx : ‖x‖ ≤ R)
    (hp : R + M < ‖p‖) : gradient (truncLog r) (x - p) = 0 := by
  refine gradient_truncLog_of_gt hr ?_
  have := norm_sub_norm_le p x
  rw [norm_sub_rev] at this
  linarith

/-- A function vanishing outside `B̄(0, R)` has zero average on the circles of far points. -/
theorem circleAverage_far {f : ℂ → ℝ} {R : ℝ} (hf : ∀ x, R < ‖x‖ → f x = 0) {r M : ℝ}
    (hr : 0 < r) (hrM : r ≤ M) {p : ℂ} (hp : R + M < ‖p‖) : Real.circleAverage f p r = 0 := by
  refine Real.circleAverage_const_on_circle fun x hx => hf x ?_
  rw [mem_sphere, dist_eq_norm, abs_of_pos hr] at hx
  have := norm_sub_norm_le p x
  rw [norm_sub_rev, hx] at this
  linarith

theorem eq_zero_of_tsupport_subset {f : ℂ → ℝ} {R : ℝ} (hR : tsupport f ⊆ closedBall 0 R) :
    ∀ x, R < ‖x‖ → f x = 0 := fun _x hx =>
  image_eq_zero_of_notMem_tsupport fun h => absurd (mem_closedBall_zero_iff.1 (hR h)) (not_le.2 hx)

/-- Near `B̄(0, R)` the truncation is a finite sum. -/
theorem truncField_eq_sum {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {α : ℂ → ℝ}
    (hα : ∀ p ∈ C, 0 < α p) {M : ℝ} (hαM : ∀ p ∈ C, α p ≤ M) (E : ℂ → ℂ) {R : ℝ} {x : ℂ}
    (hx : ‖x‖ ≤ R) :
    truncField C α E x = E x - ∑ p ∈ (hC (R + M)).toFinset, gradient (truncLog (α p)) (x - p) := by
  unfold truncField
  congr 1
  refine finsum_mem_eq_finsetSum (fun p hp => mem_of_mem_toFinset _ hp) fun p hpC hp => ?_
  exact gradient_truncLog_far (hα p hpC) (hαM p hpC) hx (lt_norm_of_notMem_toFinset _ hpC hp)

/-- `E_α` is integrable on compact subsets of `U`. -/
theorem integrableOn_truncField {U : Set ℂ} {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    {E : ℂ → ℂ} (hE : LocallyIntegrableOn E U volume) {α : ℂ → ℝ} (hα : ∀ p ∈ C, 0 < α p)
    (hαb : ∃ M, ∀ p ∈ C, α p ≤ M) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    IntegrableOn (truncField C α E) K volume := by
  obtain ⟨M, hM⟩ := hαb
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hsum : Integrable (fun x => ∑ p ∈ (hC (R + M)).toFinset,
      gradient (truncLog (α p)) (x - p)) volume :=
    integrable_finsetSum _ fun p hp =>
      integrable_gradient_truncLog (hα p (mem_of_mem_toFinset _ hp)) p
  refine ((hE.integrableOn_compact_subset hKU hK).sub hsum.integrableOn).congr_fun
    (fun x hx => ?_) hK.measurableSet
  exact (truncField_eq_sum hC hα hM E (mem_closedBall_zero_iff.1 (hR hx))).symm

/-! ### Bounds for test functions -/

theorem exists_norm_gradient_le {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∃ B, ∀ x, ‖gradient φ x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hφ.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφc.fderiv ℝ)
  exact ⟨B, fun x => by simpa [gradient] using hB x⟩

/-! ### The weak equation -/

/-- **The weak equation of `E_α`** (comparison note, Lemma `lem:truncfield`(b), book (4.1.22)), smooth test
functions: `∫ ⟪E_α, ∇φ⟫ = 2π (∑_{p ∈ C} ⨍_{∂B(p, α_p)} φ - m ∫ φ)`. -/
theorem integral_inner_truncField_of_contDiff {U : Set ℂ} {m : ℝ} {C : Set ℂ}
    (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {E : ℂ → ℂ} (hE : IsChargeField U m C E)
    {α : ℂ → ℝ} (hα : ∀ p ∈ C, 0 < α p) (hαb : ∃ M, ∀ p ∈ C, α p ≤ M) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (truncField C α E x) (gradient φ x)) =
      2 * π * ((∑ᶠ p ∈ C, Real.circleAverage φ p (α p)) - m * ∫ x, φ x) := by
  obtain ⟨M, hM⟩ := hαb
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  obtain ⟨B, hB⟩ := exists_norm_gradient_le hφ1 hφc
  set S := (hC (R + M)).toFinset with hS
  have hφ0 := eq_zero_of_tsupport_subset hR
  have hgS : ∀ x ∉ tsupport φ, gradient φ x = 0 := fun x hx => gradient_eq_zero_of_notMem_tsupport hx
  -- pointwise decomposition
  have hpt : ∀ x, inner ℝ (truncField C α E x) (gradient φ x) =
      inner ℝ (E x) (gradient φ x) -
        ∑ p ∈ S, inner ℝ (gradient (truncLog (α p)) (x - p)) (gradient φ x) := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [truncField_eq_sum hC hα hM E (mem_closedBall_zero_iff.1 (hR hx)), inner_sub_left,
        sum_inner]
    · simp [hgS x hx]
  have hint1 : Integrable (fun x => inner ℝ (E x) (gradient φ x)) volume :=
    integrable_inner_of_integrableOn (isClosed_tsupport φ).measurableSet
      (hE.1.integrableOn_compact_subset hφU hφc.isCompact) (aestronglyMeasurable_gradient φ) hB hgS
  have hint2 : ∀ p ∈ S, Integrable
      (fun x => inner ℝ (gradient (truncLog (α p)) (x - p)) (gradient φ x)) volume := fun p hp =>
    integrable_inner_of_integrableOn MeasurableSet.univ
      (integrable_gradient_truncLog (hα p (mem_of_mem_toFinset _ hp)) p).integrableOn
      (aestronglyMeasurable_gradient φ) hB (fun x hx => absurd (mem_univ x) hx)
  simp_rw [hpt]
  rw [integral_sub hint1 (integrable_finsetSum _ hint2), integral_finsetSum _ hint2,
    hE.2 φ hφ hφc hφU]
  rw [Finset.sum_congr rfl fun p hp => integral_inner_gradient_truncLog hφ1
    (hα p (mem_of_mem_toFinset _ hp)) p]
  have hfar : ∀ p ∈ C, p ∉ S → R + M < ‖p‖ := fun p hpC hp => lt_norm_of_notMem_toFinset _ hpC hp
  have hsum1 : ∑ᶠ p ∈ C, φ p = ∑ p ∈ S, φ p :=
    finsum_mem_eq_finsetSum (fun p hp => mem_of_mem_toFinset _ hp) fun p hpC hp =>
      hφ0 p (by linarith [hfar p hpC hp, (hα p hpC).trans_le (hM p hpC)])
  have hsum2 : ∑ᶠ p ∈ C, Real.circleAverage φ p (α p) = ∑ p ∈ S, Real.circleAverage φ p (α p) :=
    finsum_mem_eq_finsetSum (fun p hp => mem_of_mem_toFinset _ hp) fun p hpC hp =>
      circleAverage_far hφ0 (hα p hpC) (hM p hpC) (hfar p hpC hp)
  rw [hsum1, hsum2, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

end Screening

end SandierSerfaty

end
