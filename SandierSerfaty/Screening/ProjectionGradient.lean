/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ProjectionTest
public import SandierSerfaty.Screening.ProjectionTorus
public import SandierSerfaty.Screening.TruncDiff

/-!
# The truncated torus potential as a sum of admissible test functions

Setting of the screening note's §5: `Γ = squareLattice N`, `Q = sq c √N`, charges `a i ∈ int Q`, distinct,
`H = torusPotential Γ a`. For a radius `η > 0`, the bump `b = projBump η` (`1` on `B̄(0, η)`,
supported in `B(0, 2η)`) and a radius family `r` with `η ≤ r (a i)`:

* `projPer Γ a b = ∑ᵢ projSmooth Γ b (· - aᵢ)`: smooth, `Γ`-periodic, Lipschitz;
* `projLoc Γ a b η r = ∑ᵢ (projSing Γ b η + f_{η, r(aᵢ)}) (· - aᵢ)`: Lipschitz, supported in
  `⋃ᵢ B̄(aᵢ, max (2η) r(aᵢ)) ⊆ int Q`;
* `projPer_add_projLoc`: on `Q` off the charges, `projPer + projLoc = H - ∑ᵢ f_{r(aᵢ)}(· - aᵢ)`;
* `gradient_projPer_add_projLoc`: hence, on `int Q` off the charges and the circles
  `|x - aᵢ| = r(aᵢ)`, `∇(projPer + projLoc) = (∇H)_r = truncField (range a) r ∇H`.

This is the screening note's Lemma `lem:Htilde` in decomposed form.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

public section

namespace SandierSerfaty

namespace Screening

open Torus

/-- The bump `1` on `closedBall 0 η`, supported in `ball 0 (2η)`. -/
@[expose] noncomputable def projBump {η : ℝ} (hη : 0 < η) : ContDiffBump (0 : ℂ) :=
  ⟨η, 2 * η, hη, by linarith⟩

variable {N : ℕ}

/-- The smooth periodic part of the test function. -/
@[expose] noncomputable def projPer (Γ : Submodule ℤ ℂ) (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ))
    (x : ℂ) : ℝ :=
  ∑ i, projSmooth Γ b (x - a i)

/-- The compactly supported Lipschitz part of the test function. -/
@[expose] noncomputable def projLoc (Γ : Submodule ℤ ℂ) (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ))
    (η : ℝ) (r : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∑ i, (projSing Γ b η (x - a i) + truncDiff η (r (a i)) (x - a i))

/-! ### Lipschitz helpers -/

theorem lipschitzWith_comp_sub {f : ℂ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (c : ℂ) :
    LipschitzWith K fun x => f (x - c) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_sub_right] using hf.dist_le_mul (x - c) (y - c)

theorem exists_lipschitzWith_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℝ}
    (h : ∀ i, ∃ K, LipschitzWith K (f i)) : ∃ K, LipschitzWith K fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨Kj, hKj⟩ := h j
    refine ⟨Kj + K, ?_⟩
    have e : (fun x => ∑ i ∈ insert j s, f i x) = (f j) + fun x => ∑ i ∈ s, f i x := by
      ext x; simp [Finset.sum_insert hj]
    rw [e]; exact hKj.add hK

theorem sqrt_le_norm_of_mem {γ : ℂ} (hγ : γ ∈ squareLattice N) (h0 : γ ≠ 0) : √(N : ℝ) ≤ ‖γ‖ :=
  sqrt_le_norm_of_mem_squareLattice hγ h0

variable [NeZero N]

/-! ### The periodic part -/

theorem contDiff_projPer (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ))
    (hb : b.rIn + b.rOut ≤ √(N : ℝ)) : ContDiff ℝ ∞ (projPer (squareLattice N) a b) :=
  ContDiff.sum fun _ _ =>
    (contDiff_projSmooth (fun _ hγ h0 => sqrt_le_norm_of_mem hγ h0) b hb).comp
      (contDiff_id.sub contDiff_const)

theorem projPer_add_period (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ)) {γ : ℂ}
    (hγ : γ ∈ squareLattice N) (x : ℂ) :
    projPer (squareLattice N) a b (x + γ) = projPer (squareLattice N) a b x := by
  unfold projPer
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show x + γ - a i = (x - a i) + γ by ring, projSmooth_add_period b hγ]

theorem exists_lipschitzWith_projPer (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ))
    (hb : b.rIn + b.rOut ≤ √(N : ℝ)) : ∃ K, LipschitzWith K (projPer (squareLattice N) a b) :=
  exists_lipschitzWith_of_periodic ((contDiff_projPer a b hb).of_le (by simp))
    fun γ hγ x => projPer_add_period a b hγ x

/-! ### The local part -/

theorem exists_lipschitzWith_projLoc (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ))
    (hb : b.rOut < √(N : ℝ)) {η : ℝ} (hη : 0 < η) {r : ℂ → ℝ} (hr : ∀ i, η ≤ r (a i)) :
    ∃ K, LipschitzWith K (projLoc (squareLattice N) a b η r) := by
  obtain ⟨KB, hKB⟩ := exists_lipschitzWith_projSing (fun γ hγ h0 => sqrt_le_norm_of_mem hγ h0) b
    hb hη
  exact exists_lipschitzWith_sum Finset.univ fun i =>
    ⟨KB + Real.toNNReal η⁻¹, (lipschitzWith_comp_sub hKB (a i)).add
      (lipschitzWith_comp_sub (lipschitzWith_truncDiff hη (hr i)) (a i))⟩

omit [NeZero N] in
theorem projLoc_eq_zero (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ)) (η : ℝ) (r : ℂ → ℝ) {x : ℂ}
    (hx : ∀ i, max b.rOut (r (a i)) ≤ ‖x - a i‖) : projLoc (squareLattice N) a b η r x = 0 := by
  unfold projLoc
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [projSing_eq_zero b η ((le_max_left _ _).trans (hx i)),
    truncDiff_eq_zero ((le_max_right _ _).trans (hx i)), add_zero]

omit [NeZero N] in
theorem tsupport_projLoc_subset (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ)) (η : ℝ) (r : ℂ → ℝ) :
    tsupport (projLoc (squareLattice N) a b η r) ⊆
      ⋃ i, closedBall (a i) (max b.rOut (r (a i))) := by
  refine closure_minimal (fun x hx => ?_) (isClosed_iUnion_of_finite fun i => isClosed_closedBall)
  by_contra h
  simp only [mem_iUnion, mem_closedBall, dist_eq_norm, not_exists, not_le] at h
  exact hx (projLoc_eq_zero a b η r fun i => (h i).le)

omit [NeZero N] in
theorem hasCompactSupport_projLoc (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ)) (η : ℝ)
    (r : ℂ → ℝ) : HasCompactSupport (projLoc (squareLattice N) a b η r) :=
  (isCompact_iUnion fun _ => isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_projLoc_subset a b η r)

/-! ### The identity on the square -/

variable {c : ℂ} {a : Fin N → ℂ}

omit [NeZero N] in
/-- On `Q`, the periodized bump at `x - aᵢ` is the bump itself. -/
theorem periodize_projBump_eq (b : ContDiffBump (0 : ℂ))
    (hbQ : ∀ i, closedBall (a i) b.rOut ⊆ interior (sq c √N)) {x : ℂ} (hx : x ∈ sq c √N)
    (i : Fin N) : periodize (squareLattice N) b (x - a i) = b (x - a i) := by
  have h := periodize_eq_single (Γ := squareLattice N) (f := b) (s := b.rOut)
    (fun w hw => bump_eq_zero_of_le_norm b hw) (z := x - a i) 0 fun γ hγ => ?_
  · rw [h]; simp
  · by_contra hlt
    have h0 : (γ : ℂ) ≠ 0 := fun h => hγ (Subtype.ext h)
    have hmem : (γ : ℂ) + x ∈ interior (sq c √N) := hbQ i (by
      rw [mem_closedBall, dist_eq_norm]
      exact (show ‖(γ : ℂ) + x - a i‖ < b.rOut by
        rw [show (γ : ℂ) + x - a i = (γ : ℂ) + (x - a i) by ring]; exact not_le.1 hlt).le)
    refine add_notMem_sq_of_mem_interior hmem ((squareLattice N).neg_mem γ.2) (neg_ne_zero.2 h0) ?_
    rwa [add_neg_cancel_comm]

omit [NeZero N] in
/-- **The pointwise identity**: on `Q` off the charges,
`projPer + projLoc = greenSum - ∑ᵢ f_{r(aᵢ)}(· - aᵢ)`. -/
theorem projPer_add_projLoc {η : ℝ} (hη : 0 < η)
    (b : ContDiffBump (0 : ℂ)) (hηb : η ≤ b.rIn)
    (hbQ : ∀ i, closedBall (a i) b.rOut ⊆ interior (sq c √N)) {r : ℂ → ℝ}
    (hr : ∀ i, η ≤ r (a i)) {x : ℂ} (hx : x ∈ sq c √N) (hxP : x ∉ chargeSet (squareLattice N) a) :
    projPer (squareLattice N) a b x + projLoc (squareLattice N) a b η r x =
      greenSum (squareLattice N) a x - ∑ i, truncLog (r (a i)) (x - a i) := by
  unfold projPer projLoc greenSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hy0 : x - a i ≠ 0 := fun h => notMem_chargeSet_iff.1 hxP i (by rw [h]; exact zero_mem _)
  have h1 := projSmooth_add_projSing b hη hηb hy0 (periodize_projBump_eq b hbQ hx i)
  have h2 := truncLog_sub_truncLog hη (hr i) hy0
  linarith

omit [NeZero N] in
/-- The gradient of `f - ∑ᵢ gᵢ` at a point where all are differentiable. -/
theorem gradient_sub_sum {f : ℂ → ℝ} {g : Fin N → ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ f x)
    (hg : ∀ i, DifferentiableAt ℝ (g i) x) :
    gradient (fun y => f y - ∑ i, g i y) x = gradient f x - ∑ i, gradient (g i) x := by
  simp only [gradient]
  rw [fderiv_fun_sub hf (DifferentiableAt.fun_sum fun i _ => hg i),
    fderiv_fun_sum fun i _ => hg i, map_sub, map_sum]

/-- **The gradient identity**: on `int Q`, off the charges and the circles `|x - aᵢ| = r(aᵢ)`,
`∇(projPer + projLoc) = (∇H)_r`. -/
theorem gradient_projPer_add_projLoc (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √N)) {η : ℝ} (hη : 0 < η) (b : ContDiffBump (0 : ℂ))
    (hηb : η ≤ b.rIn) (hbQ : ∀ i, closedBall (a i) b.rOut ⊆ interior (sq c √N)) {r : ℂ → ℝ}
    (hr : ∀ i, η ≤ r (a i)) {x : ℂ} (hx : x ∈ interior (sq c √N))
    (hxP : x ∉ chargeSet (squareLattice N) a) (hxr : ∀ i, ‖x - a i‖ ≠ r (a i)) :
    gradient (fun y => projPer (squareLattice N) a b y + projLoc (squareLattice N) a b η r y) x =
      truncField (range a) r (gradient (torusPotential (squareLattice N) a)) x := by
  have hopen : IsOpen (interior (sq c √N) ∩ (chargeSet (squareLattice N) a)ᶜ) :=
    isOpen_interior.inter (isClosed_chargeSet _ a).isOpen_compl
  have hev : (fun y => projPer (squareLattice N) a b y + projLoc (squareLattice N) a b η r y) =ᶠ[𝓝 x]
      fun y => greenSum (squareLattice N) a y - ∑ i, truncLog (r (a i)) (y - a i) := by
    filter_upwards [hopen.mem_nhds ⟨hx, hxP⟩] with y hy
    exact projPer_add_projLoc hη b hηb hbQ hr (interior_subset hy.1) hy.2
  have hy0 : ∀ i, x - a i ≠ 0 := fun i h =>
    notMem_chargeSet_iff.1 hxP i (by rw [h]; exact zero_mem _)
  have hrpos : ∀ i, 0 < r (a i) := fun i => hη.trans_le (hr i)
  have hdiff : ∀ i, DifferentiableAt ℝ (fun y => truncLog (r (a i)) (y - a i)) x := fun i =>
    (differentiableAt_truncLog (hrpos i) (hy0 i) (hxr i)).comp x
      (differentiableAt_id.sub_const _)
  rw [gradient_congr_nhds hev,
    gradient_sub_sum ((contDiffAt_greenSum hxP).differentiableAt (by simp)) hdiff,
    ← gradient_torusPotential_eq_greenSum ha haQ hxP]
  unfold truncField
  rw [finsum_range_eq, sum_image_eq ha]
  congr 1
  exact Finset.sum_congr rfl fun i _ => gradient_comp_sub_right _ (a i) x

end Screening

end SandierSerfaty

end
