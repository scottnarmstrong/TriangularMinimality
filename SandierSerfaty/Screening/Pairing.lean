/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.TruncFieldWeak

/-!
# Pairing of truncated fields with Lipschitz test functions (I1)

**I1** (`integral_inner_truncField_lipschitz`; the comparison note's Lemma `lem:pairing`, book (4.1.22)–(4.1.23)):
if `E` is a charge field of density `m` in the open set `U`, then for every Lipschitz `φ` with compact
support in `U`, `∫ ⟪E_α, ∇φ⟫ = 2π (∑_{p ∈ C} ⨍_{∂B(p, α_p)} φ - m ∫ φ)`, with `∇φ` the a.e. gradient
(`gradient` is `0` at non-differentiability points). No `L²` hypothesis is needed: `E_α ∈ L¹_loc(U)`
and `∇φ` is bounded.

`integral_inner_gradient_truncLog_sub_lipschitz`: the same pairing for the field
`∇f_a(· - i) - ∇f_b(· - i)`, i.e. `-Δ f_{a,b}(· - i) = 2π (δ_i^{(b)} - δ_i^{(a)})` tested against
Lipschitz functions.

Both pass to the limit along the smooth approximations of `exists_smooth_approx`.
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal ContDiff Real

public section

namespace SandierSerfaty

namespace Screening

/-! ### Limits along uniform approximation -/

theorem tendsto_of_abs_sub_le {a : ℕ → ℝ} {l : ℝ} {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (h : ∀ n, |a n - l| ≤ δ n) : Tendsto a atTop (𝓝 l) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun n => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact h n) hδ

theorem abs_circleAverage_sub_le {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g) {δ : ℝ}
    (h : ∀ x, |f x - g x| ≤ δ) (c : ℂ) (r : ℝ) :
    |Real.circleAverage f c r - Real.circleAverage g c r| ≤ δ := by
  have hfi : CircleIntegrable f c r := hf.continuousOn.circleIntegrable'
  have hgi : CircleIntegrable g c r := hg.continuousOn.circleIntegrable'
  rw [← Real.circleAverage_sub hfi hgi]
  refine Real.abs_circleAverage_le_circleAverage_abs.trans ?_
  exact Real.circleAverage_mono_on_of_le_circle
    ((hf.sub hg).abs.continuousOn.circleIntegrable') fun x _ => h x

theorem tendsto_circleAverage_of_approx {ψ : ℕ → ℂ → ℝ} {φ : ℂ → ℝ} {δ : ℕ → ℝ}
    (hψ : ∀ n, Continuous (ψ n)) (hφ : Continuous φ) (hδ : Tendsto δ atTop (𝓝 0))
    (h : ∀ n x, |ψ n x - φ x| ≤ δ n) (c : ℂ) (r : ℝ) :
    Tendsto (fun n => Real.circleAverage (ψ n) c r) atTop (𝓝 (Real.circleAverage φ c r)) :=
  tendsto_of_abs_sub_le hδ fun n => abs_circleAverage_sub_le (hψ n) hφ (h n) c r

theorem tendsto_integral_of_approx {ψ : ℕ → ℂ → ℝ} {φ : ℂ → ℝ} {δ : ℕ → ℝ} {S : Set ℂ}
    (hS : IsCompact S) (hψ : ∀ n, Continuous (ψ n)) (hφ : Continuous φ)
    (hψS : ∀ n, ∀ x ∉ S, ψ n x = 0) (hφS : ∀ x ∉ S, φ x = 0) (hδ : Tendsto δ atTop (𝓝 0))
    (h : ∀ n x, |ψ n x - φ x| ≤ δ n) :
    Tendsto (fun n => ∫ x, ψ n x) atTop (𝓝 (∫ x, φ x)) := by
  have hint : ∀ f : ℂ → ℝ, Continuous f → (∀ x ∉ S, f x = 0) → Integrable f volume :=
    fun f hf hfS => hf.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hS fun x hx => hfS x hx)
  refine tendsto_of_abs_sub_le (by simpa using hδ.mul_const (volume.real S)) fun n => ?_
  rw [← integral_sub (hint _ (hψ n) (hψS n)) (hint _ hφ hφS),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
      fun x hx => by simp [hψS n x hx, hφS x hx]]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun x => ψ n x - φ x)
    hS.measure_lt_top
    fun x _ => by rw [Real.norm_eq_abs]; exact h n x
  rwa [Real.norm_eq_abs] at this

/-! ### I1 -/

end Screening

open Screening in
/-- **I1: pairing of a truncated charge field with Lipschitz test functions** (comparison note, Lemma
`lem:pairing`, book (4.1.22)–(4.1.23)). -/
theorem integral_inner_truncField_lipschitz {U : Set ℂ} (hU : IsOpen U) {m : ℝ} {C : Set ℂ}
    (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {E : ℂ → ℂ} (hE : IsChargeField U m C E)
    {α : ℂ → ℝ} (hα : ∀ p ∈ C, 0 < α p) (hαb : ∃ M, ∀ p ∈ C, α p ≤ M)
    {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (truncField C α E x) (gradient φ x)) =
      2 * Real.pi * ((∑ᶠ p ∈ C, Real.circleAverage φ p (α p)) - m * ∫ x, φ x) := by
  obtain ⟨ψ, S, δ, hS, hSU, hφS, hδ, hψ, hψφ, hψB, hlim⟩ := exists_smooth_approx hU hφ hφc hφU
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).1.continuous
  have hψS : ∀ n, ∀ x ∉ S, ψ n x = 0 := fun n x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ((hψ n).2.2 h)
  have hφS' : ∀ x ∉ S, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφS h)
  have hL := tendsto_integral_inner_gradient hS.measurableSet
    (integrableOn_truncField hC hE.1 hα hαb hS hSU)
    (fun n x hx => gradient_eq_zero_of_notMem_tsupport fun h => hx ((hψ n).2.2 h)) hψB hlim
  have hEq : ∀ n, (∫ x, inner ℝ (truncField C α E x) (gradient (ψ n) x)) =
      2 * π * ((∑ᶠ p ∈ C, Real.circleAverage (ψ n) p (α p)) - m * ∫ x, ψ n x) := fun n =>
    integral_inner_truncField_of_contDiff hC hE hα hαb (hψ n).1 (hψ n).2.1 ((hψ n).2.2.trans hSU)
  simp only [hEq] at hL
  refine tendsto_nhds_unique hL ?_
  -- the right-hand side converges
  obtain ⟨M, hM⟩ := hαb
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  set T := (hC (R + M)).toFinset
  have hfin : ∀ f : ℂ → ℝ, (∀ x ∉ S, f x = 0) →
      ∑ᶠ p ∈ C, Real.circleAverage f p (α p) = ∑ p ∈ T, Real.circleAverage f p (α p) :=
    fun f hfS => finsum_mem_eq_finsetSum (fun p hp => mem_of_mem_toFinset _ hp) fun p hpC hp =>
      circleAverage_far (fun x hx => hfS x fun h => absurd (mem_closedBall_zero_iff.1 (hR h))
        (not_le.2 hx)) (hα p hpC) (hM p hpC) (lt_norm_of_notMem_toFinset _ hpC hp)
  simp only [hfin _ (hψS _), hfin _ hφS']
  refine (tendsto_const_nhds.mul ((tendsto_finsetSum _ fun p _ =>
    tendsto_circleAverage_of_approx hψc hφ.continuous hδ hψφ p (α p)).sub
      (tendsto_const_nhds.mul (tendsto_integral_of_approx hS hψc hφ.continuous hψS hφS' hδ hψφ))))

namespace Screening

/-- The pairing of `∇f_a(· - i) - ∇f_b(· - i)` with a Lipschitz test function:
`-Δ (f_a - f_b)(· - i) = 2π (δ_i^{(b)} - δ_i^{(a)})`. -/
theorem integral_inner_gradient_truncLog_sub_lipschitz {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (i : ℂ) {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ) :
    (∫ x, inner ℝ (gradient (truncLog a) (x - i) - gradient (truncLog b) (x - i))
      (gradient φ x)) =
      2 * π * (Real.circleAverage φ i b - Real.circleAverage φ i a) := by
  obtain ⟨ψ, S, δ, hS, -, hφS, hδ, hψ, hψφ, hψB, hlim⟩ :=
    exists_smooth_approx isOpen_univ hφ hφc (subset_univ _)
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).1.continuous
  have hG : Integrable (fun x => gradient (truncLog a) (x - i) - gradient (truncLog b) (x - i))
      volume := (integrable_gradient_truncLog ha i).sub (integrable_gradient_truncLog hb i)
  have hL := tendsto_integral_inner_gradient hS.measurableSet hG.integrableOn
    (fun n x hx => gradient_eq_zero_of_notMem_tsupport fun h => hx ((hψ n).2.2 h)) hψB hlim
  have hEq : ∀ n, (∫ x, inner ℝ (gradient (truncLog a) (x - i) - gradient (truncLog b) (x - i))
      (gradient (ψ n) x)) = 2 * π * (Real.circleAverage (ψ n) i b -
        Real.circleAverage (ψ n) i a) := by
    intro n
    have h1 : ContDiff ℝ 1 (ψ n) := (hψ n).1.of_le (by simp)
    obtain ⟨B, hB⟩ := exists_norm_gradient_le h1 (hψ n).2.1
    have hi : ∀ η > 0, Integrable
        (fun x => inner ℝ (gradient (truncLog η) (x - i)) (gradient (ψ n) x)) volume :=
      fun η hη => integrable_inner_of_integrableOn MeasurableSet.univ
        (integrable_gradient_truncLog hη i).integrableOn (aestronglyMeasurable_gradient _) hB
        (fun x hx => absurd (mem_univ x) hx)
    simp_rw [inner_sub_left]
    rw [integral_sub (hi a ha) (hi b hb), integral_inner_gradient_truncLog h1 ha,
      integral_inner_gradient_truncLog h1 hb]
    ring
  simp only [hEq] at hL
  exact tendsto_nhds_unique hL (tendsto_const_nhds.mul
    ((tendsto_circleAverage_of_approx hψc hφ.continuous hδ hψφ i b).sub
      (tendsto_circleAverage_of_approx hψc hφ.continuous hδ hψφ i a)))

end Screening

end SandierSerfaty

end
