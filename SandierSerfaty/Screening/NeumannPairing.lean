/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Defs
public import SandierSerfaty.Screening.Mollify
public import SandierSerfaty.Screening.Pairing

/-!
# Pairings on a set with Lipschitz and smooth test functions

* `setIntegral_inner_gradient_lipschitz`: if a field `G ∈ L¹(S)` satisfies
  `∫_S ⟪G, ∇φ⟫ = 2π (∑_{y ∈ Y} φ y - m ∫_S φ)` for smooth compactly supported `φ` with support in an
  open set `U`, the same identity holds for Lipschitz compactly supported `φ` with support in `U`
  (mollification, `exists_smooth_approx`; the screening note's Lemma `lem:moll`).
* `IsNeumannChargeField.setIntegral_inner_gradient_lipschitz`: the Neumann identity for Lipschitz
  compactly supported test functions.
* `IsNeumannChargeField.setIntegral_inner_gradient_of_contDiff`: the Neumann identity for every
  smooth `φ` (no support condition), on a bounded set `Q` (cut `φ` off far from `Q`).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

/-- Uniform convergence of compactly supported continuous functions gives convergence of the set
integrals over any measurable set. -/
theorem tendsto_setIntegral_of_approx {ψ : ℕ → ℂ → ℝ} {φ : ℂ → ℝ} {δ : ℕ → ℝ} {S T : Set ℂ}
    (hS : MeasurableSet S) (hT : IsCompact T) (hψ : ∀ n, Continuous (ψ n)) (hφ : Continuous φ)
    (hψT : ∀ n, ∀ x ∉ T, ψ n x = 0) (hφT : ∀ x ∉ T, φ x = 0) (hδ : Tendsto δ atTop (𝓝 0))
    (h : ∀ n x, |ψ n x - φ x| ≤ δ n) :
    Tendsto (fun n => ∫ x in S, ψ n x) atTop (𝓝 (∫ x in S, φ x)) := by
  have hint : ∀ f : ℂ → ℝ, Continuous f → (∀ x ∉ T, f x = 0) → Integrable f volume :=
    fun f hf hfT => hf.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hT fun x hx => hfT x hx)
  refine tendsto_of_abs_sub_le (by simpa using hδ.mul_const (volume.real T)) fun n => ?_
  rw [← integral_sub (hint _ (hψ n) (hψT n)).integrableOn (hint _ hφ hφT).integrableOn,
    ← integral_indicator hS]
  have hb : Integrable (T.indicator fun _ => δ n) volume :=
    (integrable_indicator_iff hT.measurableSet).2 (integrableOn_const hT.measure_lt_top.ne)
  have := norm_integral_le_of_norm_le (f := S.indicator fun x => ψ n x - φ x) hb
    (Eventually.of_forall fun x => ?_)
  · rwa [Real.norm_eq_abs, integral_indicator hT.measurableSet, setIntegral_const,
      smul_eq_mul, mul_comm] at this
  · by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS, Real.norm_eq_abs]
      by_cases hxT : x ∈ T
      · rw [indicator_of_mem hxT]; exact h n x
      · rw [indicator_of_notMem hxT, hψT n x hxT, hφT x hxT, sub_zero, abs_zero]
    · rw [indicator_of_notMem hxS, norm_zero]
      by_cases hxT : x ∈ T
      · rw [indicator_of_mem hxT]; exact (abs_nonneg _).trans (h n x)
      · rw [indicator_of_notMem hxT]

theorem setIntegral_inner_eq_integral_indicator {G : ℂ → ℂ} {g : ℂ → ℂ} {S : Set ℂ}
    (hS : MeasurableSet S) :
    ∫ x in S, inner ℝ (G x) (g x) = ∫ x, inner ℝ (S.indicator G x) (g x) := by
  rw [← integral_indicator hS]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, inner_zero_left]

/-- **Lipschitz test functions in a set pairing.** -/
theorem setIntegral_inner_gradient_lipschitz {S U : Set ℂ} (hS : MeasurableSet S) (hU : IsOpen U)
    {G : ℂ → ℂ} (hG : IntegrableOn G S) {Y : Finset ℂ} {m : ℝ}
    (hsmooth : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in S, inner ℝ (G x) (gradient φ x) = 2 * π * (∑ y ∈ Y, φ y - m * ∫ x in S, φ x))
    {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    ∫ x in S, inner ℝ (G x) (gradient φ x) = 2 * π * (∑ y ∈ Y, φ y - m * ∫ x in S, φ x) := by
  obtain ⟨ψ, T, δ, hT, hTU, hφT, hδ, hψ, hψφ, hψB, hlim⟩ := exists_smooth_approx hU hφ hφc hφU
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).1.continuous
  have hψT : ∀ n, ∀ x ∉ T, ψ n x = 0 := fun n x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx ((hψ n).2.2 h)
  have hφT' : ∀ x ∉ T, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hφT h)
  have hGi : IntegrableOn (S.indicator G) T := ((integrable_indicator_iff hS).2 hG).integrableOn
  have hL := tendsto_integral_inner_gradient hT.measurableSet hGi
    (fun n x hx => gradient_eq_zero_of_notMem_tsupport fun h => hx ((hψ n).2.2 h)) hψB hlim
  simp only [← setIntegral_inner_eq_integral_indicator hS] at hL
  have hEq : ∀ n, ∫ x in S, inner ℝ (G x) (gradient (ψ n) x) =
      2 * π * (∑ y ∈ Y, ψ n y - m * ∫ x in S, ψ n x) := fun n =>
    hsmooth _ (hψ n).1 (hψ n).2.1 ((hψ n).2.2.trans hTU)
  simp only [hEq] at hL
  refine tendsto_nhds_unique hL (tendsto_const_nhds.mul ((tendsto_finsetSum _ fun y _ => ?_).sub
    (tendsto_const_nhds.mul (tendsto_setIntegral_of_approx hS hT hψc hφ.continuous hψT hφT' hδ
      hψφ))))
  exact tendsto_of_abs_sub_le hδ fun n => hψφ n y

end Screening

open Screening

/-- **The Neumann identity for Lipschitz test functions.** -/
theorem IsNeumannChargeField.setIntegral_inner_gradient_lipschitz {Q : Set ℂ} {m : ℝ}
    {Y : Finset ℂ} {E : ℂ → ℂ} (hE : IsNeumannChargeField Q m Y E) (hQ : MeasurableSet Q)
    {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (hφc : HasCompactSupport φ) :
    ∫ x in Q, inner ℝ (E x) (gradient φ x) = 2 * π * (∑ y ∈ Y, φ y - m * ∫ x in Q, φ x) :=
  Screening.setIntegral_inner_gradient_lipschitz hQ isOpen_univ hE.1 (fun ψ hψ hψc _ => hE.2 ψ hψ hψc) hφ
    hφc (subset_univ _)

/-- **The Neumann identity for smooth test functions** (no support condition): cut `φ` off far
from the bounded set `Q` and the charges. -/
theorem IsNeumannChargeField.setIntegral_inner_gradient_of_contDiff {Q : Set ℂ} {m : ℝ}
    {Y : Finset ℂ} {E : ℂ → ℂ} (hE : IsNeumannChargeField Q m Y E) (hQ : MeasurableSet Q)
    (hQb : Bornology.IsBounded Q) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∫ x in Q, inner ℝ (E x) (gradient φ x) = 2 * π * (∑ y ∈ Y, φ y - m * ∫ x in Q, φ x) := by
  obtain ⟨R, hR⟩ := (hQb.union Y.finite_toSet.isBounded).subset_closedBall (0 : ℂ)
  set R' := max R 0 + 1 with hR'
  have hR'0 : 0 < R' := by positivity
  let χ : ContDiffBump (0 : ℂ) := ⟨R', R' + 1, hR'0, by linarith⟩
  set ψ : ℂ → ℝ := fun x => χ x * φ x with hψ
  have hψs : ContDiff ℝ ∞ ψ := χ.contDiff.mul hφ
  have hψc : HasCompactSupport ψ := χ.hasCompactSupport.mul_right
  have hball : ∀ x ∈ Q ∪ (Y : Set ℂ), ball (0 : ℂ) R' ∈ 𝓝 x := fun x hx =>
    isOpen_ball.mem_nhds (mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 (hR hx)).trans_lt
      (by rw [hR']; linarith [le_max_left R 0])))
  have hev : ∀ x ∈ Q ∪ (Y : Set ℂ), ψ =ᶠ[𝓝 x] φ := fun x hx => by
    filter_upwards [hball x hx] with y hy
    rw [hψ]
    simp only
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
  have h := hE.2 ψ hψs hψc
  have hg : ∫ x in Q, inner ℝ (E x) (gradient ψ x) = ∫ x in Q, inner ℝ (E x) (gradient φ x) :=
    setIntegral_congr_fun hQ fun x hx => by rw [gradient_congr_nhds (hev x (Or.inl hx))]
  have hY : ∑ y ∈ Y, ψ y = ∑ y ∈ Y, φ y :=
    Finset.sum_congr rfl fun y hy => (hev y (Or.inr hy)).eq_of_nhds
  have hi : ∫ x in Q, ψ x = ∫ x in Q, φ x :=
    setIntegral_congr_fun hQ fun x hx => (hev x (Or.inl hx)).eq_of_nhds
  rw [← hg, h, hY, hi]

end SandierSerfaty

end
