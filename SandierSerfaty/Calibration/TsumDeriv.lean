/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Termwise differentiation of series on an open interval

Mathlib's `contDiff_tsum` is global; the calibration series have summable derivative majorants only on
the half-lines `[d, ∞)`, `d > 0` (the modes `i ≤ 38` carry the logarithm at `0`). The lemmas here are the
local versions, through `hasDerivAt_tsum_of_isPreconnected`:

* `tsum_contDiffOn_one`: `F = ∑' i, g i` is `C¹` on an open interval `U` with
  `F' = ∑' i, (g i)'` if the `g i` are `C¹` on `U` with summable majorants of `g i` and `(g i)'`;
* `tsum_contDiffOn_two`: the same for `C²`, with `F'' = ∑' i, (g i)''`.

The index type is arbitrary (`ℕ` for single sums, `ℕ × ℕ` for the double sums of `f₀` and `e`).
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

variable {ι : Type*} {U : Set ℝ} {g : ι → ℝ → ℝ}

/-- First-order termwise differentiation on an open preconnected set. -/
theorem tsum_contDiffOn_one {M₀ M₁ : ι → ℝ} (hU : IsOpen U) (hc : IsPreconnected U)
    (h₀ : Summable M₀) (h₁ : Summable M₁) (hg : ∀ i, ContDiffOn ℝ 1 (g i) U)
    (b₀ : ∀ i, ∀ x ∈ U, |g i x| ≤ M₀ i) (b₁ : ∀ i, ∀ x ∈ U, |deriv (g i) x| ≤ M₁ i) :
    ContDiffOn ℝ 1 (fun x => ∑' i, g i x) U ∧
      ∀ x ∈ U, HasDerivAt (fun x => ∑' i, g i x) (∑' i, deriv (g i) x) x := by
  have hd : ∀ i, ∀ x ∈ U, HasDerivAt (g i) (deriv (g i) x) x := fun i x hx =>
    (((hg i).differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hcont : ∀ i, ContinuousOn (deriv (g i)) U := fun i =>
    ((hg i).deriv_of_isOpen hU (m := 0) (by simp)).continuousOn
  have key : ∀ x ∈ U, HasDerivAt (fun x => ∑' i, g i x) (∑' i, deriv (g i) x) x := by
    intro x hx
    exact hasDerivAt_tsum_of_isPreconnected h₁ hU hc hd b₁ hx
      (Summable.of_norm_bounded h₀ fun i => by simpa [Real.norm_eq_abs] using b₀ i x hx) hx
  refine ⟨?_, key⟩
  have hder : EqOn (deriv fun x => ∑' i, g i x) (fun x => ∑' i, deriv (g i) x) U :=
    fun x hx => (key x hx).deriv
  have h1 : DifferentiableOn ℝ (fun x => ∑' i, g i x) U :=
    fun x hx => (key x hx).differentiableAt.differentiableWithinAt
  have h2 : ContinuousOn (fun x => ∑' i, deriv (g i) x) U :=
    continuousOn_tsum hcont h₁ fun i x hx => by simpa [Real.norm_eq_abs] using b₁ i x hx
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨h1, by simp, ?_⟩
  exact (contDiffOn_zero.2 h2).congr fun x hx => hder hx

/-- Second-order termwise differentiation on an open preconnected set. -/
theorem tsum_contDiffOn_two {M₀ M₁ M₂ : ι → ℝ} (hU : IsOpen U) (hc : IsPreconnected U)
    (h₀ : Summable M₀) (h₁ : Summable M₁) (h₂ : Summable M₂) (hg : ∀ i, ContDiffOn ℝ 2 (g i) U)
    (b₀ : ∀ i, ∀ x ∈ U, |g i x| ≤ M₀ i) (b₁ : ∀ i, ∀ x ∈ U, |deriv (g i) x| ≤ M₁ i)
    (b₂ : ∀ i, ∀ x ∈ U, |deriv (deriv (g i)) x| ≤ M₂ i) :
    ContDiffOn ℝ 2 (fun x => ∑' i, g i x) U ∧
      (∀ x ∈ U, deriv (fun x => ∑' i, g i x) x = ∑' i, deriv (g i) x) ∧
      ∀ x ∈ U, deriv (deriv fun x => ∑' i, g i x) x = ∑' i, deriv (deriv (g i)) x := by
  have hg1 : ∀ i, ContDiffOn ℝ 1 (g i) U := fun i => (hg i).of_le (by norm_num)
  have hg' : ∀ i, ContDiffOn ℝ 1 (deriv (g i)) U := fun i =>
    (hg i).deriv_of_isOpen hU (m := 1) (by norm_num)
  obtain ⟨hF, hF'⟩ := tsum_contDiffOn_one hU hc h₀ h₁ hg1 b₀ b₁
  obtain ⟨hG, hG'⟩ := tsum_contDiffOn_one (g := fun i => deriv (g i)) hU hc h₁ h₂ hg' b₁ b₂
  have hder : EqOn (deriv fun x => ∑' i, g i x) (fun x => ∑' i, deriv (g i) x) U :=
    fun x hx => (hF' x hx).deriv
  refine ⟨?_, fun x hx => (hF' x hx).deriv, fun x hx => ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hU]
    exact ⟨hF.differentiableOn one_ne_zero, by simp, hG.congr fun x hx => hder hx⟩
  · have : deriv (fun x => ∑' i, g i x) =ᶠ[nhds x] fun x => ∑' i, deriv (g i) x :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hder
    rw [this.deriv_eq]
    exact (hG' x hx).deriv

end Calibration

end SandierSerfaty

end
