/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import SandierSerfaty.Analysis.LaplacianComp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The Laplacian at a local minimum

A function of class `C²` on the plane with a local minimum at `x` has nonnegative Laplacian at `x`:
`SandierSerfaty.Analysis.laplacian_nonneg_of_isLocalMin`. This is the elementary core of the strict
minimum principle for functions with `-Δ > 0` (paper proof of
Lemma `geo:separation`).

The proof restricts to lines: for each direction `v` the function `t ↦ f (x + t v)` has a local minimum
at `0`, hence nonnegative second derivative `iteratedFDeriv ℝ 2 f x ![v, v]`
(`SandierSerfaty.Analysis.iteratedFDeriv_two_diag_nonneg_of_isLocalMin`), and `Δ f x` is the sum of
the two coordinate directions.
-/

open Filter Topology Laplacian

public section

namespace SandierSerfaty

namespace Analysis

/-- A real function of one variable with a local minimum at `0` has nonnegative second derivative,
provided it is twice differentiable at `0`. -/
theorem deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0)
    (hmin : IsLocalMin g 0) : 0 ≤ deriv (deriv g) 0 := by
  by_contra hneg
  push Not at hneg
  have hd : deriv g 0 = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax g 0 :=
    isLocalMax_of_deriv_deriv_neg hneg hd hg.continuousAt
  have hconst : ∀ᶠ t in 𝓝 (0 : ℝ), g t = g 0 := by
    filter_upwards [hmin, hmax] with t h1 h2
    exact le_antisymm h2 h1
  have h2 : deriv g =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_eventually_nhds.2 hconst] with t ht
    have : g =ᶠ[𝓝 t] fun _ => g 0 := ht
    simpa using this.deriv_eq
  have : deriv (deriv g) 0 = 0 := by
    have := h2.deriv_eq
    simpa using this
  exact absurd this hneg.ne

/-- The second derivative of `f` in the direction `v` at a local minimum is nonnegative. -/
theorem iteratedFDeriv_two_diag_nonneg_of_isLocalMin {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x)
    (hmin : IsLocalMin f x) (v : ℂ) : 0 ≤ iteratedFDeriv ℝ 2 f x ![v, v] := by
  set ℓ : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hℓ
  have hℓapp : ∀ t : ℝ, ℓ t = t • v := fun t => by simp [hℓ]
  set g : ℝ → ℝ := fun t => f (x + ℓ t) with hg
  have hline : ContDiffAt ℝ 2 (fun t : ℝ => x + ℓ t) 0 := by
    apply contDiffAt_const.add; exact ℓ.contDiff.contDiffAt
  have hgx : ContDiffAt ℝ 2 g 0 := by
    have h0 : (x + ℓ 0) = x := by simp
    refine ContDiffAt.comp (g := f) (f := fun t : ℝ => x + ℓ t) 0 ?_ hline
    rw [h0]; exact hf
  have hgmin : IsLocalMin g 0 := by
    have hcont : ContinuousAt (fun t : ℝ => x + ℓ t) 0 := hline.continuousAt
    have h0 : (x + ℓ 0) = x := by simp
    have : Tendsto (fun t : ℝ => x + ℓ t) (𝓝 0) (𝓝 x) := by
      simpa [h0] using hcont.tendsto
    have h2 := this.eventually hmin
    filter_upwards [h2] with t ht
    simpa [hg] using ht
  have h1 := deriv_deriv_nonneg_of_isLocalMin hgx hgmin
  -- identify the second derivative of `g`
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have := hf.fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)
  have hderivg : ∀ᶠ t in 𝓝 (0 : ℝ), deriv g t = fderiv ℝ f (x + ℓ t) v := by
    have hfdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
      filter_upwards [hf.eventually (by norm_num)] with y hy
      exact hy.differentiableAt (by norm_num)
    have h0 : (x + ℓ 0) = x := by simp
    have hc : ContinuousAt (fun t : ℝ => x + ℓ t) 0 := hline.continuousAt
    have : Tendsto (fun t : ℝ => x + ℓ t) (𝓝 0) (𝓝 x) := by simpa [h0] using hc.tendsto
    filter_upwards [this.eventually hfdiff] with t ht
    have hl : HasDerivAt (fun t : ℝ => x + ℓ t) v t := by
      have := (ℓ.hasFDerivAt (x := t)).const_add x
      simpa [hℓapp] using this.hasDerivAt
    have := (ht.hasFDerivAt.comp_hasDerivAt t hl)
    exact this.deriv
  have hd2 : deriv (deriv g) 0 = iteratedFDeriv ℝ 2 f x ![v, v] := by
    have hev : deriv g =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + ℓ t) v := hderivg
    rw [hev.deriv_eq]
    have h0 : (x + ℓ 0) = x := by simp
    have hl : HasDerivAt (fun t : ℝ => x + ℓ t) v 0 := by
      have := (ℓ.hasFDerivAt (x := 0)).const_add x
      simpa [hℓapp] using this.hasDerivAt
    have hfd' : DifferentiableAt ℝ (fderiv ℝ f) (x + ℓ 0) := by rw [h0]; exact hfd
    have := (hfd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl)
    have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + ℓ t) v)
        (fderiv ℝ (fderiv ℝ f) (x + ℓ 0) v v) 0 := by
      have := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) this
      convert this using 1
      · rfl
      · rfl
    rw [h3.deriv, h0, iteratedFDeriv_two_apply]
    simp
  rw [← hd2]; exact h1

/-- **Second-order necessary condition on the plane**: a `C²` function with a local minimum at `x` has
`0 ≤ Δ f x`. -/
theorem laplacian_nonneg_of_isLocalMin {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x)
    (hmin : IsLocalMin f x) : 0 ≤ Δ f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  exact add_nonneg (iteratedFDeriv_two_diag_nonneg_of_isLocalMin hf hmin 1)
    (iteratedFDeriv_two_diag_nonneg_of_isLocalMin hf hmin Complex.I)


/-- The Laplacian of a `C²` function on the plane is continuous at the point. -/
theorem continuousAt_laplacian {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    ContinuousAt (Δ f) x := by
  have e : Δ f = fun y => iteratedFDeriv ℝ 2 f y ![1, 1] +
      iteratedFDeriv ℝ 2 f y ![Complex.I, Complex.I] := by
    exact InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane f
  rw [e]
  have h := hf.continuousAt_iteratedFDeriv (k := 2) le_rfl
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1, 1]).continuous.continuousAt.comp
    h).add ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ
      ![Complex.I, Complex.I]).continuous.continuousAt.comp h)

/-- The Laplacian of `‖·‖²` on the plane is `4`. -/
theorem laplacian_norm_sq (x : ℂ) : Δ (fun w : ℂ => ‖w‖ ^ 2) x = 4 := by
  set P : ℝ → ℝ := fun t => t ^ 2 with hP
  have hPc : ContDiff ℝ 2 P := by fun_prop
  have e : (fun w : ℂ => ‖w‖ ^ 2) = (P ∘ Complex.reCLM) + (P ∘ Complex.imCLM) := by
    funext w
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hP, sq]
  have h2 : iteratedDeriv 2 P = fun _ => 2 := by
    have h1 : deriv P = fun s => 2 * s := by
      funext s
      have : HasDerivAt P (2 * s) s := by simpa [hP] using hasDerivAt_pow 2 s
      exact this.deriv
    funext t
    rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
    simp
  rw [e, ContDiffAt.laplacian_add (hPc.comp Complex.reCLM.contDiff).contDiffAt
    (hPc.comp Complex.imCLM.contDiff).contDiffAt,
    laplacian_comp_clm _ _ hPc, laplacian_comp_clm _ _ hPc, h2]
  simp
  norm_num

end Analysis

end SandierSerfaty

end
