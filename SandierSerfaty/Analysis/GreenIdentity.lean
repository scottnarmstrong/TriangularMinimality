/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Pointwise Green identity on `ℂ`

With `∂₁ f x = fderiv ℝ f x 1` and `∂₂ f x = fderiv ℝ f x I`:

* `norm_gradient_sq`: `‖gradient f x‖² = (∂₁ f x)² + (∂₂ f x)²`;
* `laplacian_eq_pd`: `Δ f x = ∂₁ ∂₁ f x + ∂₂ ∂₂ f x` for `f` of class `C²` at `x`;
* `div_green_field`: the divergence of the field `φ u ∇u` is
  `φ |∇u|² + u ⟨∇φ, ∇u⟩ + φ u Δu`.
-/

open Laplacian

public section

namespace SandierSerfaty

namespace Analysis

/-- The first partial derivative on `ℂ ≅ ℝ²`. -/
@[expose] noncomputable def pd₁ (f : ℂ → ℝ) (x : ℂ) : ℝ := fderiv ℝ f x 1

/-- The second partial derivative on `ℂ ≅ ℝ²`. -/
@[expose] noncomputable def pd₂ (f : ℂ → ℝ) (x : ℂ) : ℝ := fderiv ℝ f x Complex.I

theorem gradient_re (f : ℂ → ℝ) (x : ℂ) : (gradient f x).re = pd₁ f x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℂ) (x := (1 : ℂ))
    (y := fderiv ℝ f x)
  unfold gradient pd₁
  rw [← h, Complex.inner]
  simp

theorem gradient_im (f : ℂ → ℝ) (x : ℂ) : (gradient f x).im = pd₂ f x := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := ℂ) (x := Complex.I)
    (y := fderiv ℝ f x)
  unfold gradient pd₂
  rw [← h, Complex.inner]
  simp

theorem norm_gradient_sq (f : ℂ → ℝ) (x : ℂ) :
    ‖gradient f x‖ ^ 2 = pd₁ f x ^ 2 + pd₂ f x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, ← gradient_re, ← gradient_im]
  ring

theorem fderiv_fderiv_apply {u : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) (v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ u y v) x w = fderiv ℝ (fderiv ℝ u) x w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have := fderiv_clm_apply hd (differentiableAt_const v)
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add] at this
  rw [this]
  rfl

theorem laplacian_eq_pd {u : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) :
    Δ u x = pd₁ (pd₁ u) x + pd₂ (pd₂ u) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have e1 : pd₁ u = fun y => fderiv ℝ u y 1 := rfl
  have e2 : pd₂ u = fun y => fderiv ℝ u y Complex.I := rfl
  simp only [iteratedFDeriv_two_apply, e1, e2, pd₁, pd₂]
  rw [fderiv_fderiv_apply hu, fderiv_fderiv_apply hu]
  simp

theorem differentiableAt_pd {u : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) (v : ℂ) :
    DifferentiableAt ℝ (fun y => fderiv ℝ u y v) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact hd.clm_apply (differentiableAt_const v)

theorem fderiv_field_apply {u φ : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) (hφ : ContDiffAt ℝ 1 φ x)
    (v : ℂ) :
    fderiv ℝ (fun y => φ y * u y * fderiv ℝ u y v) x v =
      φ x * u x * fderiv ℝ (fun y => fderiv ℝ u y v) x v +
        fderiv ℝ u x v * (φ x * fderiv ℝ u x v + u x * fderiv ℝ φ x v) := by
  have h1 : DifferentiableAt ℝ φ x := hφ.differentiableAt one_ne_zero
  have h2 : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have h3 := differentiableAt_pd hu v
  have h12 : DifferentiableAt ℝ (fun y => φ y * u y) x := h1.mul h2
  rw [fderiv_fun_mul h12 h3, fderiv_fun_mul h1 h2]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- The divergence of the field `φ u ∇u`. -/
theorem div_green_field {u φ : ℂ → ℝ} {x : ℂ} (hu : ContDiffAt ℝ 2 u x) (hφ : ContDiffAt ℝ 1 φ x) :
    pd₁ (fun y => φ y * u y * pd₁ u y) x + pd₂ (fun y => φ y * u y * pd₂ u y) x =
      φ x * (pd₁ u x ^ 2 + pd₂ u x ^ 2) + u x * (pd₁ φ x * pd₁ u x + pd₂ φ x * pd₂ u x) +
        φ x * u x * Δ u x := by
  rw [laplacian_eq_pd hu]
  have e1 : pd₁ u = fun y => fderiv ℝ u y 1 := rfl
  have e2 : pd₂ u = fun y => fderiv ℝ u y Complex.I := rfl
  simp only [e1, e2, pd₁, pd₂]
  rw [fderiv_field_apply hu hφ, fderiv_field_apply hu hφ]
  ring

end Analysis

end SandierSerfaty

end
