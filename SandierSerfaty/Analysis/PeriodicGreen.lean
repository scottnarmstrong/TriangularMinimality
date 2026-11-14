/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.GreenIdentity
public import SandierSerfaty.Analysis.PeriodicIntegral

/-!
# Green's identity on the periodic cell, away from the singular set

`SandierSerfaty.Analysis.periodic_green`: let `u` be `Γ`-periodic, `C²` off a set `S`, with
`Δ u = 2π` off `S`, and let `φ` be a `C¹` periodic cutoff vanishing near `S`. Then
`∫_D (φ |∇u|² + u ⟨∇φ, ∇u⟩ + 2π φ u) = 0`.
This is the divergence theorem for the periodic field `φ u ∇u`, with no boundary terms
(`SandierSerfaty.Torus.integral_torusDomain_fderiv`).
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Analysis

/-- `|∇u|²`. -/
@[expose] noncomputable def gradSq (u : ℂ → ℝ) (x : ℂ) : ℝ := pd₁ u x ^ 2 + pd₂ u x ^ 2

/-- `⟨∇φ, ∇u⟩`. -/
@[expose] noncomputable def gradDot (φ u : ℂ → ℝ) (x : ℂ) : ℝ :=
  pd₁ φ x * pd₁ u x + pd₂ φ x * pd₂ u x

theorem contDiffAt_pd {u : ℂ → ℝ} {x : ℂ} {n : ℕ} (hu : ContDiffAt ℝ (n + 1) u x) (v : ℂ) :
    ContDiffAt ℝ n (fun y => fderiv ℝ u y v) x := by
  have : ContDiffAt ℝ n (fderiv ℝ u) x := hu.fderiv_right (by norm_cast)
  exact this.clm_apply contDiffAt_const

theorem pd_eq_zero_of_eventuallyEq_zero {φ : ℂ → ℝ} {x : ℂ} (h : φ =ᶠ[𝓝 x] fun _ => 0) (v : ℂ) :
    fderiv ℝ φ x v = 0 := by
  rw [h.fderiv_eq]; simp

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- **Green's identity on the periodic cell.** -/
theorem periodic_green {u φ : ℂ → ℝ} {S : Set ℂ}
    (huper : ∀ γ ∈ Γ, ∀ x, u (x + γ) = u x)
    (hu : ∀ x, x ∉ S → ContDiffAt ℝ 2 u x) (hΔ : ∀ x, x ∉ S → Δ u x = 2 * Real.pi)
    (hφ : ContDiff ℝ 1 φ) (hφper : ∀ γ ∈ Γ, ∀ x, φ (x + γ) = φ x)
    (hvan : ∀ x ∈ S, φ =ᶠ[𝓝 x] fun _ => 0) :
    ∫ x in torusDomain Γ, (φ x * gradSq u x + u x * gradDot φ u x + 2 * Real.pi * (φ x * u x)) = 0 := by
  set Y₁ : ℂ → ℝ := fun y => φ y * u y * pd₁ u y with hY₁
  set Y₂ : ℂ → ℝ := fun y => φ y * u y * pd₂ u y with hY₂
  -- regularity of the field
  have hreg : ∀ (v : ℂ) (x : ℂ), ContDiffAt ℝ 1 (fun y => φ y * u y * fderiv ℝ u y v) x := by
    intro v x
    by_cases hx : x ∈ S
    · have h0 := hvan x hx
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy
      simp [hy]
    · have h2 := hu x hx
      have h1 : ContDiffAt ℝ 1 u x := h2.of_le (by norm_num)
      exact (hφ.contDiffAt.mul h1).mul (contDiffAt_pd (n := 1) h2 v)
  have hY₁c : ContDiff ℝ 1 Y₁ := contDiff_iff_contDiffAt.2 (hreg 1)
  have hY₂c : ContDiff ℝ 1 Y₂ := contDiff_iff_contDiffAt.2 (hreg Complex.I)
  -- periodicity
  have hpdper : ∀ (f : ℂ → ℝ), (∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) → ∀ γ ∈ Γ, ∀ x, ∀ v,
      fderiv ℝ f (x + γ) v = fderiv ℝ f x v := fun f hf γ hγ x v => by
    rw [Torus.fderiv_periodic Γ hf hγ]
  have hY₁per : ∀ γ ∈ Γ, ∀ x, Y₁ (x + γ) = Y₁ x := fun γ hγ x => by
    simp only [hY₁, pd₁, hφper γ hγ, huper γ hγ, hpdper u huper γ hγ x 1]
  have hY₂per : ∀ γ ∈ Γ, ∀ x, Y₂ (x + γ) = Y₂ x := fun γ hγ x => by
    simp only [hY₂, pd₂, hφper γ hγ, huper γ hγ, hpdper u huper γ hγ x Complex.I]
  -- pointwise divergence
  have hdiv : ∀ x, pd₁ Y₁ x + pd₂ Y₂ x =
      φ x * gradSq u x + u x * gradDot φ u x + 2 * Real.pi * (φ x * u x) := by
    intro x
    by_cases hx : x ∈ S
    · have h0 := hvan x hx
      have hφx : φ x = 0 := h0.self_of_nhds
      have hY : Y₁ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0] with y hy; simp [hY₁, hy]
      have hY' : Y₂ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0] with y hy; simp [hY₂, hy]
      simp [pd₁, pd₂, hY.fderiv_eq, hY'.fderiv_eq, gradDot, hφx,
        pd_eq_zero_of_eventuallyEq_zero h0, pd₁, pd₂]
    · have := div_green_field (hu x hx) (hφ.contDiffAt (x := x))
      rw [hΔ x hx] at this
      simp only [hY₁, hY₂] at *
      rw [this]
      simp only [gradSq, gradDot]
      ring
  -- integrate
  have hint : ∀ (Y : ℂ → ℝ) (hY : ContDiff ℝ 1 Y) (hYp : ∀ γ ∈ Γ, ∀ x, Y (x + γ) = Y x) (v : ℂ),
      IntegrableOn (fun x => fderiv ℝ Y x v) (torusDomain Γ) := by
    intro Y hY hYp v
    refine Torus.integrableOn_torusDomain_of_periodic Γ
      ((hY.continuous_fderiv one_ne_zero).clm_apply continuous_const) fun γ hγ x => ?_
    rw [Torus.fderiv_periodic Γ hYp hγ]
  have e1 := Torus.integral_torusDomain_fderiv Γ hY₁c hY₁per 1
  have e2 := Torus.integral_torusDomain_fderiv Γ hY₂c hY₂per Complex.I
  simp_rw [← hdiv]
  have hsplit := integral_add (hint Y₁ hY₁c hY₁per 1) (hint Y₂ hY₂c hY₂per Complex.I)
  simp only [pd₁, pd₂]
  rw [hsplit, e1, e2, add_zero]

end Analysis

end SandierSerfaty

end
