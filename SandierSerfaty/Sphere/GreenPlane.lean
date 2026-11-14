/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.LocalGreen
public import SandierSerfaty.Analysis.GreenRegularity
public import SandierSerfaty.Analysis.PunctureAsymptotics
public import SandierSerfaty.Analysis.WeylCalculus

/-!
# Green's identity on the plane with a variable Laplacian

Generalizations of `Analysis.local_green` (constant Laplacian `2π`) and `Analysis.periodic_green`
(periodic cell) to the plane `ℂ` and a prescribed Laplacian `Δ u = L` off a singular set:

* `Sphere.local_green_var`: the exterior of a disc about a puncture `p`, for a cutoff `β` equal to `1`
  near `p`;
* `Sphere.plane_green`: `∫_ℂ (φ |∇u|² + u ⟨∇φ, ∇u⟩ + φ u L) = 0` for `φ` of class `C¹` with compact
  support vanishing near the singular set (no boundary term).
-/

open MeasureTheory Filter Topology Laplacian SandierSerfaty.Analysis
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

/-- **Local Green identity with a variable Laplacian.** -/
theorem local_green_var {u β L : ℂ → ℝ} {p : ℂ} {η ρ : ℝ} {S : Set ℂ}
    (hη : 0 < η) (hηρ : η ≤ ρ)
    (hu : ∀ x, x ∉ S → ContDiffAt ℝ 2 u x) (hΔ : ∀ x, x ∉ S → Δ u x = L x)
    (hβ : ContDiff ℝ ∞ β) (hβ1 : ∀ x, ‖x - p‖ ≤ ρ → β x = 1)
    (hβ0 : ∀ x, 2 * ρ ≤ ‖x - p‖ → β x = 0)
    (hS : ∀ x ∈ S, x ≠ p → β =ᶠ[𝓝 x] fun _ => 0) :
    ∫ x in {x : ℂ | η ≤ ‖x - p‖},
        (β x * gradSq u x + u x * gradDot β u x + β x * u x * L x) =
      -∫ θ in (-Real.pi)..Real.pi,
        η * (u (p + polarPt η θ) *
          (Real.cos θ * pd₁ u (p + polarPt η θ) + Real.sin θ * pd₂ u (p + polarPt η θ))) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hη hηρ
  have hβ' : ContDiff ℝ 1 β := hβ.of_le (by norm_cast)
  set Y₁ : ℂ → ℝ := fun y => β y * u y * pd₁ u y with hY₁
  set Y₂ : ℂ → ℝ := fun y => β y * u y * pd₂ u y with hY₂
  have hreg : ∀ (v : ℂ) (x : ℂ), x ≠ p →
      ContDiffAt ℝ 1 (fun y => β y * u y * fderiv ℝ u y v) x := by
    intro v x hxp
    by_cases hx : x ∈ S
    · have h0 := hS x hx hxp
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy
      simp [hy]
    · have h2 := hu x hx
      have h1 : ContDiffAt ℝ 1 u x := h2.of_le (by norm_num)
      exact (hβ'.contDiffAt.mul h1).mul (contDiffAt_pd (n := 1) h2 v)
  have key := integral_exterior_div (Y₁ := Y₁) (Y₂ := Y₂) (p := p) (η := η) (R := 2 * ρ) hη
    (by linarith) (fun x hx => hreg 1 x hx) (fun x hx => hreg Complex.I x hx)
    (fun x hx => by simp [hY₁, hY₂, hβ0 x hx])
  have hclosed : MeasurableSet {x : ℂ | η ≤ ‖x - p‖} :=
    (isClosed_le continuous_const
      (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet
  rw [← setIntegral_congr_fun hclosed (g := fun x => fderiv ℝ Y₁ x 1 + fderiv ℝ Y₂ x Complex.I) ?_]
    at key
  · rw [key]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hn : ‖polarPt η θ‖ = η := norm_polarPt hη.le θ
    have : β (p + polarPt η θ) = 1 := hβ1 _ (by simpa [hn] using hηρ)
    simp only [hY₁, hY₂, this, pd₁, pd₂]
    ring
  · intro x hx
    have hxp : x ≠ p := by
      have hx' : η ≤ ‖x - p‖ := hx
      intro h; rw [h, sub_self, norm_zero] at hx'
      exact absurd hx' (not_le.2 hη)
    by_cases hxS : x ∈ S
    · have h0 := hS x hxS hxp
      have hβx : β x = 0 := h0.self_of_nhds
      have hY : Y₁ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0] with y hy; simp [hY₁, hy]
      have hY' : Y₂ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0] with y hy; simp [hY₂, hy]
      simp [hY.fderiv_eq, hY'.fderiv_eq, gradDot, hβx, pd_eq_zero_of_eventuallyEq_zero h0, pd₁,
        pd₂]
    · have := div_green_field (hu x hxS) (hβ'.contDiffAt (x := x))
      rw [hΔ x hxS] at this
      show _ = pd₁ Y₁ x + pd₂ Y₂ x
      rw [this]
      simp only [gradSq, gradDot]

/-- The integral of a partial derivative of a `C¹` function of compact support vanishes. -/
theorem integral_fderiv_apply_eq_zero {Y : ℂ → ℝ} (hY : ContDiff ℝ 1 Y) (hc : HasCompactSupport Y)
    (v : ℂ) : ∫ x, fderiv ℝ Y x v = 0 := by
  have h := Weyl.integral_mul_pd_eq_neg (f := fun _ => (1 : ℝ)) (g := Y) (W := Set.univ)
    (K := tsupport Y) hc (Set.subset_univ _) isOpen_univ
    contDiffOn_const hY (fun x hx => image_eq_zero_of_notMem_tsupport hx) v
  simpa [Weyl.pd] using h

/-- **Green's identity on the plane** for a compactly supported cutoff vanishing near the singular
set: `∫_ℂ (φ |∇u|² + u ⟨∇φ, ∇u⟩ + φ u L) = 0`. -/
theorem plane_green {u φ L : ℂ → ℝ} {S : Set ℂ}
    (hu : ∀ x, x ∉ S → ContDiffAt ℝ 2 u x) (hΔ : ∀ x, x ∉ S → Δ u x = L x)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hvan : ∀ x ∈ S, φ =ᶠ[𝓝 x] fun _ => 0) :
    ∫ x, (φ x * gradSq u x + u x * gradDot φ u x + φ x * u x * L x) = 0 := by
  set Y₁ : ℂ → ℝ := fun y => φ y * u y * pd₁ u y with hY₁
  set Y₂ : ℂ → ℝ := fun y => φ y * u y * pd₂ u y with hY₂
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
  have hsupp : ∀ (g : ℂ → ℝ), HasCompactSupport (fun y => φ y * g y) :=
    fun g => hφc.mul_right
  have hcs₁ : HasCompactSupport Y₁ := by
    show HasCompactSupport (fun y => φ y * u y * pd₁ u y)
    exact (hφc.mul_right).mul_right
  have hcs₂ : HasCompactSupport Y₂ := by
    show HasCompactSupport (fun y => φ y * u y * pd₂ u y)
    exact (hφc.mul_right).mul_right
  have hdiv : ∀ x, pd₁ Y₁ x + pd₂ Y₂ x =
      φ x * gradSq u x + u x * gradDot φ u x + φ x * u x * L x := by
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
  have e1 := integral_fderiv_apply_eq_zero hY₁c hcs₁ 1
  have e2 := integral_fderiv_apply_eq_zero hY₂c hcs₂ Complex.I
  have hi : ∀ (Y : ℂ → ℝ) (hY : ContDiff ℝ 1 Y) (hc : HasCompactSupport Y) (v : ℂ),
      Integrable (fun x => fderiv ℝ Y x v) := fun Y hY hc v =>
    ((hY.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  simp_rw [← hdiv]
  have hsplit := integral_add (hi Y₁ hY₁c hcs₁ 1) (hi Y₂ hY₂c hcs₂ Complex.I)
  simp only [pd₁, pd₂]
  rw [hsplit, e1, e2, add_zero]

end Sphere

end SandierSerfaty

end
