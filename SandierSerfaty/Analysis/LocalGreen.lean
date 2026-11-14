/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PeriodicGreen
public import SandierSerfaty.Analysis.PolarDivergence

/-!
# Green's identity near a puncture

`SandierSerfaty.Analysis.local_green`: for a cutoff `β` equal to `1` on `B(p, ρ)` and supported in
`B(p, 2ρ)` and `u` of class `C²` off a singular set `S` (with `Δ u = 2π` there), the exterior integral
over `{η ≤ ‖x - p‖}` of `β |∇u|² + u ⟨∇β, ∇u⟩ + 2π β u` equals the boundary term
`-∫ θ, η · u · ∂_r u` on the circle `‖x - p‖ = η`.
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Analysis

theorem local_green {u β : ℂ → ℝ} {p : ℂ} {η ρ : ℝ} {S : Set ℂ}
    (hη : 0 < η) (hηρ : η ≤ ρ)
    (hu : ∀ x, x ∉ S → ContDiffAt ℝ 2 u x) (hΔ : ∀ x, x ∉ S → Δ u x = 2 * Real.pi)
    (hβ : ContDiff ℝ ∞ β) (hβ1 : ∀ x, ‖x - p‖ ≤ ρ → β x = 1)
    (hβ0 : ∀ x, 2 * ρ ≤ ‖x - p‖ → β x = 0)
    (hS : ∀ x ∈ S, x ≠ p → β =ᶠ[𝓝 x] fun _ => 0) :
    ∫ x in {x : ℂ | η ≤ ‖x - p‖},
        (β x * gradSq u x + u x * gradDot β u x + 2 * Real.pi * (β x * u x)) =
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
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet
  rw [← setIntegral_congr_fun hclosed (g := fun x => fderiv ℝ Y₁ x 1 + fderiv ℝ Y₂ x Complex.I) ?_] at key
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
      simp [hY.fderiv_eq, hY'.fderiv_eq, gradDot, hβx, pd_eq_zero_of_eventuallyEq_zero h0, pd₁, pd₂]
    · have := div_green_field (hu x hxS) (hβ'.contDiffAt (x := x))
      rw [hΔ x hxS] at this
      show _ = pd₁ Y₁ x + pd₂ Y₂ x
      rw [this]
      simp only [gradSq, gradDot]
      ring

end Analysis

end SandierSerfaty

end
