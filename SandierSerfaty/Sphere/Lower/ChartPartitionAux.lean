/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.TruncIntegrable
public import SandierSerfaty.Sphere.Lower.GoodSquare
public import SandierSerfaty.Sphere.Lower.ChartLower

/-!
# Comparing the chart truncation with `H_{1/4}` away from the boundary (aux. for the partition lemma)

For `D = B(0, ρ)` and `Z = innerBlown X ρ`: on `B(0, ρ - 3/4)` the depth-truncated potential
`H - ∑_{p∈Z} f_{α_p}(· - p)` agrees (off the points) with `truncPot X (1/4)`, hence also their gradients, and the
Dirichlet integrals over squares inside `closedBall 0 (ρ - 1)` agree.
-/

open MeasureTheory Set Filter Topology Laplacian Metric
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem gradient_eq_gradC (f : ℂ → ℝ) (x : ℂ) : gradient f x = gradC f x := by
  have h : ∀ v : ℂ, inner ℝ (gradient f x) v = fderiv ℝ f x v := fun v => by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  apply Complex.ext
  · rw [gradC_re]
    have := h 1
    rw [Complex.inner, one_mul] at this
    simpa using this
  · rw [gradC_im]
    have := h Complex.I
    rw [Complex.inner] at this
    simpa [Complex.mul_re] using this

theorem truncLog_depth_eq_quarter {ρ : ℝ} {p y : ℂ} (hp : ‖p‖ < ρ) (hy : ‖y‖ < ρ - 3 / 4) :
    truncLog (depthRadius ρ p) (y - p) = truncLog (1 / 4) (y - p) := by
  have hα := depthRadius_pos hp
  by_cases h : 1 / 4 ≤ ‖y - p‖
  · rw [Screening.truncLog_eq_zero hα ((depthRadius_le_quarter ρ p).trans h),
      Screening.truncLog_eq_zero (by norm_num) h]
  · rw [not_le] at h
    have h1 : ‖p‖ < ρ - 1 / 2 := by
      have := norm_le_norm_add_norm_sub' p y
      have h3 : ‖p‖ ≤ ‖y‖ + ‖y - p‖ := by
        calc ‖p‖ = ‖y - (y - p)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖y‖ + ‖y - p‖ := norm_sub_le _ _
      linarith
    have : depthRadius ρ p = 1 / 4 := by
      unfold depthRadius
      exact min_eq_left (by linarith)
    rw [this]

theorem truncLog_quarter_far {ρ : ℝ} {z y : ℂ} (hz : ρ ≤ ‖z‖) (hy : ‖y‖ < ρ - 3 / 4) :
    truncLog (1 / 4) (y - z) = 0 := by
  refine Screening.truncLog_eq_zero (by norm_num) ?_
  have : ‖z‖ ≤ ‖y‖ + ‖y - z‖ := by
    calc ‖z‖ = ‖y - (y - z)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖y‖ + ‖y - z‖ := norm_sub_le _ _
  linarith

theorem trunc_eq_truncPot {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {ρ : ℝ} {y : ℂ}
    (hy : ‖y‖ < ρ - 3 / 4) (hyz : ∀ i, y ≠ blowupScale n • X i) :
    blowupPot X y - ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p) = truncPot X (1 / 4) y := by
  have h1 := truncPot_eq hn X (η := 1 / 4) (by norm_num) hyz
  rw [h1]
  congr 1
  unfold innerBlown
  rw [Finset.sum_image (fun i _ j _ h => hinj h)]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
    (fun i => ‖blowupScale n • X i‖ < ρ) (fun i => truncLog (1 / 4) (y - blowupScale n • X i))
  rw [← hsplit, Finset.sum_eq_zero (s := Finset.univ.filter fun i => ¬ ‖blowupScale n • X i‖ < ρ),
    add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    exact truncLog_depth_eq_quarter (Finset.mem_filter.1 hi).2 hy
  · intro i hi
    exact truncLog_quarter_far (not_lt.1 (Finset.mem_filter.1 hi).2) hy

theorem gradient_trunc_eq {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {ρ : ℝ} {x : ℂ}
    (hx : ‖x‖ < ρ - 3 / 4) (hxz : ∀ i, x ≠ blowupScale n • X i) :
    gradient (fun y => blowupPot X y - ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) x =
      gradC (truncPot X (1 / 4)) x := by
  rw [← gradient_eq_gradC]
  have hopen : IsOpen ({y : ℂ | ‖y‖ < ρ - 3 / 4} ∩ ⋂ i, {y : ℂ | y ≠ blowupScale n • X i}) :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_iInter_of_finite fun i => isOpen_ne)
  have hev : (fun y => blowupPot X y - ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) =ᶠ[𝓝 x]
      truncPot X (1 / 4) := by
    filter_upwards [hopen.mem_nhds ⟨hx, Set.mem_iInter.2 hxz⟩] with y hy
    exact trunc_eq_truncPot hn X hinj hy.1 (fun i => Set.mem_iInter.1 hy.2 i)
  exact Screening.gradient_congr_nhds hev

theorem ae_sq_trunc_eq {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {ρ : ℝ} {Ω : Set ℂ}
    (hΩm : MeasurableSet Ω) (hQ : ∀ x ∈ Ω, ‖x‖ ≤ ρ - 1) :
    ∀ᵐ x ∂(volume.restrict Ω), ‖gradient (fun y => blowupPot X y -
      ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2 =
      ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 := by
  refine (ae_restrict_iff' hΩm).2 ?_
  filter_upwards [(Set.countable_range fun i => blowupScale n • X i).ae_notMem (volume : Measure ℂ)]
    with x hx hxQ
  have hxz : ∀ i, x ≠ blowupScale n • X i := fun i h => hx ⟨i, h.symm⟩
  rw [gradient_trunc_eq hn X hinj (by linarith [hQ x hxQ]) hxz]

theorem integral_sq_trunc_eq {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {ρ : ℝ} {Ω : Set ℂ}
    (hΩm : MeasurableSet Ω) (hQ : ∀ x ∈ Ω, ‖x‖ ≤ ρ - 1) :
    ∫ x in Ω, ‖gradient (fun y => blowupPot X y -
      ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2 =
      ∫ x in Ω, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 :=
  integral_congr_ae (ae_sq_trunc_eq hn X hinj hΩm hQ)

end Lower

end Sphere

end SandierSerfaty

end
