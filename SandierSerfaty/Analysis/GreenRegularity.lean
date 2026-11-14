/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PeriodicGreen
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Regularity of the Green integrands away from the singular set

For `u` of class `C²` off a set `S` and a smooth `φ` that vanishes near every point of `S` that it
is evaluated at, the three integrands of Green's identity
`φ |∇u|²`, `u ⟨∇φ, ∇u⟩`, `φ u` are `C¹` at that point
(`SandierSerfaty.Analysis.contDiffAt_green_pieces`), hence integrable when compactly supported
(`SandierSerfaty.Analysis.integrableOn_exterior_of_zero`).
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Analysis

/-- If `φ` vanishes near `x`, then so does `pd₁ φ`-type data. -/
theorem pd_eventuallyEq_zero {φ : ℂ → ℝ} {x : ℂ} (h : φ =ᶠ[𝓝 x] fun _ => 0) (v : ℂ) :
    (fun y => fderiv ℝ φ y v) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  rw [hy.fderiv_eq]; simp

/-- The Green integrands are `C¹` at points where `u` is `C²` or `φ` vanishes nearby. -/
theorem contDiffAt_green_pieces {u φ : ℂ → ℝ} {x : ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hx : ContDiffAt ℝ 2 u x ∨ φ =ᶠ[𝓝 x] fun _ => 0) :
    ContDiffAt ℝ 1 (fun y => φ y * gradSq u y) x ∧
      ContDiffAt ℝ 1 (fun y => u y * gradDot φ u y) x ∧
      ContDiffAt ℝ 1 (fun y => φ y * u y) x := by
  rcases hx with hu | h0
  · have h1 : ContDiffAt ℝ 1 u x := hu.of_le (by norm_num)
    have hφ1 : ContDiffAt ℝ 1 φ x := (hφ.of_le (by norm_cast)).contDiffAt
    have hpu : ∀ v, ContDiffAt ℝ 1 (fun y => fderiv ℝ u y v) x := fun v => contDiffAt_pd (n := 1) hu v
    have hpφ : ∀ v, ContDiffAt ℝ 1 (fun y => fderiv ℝ φ y v) x := fun v =>
      contDiffAt_pd (n := 1) (hφ.contDiffAt.of_le (by norm_cast)) v
    refine ⟨?_, ?_, hφ1.mul h1⟩
    · unfold gradSq pd₁ pd₂
      exact hφ1.mul (((hpu 1).pow 2).add ((hpu Complex.I).pow 2))
    · unfold gradDot pd₁ pd₂
      exact h1.mul (((hpφ 1).mul (hpu 1)).add ((hpφ Complex.I).mul (hpu Complex.I)))
  · have h1 : ContDiffAt ℝ 1 (fun y => φ y * gradSq u y) x := by
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy; simp [hy]
    have h3 : ContDiffAt ℝ 1 (fun y => φ y * u y) x := by
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy; simp [hy]
    have h2 : ContDiffAt ℝ 1 (fun y => u y * gradDot φ u y) x := by
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0, pd_eventuallyEq_zero h0 1, pd_eventuallyEq_zero h0 Complex.I] with y hy hy1 hy2
      simp [gradDot, pd₁, pd₂, hy1, hy2]
    exact ⟨h1, h2, h3⟩

theorem pd_eventuallyEq_zero_of_const {φ : ℂ → ℝ} {x : ℂ} {c : ℝ} (h : φ =ᶠ[𝓝 x] fun _ => c) (v : ℂ) :
    (fun y => fderiv ℝ φ y v) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  rw [hy.fderiv_eq]; simp

/-- The middle Green integrand `u ⟨∇φ, ∇u⟩` is `C¹` where `u` is `C²` or `∇φ` vanishes nearby. -/
theorem contDiffAt_green_piece₂ {u φ : ℂ → ℝ} {x : ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hx : ContDiffAt ℝ 2 u x ∨ ∀ v, (fun y => fderiv ℝ φ y v) =ᶠ[𝓝 x] fun _ => 0) :
    ContDiffAt ℝ 1 (fun y => u y * gradDot φ u y) x := by
  rcases hx with hu | h0
  · exact (contDiffAt_green_pieces (φ := φ) hφ (Or.inl hu)).2.1
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [h0 1, h0 Complex.I] with y hy1 hy2
    simp [gradDot, pd₁, pd₂, hy1, hy2]


/-- A function continuous on `{η ≤ ‖x - p‖}` and vanishing for `‖x - p‖ ≥ R` is integrable there. -/
theorem integrableOn_exterior_of_zero {f : ℂ → ℝ} {p : ℂ} {η R : ℝ} (_hη : 0 < η)
    (hcont : ∀ x, η ≤ ‖x - p‖ → ContinuousAt f x) (hzero : ∀ x, R ≤ ‖x - p‖ → f x = 0) :
    IntegrableOn f {x : ℂ | η ≤ ‖x - p‖} := by
  have hclosed : IsClosed {x : ℂ | η ≤ ‖x - p‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have hK : IsCompact ({x : ℂ | η ≤ ‖x - p‖} ∩ Metric.closedBall p R) :=
    (isCompact_closedBall p R).inter_left hclosed
  have hint : IntegrableOn f ({x : ℂ | η ≤ ‖x - p‖} ∩ Metric.closedBall p R) :=
    ContinuousOn.integrableOn_compact hK fun x hx => (hcont x hx.1).continuousWithinAt
  refine IntegrableOn.of_forall_sdiff_eq_zero hint hclosed.measurableSet fun x hx => ?_
  apply hzero
  by_contra hlt
  rw [not_le] at hlt
  exact hx.2 ⟨hx.1, by simpa [dist_eq_norm] using hlt.le⟩

end Analysis

end SandierSerfaty

end
