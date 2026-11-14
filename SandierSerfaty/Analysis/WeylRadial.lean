/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.WeylCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Compactly supported radial potentials on `ℂ`

For a smooth function `κ : ℝ → ℝ` supported in `[a, b]` with `0 < a` and `∫₀ᵇ κ = 0`, there is a
smooth `G : ℝ → ℝ` vanishing on `[b, ∞)` with `4 s G''(s) + 4 G'(s) = κ(s)` for all `s`
(`Weyl.exists_radialPotential`). Then `ψ(z) = G(‖z - c‖²)` is a smooth, compactly supported function
on `ℂ` with `Δψ(z) = κ(‖z - c‖²)` (`Weyl.exists_radial_lap_eq`). This is the planar potential of a
radial density of total mass zero; it is used to show that the mollification of a weakly harmonic
function does not depend on the scale.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- The primitive `P s = ∫₀ˢ κ`. -/
private theorem hasDerivAt_primitive {κ : ℝ → ℝ} (hκ : Continuous κ) (s : ℝ) :
    HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, κ t) (κ s) s :=
  intervalIntegral.integral_hasDerivAt_right (hκ.intervalIntegrable _ _)
    (hκ.stronglyMeasurableAtFilter _ _) hκ.continuousAt

/-- A smooth `G` with `(4 s G')' = κ`, vanishing for `s ≥ b`. -/
theorem exists_radialPotential {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) {a b : ℝ} (ha : 0 < a)
    (hκa : ∀ s ≤ a, κ s = 0) (hκb : ∀ s, b ≤ s → κ s = 0)
    (hint : ∫ s in (0 : ℝ)..b, κ s = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ (∀ s, b ≤ s → G s = 0) ∧
      ∀ s, 4 * s * deriv (deriv G) s + 4 * deriv G s = κ s := by
  set P : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, κ t with hPdef
  have hPd : ∀ s, HasDerivAt P (κ s) s := hasDerivAt_primitive hκ.continuous
  have hPsmooth : ContDiff ℝ ∞ P := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun s => (hPd s).differentiableAt, ?_⟩
    have : deriv P = κ := funext fun s => (hPd s).deriv
    rw [this]; exact hκ
  have hPa : ∀ s ≤ a, P s = 0 := by
    intro s hs
    simp only [hPdef]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.mem_uIcc] at ht
      exact hκa t (by rcases ht with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith)
  have hPb : ∀ s, b ≤ s → P s = 0 := by
    intro s hs
    simp only [hPdef]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
      (hκ.continuous.intervalIntegrable 0 b) (hκ.continuous.intervalIntegrable b s), hint,
      intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.mem_uIcc] at ht
      exact hκb t (by rcases ht with ⟨h1, _⟩ | ⟨h1, h2⟩ <;> linarith)
  set h : ℝ → ℝ := fun s => P s / (4 * s) with hhdef
  have hh : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      have hev : h =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds ha] with t ht
        simp [hhdef, hPa t (le_of_lt ht)]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact hPsmooth.contDiffAt.div (contDiffAt_const.mul contDiffAt_id) (by simpa using hs)
  have hhb : ∀ s, b ≤ s → h s = 0 := fun s hs => by simp [hhdef, hPb s hs]
  set G : ℝ → ℝ := fun s => ∫ t in b..s, h t with hGdef
  have hGd : ∀ s, HasDerivAt G (h s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hh.continuous.intervalIntegrable _ _)
      (hh.continuous.stronglyMeasurableAtFilter _ _) hh.continuous.continuousAt
  have hGderiv : deriv G = h := funext fun s => (hGd s).deriv
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun s => (hGd s).differentiableAt, by rw [hGderiv]; exact hh⟩
  · intro s hs
    simp only [hGdef]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.mem_uIcc] at ht
      exact hhb t (by rcases ht with ⟨h1, _⟩ | ⟨h1, h2⟩ <;> linarith)
  · intro s
    rw [hGderiv]
    have hhd : HasDerivAt h (deriv h s) s :=
      ((hh.differentiable (by norm_num)) s).hasDerivAt
    have h4 : HasDerivAt (fun t => 4 * id t * h t) (4 * 1 * h s + 4 * id s * deriv h s) s :=
      ((hasDerivAt_id s).const_mul (4 : ℝ)).mul hhd
    have hfun : (fun t => 4 * id t * h t) = P := by
      funext t
      by_cases ht : t = 0
      · subst ht
        simp [hPdef]
      · simp only [id, hhdef]
        field_simp
    rw [hfun] at h4
    have := h4.unique (hPd s)
    simp only [id] at this
    linarith

end SandierSerfaty.Weyl

end
