/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The midpoint rule with its error bound

paper `comp:midpoint`: for a function `Y` with a bounded second derivative on
`[v, u]`,

  `|∫_v^u Y - (u - v) Y((v + u)/2)| ≤ (u - v)³/24 · sup_{[v,u]} |Y''|`.

Mathlib has the trapezoidal rule (`trapezoidal_error_le`) but no midpoint rule; this file proves it.

* `abs_sub_midpoint_le`: the antiderivative form. If `F' = f`, `f' = f₁`, `f₁' = f₂` at every point of
  `[a, b]` (two-sided derivatives, as `Certificate.Jet.JetEncl` supplies them) and `|f₂| ≤ M` there, then
  `|F b - F a - (b - a) f((a + b)/2)| ≤ (b - a)³/24 · M`. No integral appears.
* `abs_integral_sub_midpoint_le`: the integral form, for `f` with two derivatives on an open set containing
  `[a, b]`.

Proof: with `m = (a + b)/2`, `φ(s) = F(m + s) - F(m - s) - 2 s f(m)` has `φ(0) = 0`,
`φ'(s) = f(m + s) + f(m - s) - 2 f(m)` with `φ'(0) = 0` and `φ''(s) = f₁(m + s) - f₁(m - s)`, which is at most
`2 M s` in absolute value by the mean value theorem; two applications of the comparison principle
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` give `|φ'(s)| ≤ M s²` and `|φ(s)| ≤ M s³/3`, and
`s = (b - a)/2` gives the bound.
-/

open Set Filter

public section

namespace SandierSerfaty.Certificate.Table

/-- **The midpoint rule**, antiderivative form: if `F' = f`, `f' = f₁`, `f₁' = f₂` at every point of
`[a, b]` and `|f₂| ≤ M` there, then `|F b - F a - (b - a) f((a + b)/2)| ≤ (b - a)³/24 · M`. -/
theorem abs_sub_midpoint_le {F f f₁ f₂ : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Icc a b, HasDerivAt f₁ (f₂ x) x) (hM : ∀ x ∈ Icc a b, |f₂ x| ≤ M) :
    |F b - F a - (b - a) * f ((a + b) / 2)| ≤ (b - a) ^ 3 / 24 * M := by
  set m := (a + b) / 2 with hm
  set h := (b - a) / 2 with hh
  have h0 : 0 ≤ h := by rw [hh]; linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  -- the points `m ± s` stay in `[a, b]`
  have hp : ∀ s ∈ Icc 0 h, m + s ∈ Icc a b := fun s hs => by
    constructor <;> [skip; skip] <;> (have := hs.1; have := hs.2; rw [hm]; rw [hh] at *; linarith)
  have hn : ∀ s ∈ Icc 0 h, m - s ∈ Icc a b := fun s hs => by
    constructor <;> [skip; skip] <;> (have := hs.1; have := hs.2; rw [hm]; rw [hh] at *; linarith)
  -- derivatives of `s ↦ g(m + s)` and `s ↦ g(m - s)`
  have dP : ∀ {g g' : ℝ → ℝ}, (∀ x ∈ Icc a b, HasDerivAt g (g' x) x) → ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => g (m + s)) (g' (m + s)) s := fun hg s hs => by
    have := (hg (m + s) (hp s hs)).comp s ((hasDerivAt_id s).const_add m)
    simpa [Function.comp_def] using this
  have dN : ∀ {g g' : ℝ → ℝ}, (∀ x ∈ Icc a b, HasDerivAt g (g' x) x) → ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => g (m - s)) (-g' (m - s)) s := fun hg s hs => by
    have := (hg (m - s) (hn s hs)).comp s ((hasDerivAt_id s).const_sub m)
    simpa [Function.comp_def] using this
  -- `χ(s) = f₁(m + s) - f₁(m - s)` is at most `2 M s`
  have hχ : ∀ s ∈ Icc 0 h, |f₁ (m + s) - f₁ (m - s)| ≤ 2 * M * s := by
    intro s hs
    have hconv : Convex ℝ (Icc a b) := convex_Icc a b
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁) (f' := f₂) (C := M)
      (fun x hx => (hf₁ x hx).hasDerivWithinAt) (fun x hx => by simpa using hM x hx) (hn s hs) (hp s hs)
    simp only [Real.norm_eq_abs] at this
    have e : |m + s - (m - s)| = 2 * s := by
      rw [show m + s - (m - s) = 2 * s by ring, abs_of_nonneg (by linarith [hs.1])]
    rw [e] at this
    linarith
  -- `ψ(s) = f(m + s) + f(m - s) - 2 f(m)` is at most `M s²`
  have hψ : ∀ s ∈ Icc 0 h, |f (m + s) + f (m - s) - 2 * f m| ≤ M * s ^ 2 := by
    have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => f (m + s) + f (m - s) - 2 * f m)
        (f₁ (m + s) - f₁ (m - s)) s := fun s hs => by
      have := ((dP hf s hs).add (dN hf s hs)).sub_const (2 * f m)
      simpa [sub_eq_add_neg] using this
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
      (f := fun s => f (m + s) + f (m - s) - 2 * f m) (f' := fun s => f₁ (m + s) - f₁ (m - s))
      (B := fun s => M * s ^ 2) (B' := fun s => 2 * M * s)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp; ring_nf)
      (fun s => by
        have := ((hasDerivAt_pow 2 s).const_mul M)
        convert this using 1; push_cast; ring)
      (fun s hs => by simpa using hχ s (Ico_subset_Icc_self hs))
    intro s hs
    simpa using this hs
  -- `φ(s) = F(m + s) - F(m - s) - 2 s f(m)` is at most `M s³/3`
  have hφ : ∀ s ∈ Icc 0 h, |F (m + s) - F (m - s) - 2 * s * f m| ≤ M * s ^ 3 / 3 := by
    have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => F (m + s) - F (m - s) - 2 * s * f m)
        (f (m + s) + f (m - s) - 2 * f m) s := fun s hs => by
      have h2 : HasDerivAt (fun s : ℝ => 2 * s * f m) (2 * f m) s := by
        simpa using ((hasDerivAt_id s).const_mul 2).mul_const (f m)
      have := ((dP hF s hs).sub (dN hF s hs)).sub h2
      convert this using 1; ring
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
      (f := fun s => F (m + s) - F (m - s) - 2 * s * f m) (f' := fun s => f (m + s) + f (m - s) - 2 * f m)
      (B := fun s => M * s ^ 3 / 3) (B' := fun s => M * s ^ 2)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp)
      (fun s => by
        have := ((hasDerivAt_pow 3 s).const_mul M).div_const 3
        convert this using 1; push_cast; ring)
      (fun s hs => by simpa using hψ s (Ico_subset_Icc_self hs))
    intro s hs
    simpa using this hs
  have key := hφ h ⟨h0, le_rfl⟩
  have e1 : m + h = b := by rw [hm, hh]; ring
  have e2 : m - h = a := by rw [hm, hh]; ring
  rw [e1, e2] at key
  have e3 : 2 * h = b - a := by rw [hh]; ring
  rw [e3] at key
  calc |F b - F a - (b - a) * f ((a + b) / 2)| ≤ M * h ^ 3 / 3 := key
    _ = (b - a) ^ 3 / 24 * M := by rw [hh]; ring

/-- **The midpoint rule**, integral form: if `f' = f₁` and `f₁' = f₂` on an open set `U ⊇ [a, b]` and
`|f₂| ≤ M` on `[a, b]`, then `|∫_a^b f - (b - a) f((a + b)/2)| ≤ (b - a)³/24 · M`. -/
theorem abs_integral_sub_midpoint_le {f f₁ f₂ : ℝ → ℝ} {a b M : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hab : a ≤ b) (hsub : Icc a b ⊆ U) (hf : ∀ x ∈ U, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ U, HasDerivAt f₁ (f₂ x) x) (hM : ∀ x ∈ Icc a b, |f₂ x| ≤ M) :
    |(∫ x in a..b, f x) - (b - a) * f ((a + b) / 2)| ≤ (b - a) ^ 3 / 24 * M := by
  have hcont : ContinuousOn f U := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hint : ∀ x ∈ Icc a b, IntervalIntegrable f MeasureTheory.volume a x := fun x hx =>
    (hcont.mono (fun y hy => hsub ?_)).intervalIntegrable
  · have hF : ∀ x ∈ Icc a b, HasDerivAt (fun u => ∫ y in a..u, f y) (f x) x := fun x hx =>
      intervalIntegral.integral_hasDerivAt_right (hint x hx)
        (hcont.stronglyMeasurableAtFilter hU x (hsub hx)) (hf x (hsub hx)).continuousAt
    have := abs_sub_midpoint_le hab hF (fun x hx => hf x (hsub hx)) (fun x hx => hf₁ x (hsub hx)) hM
    simpa using this
  · rw [uIcc_of_le hx.1] at hy
    exact ⟨hy.1, hy.2.trans hx.2⟩

end SandierSerfaty.Certificate.Table
