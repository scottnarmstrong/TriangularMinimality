/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# One-sided Taylor bounds from a cell endpoint

The query layer approximates the radial functions `f̃₀` and `ẽ` on a table cell `[a, b]` by their first-order
Taylor polynomial at the right node `b` (the node tuple stores the value
and the derivative at `b` with tiny radii, the cell tuple a bound `M` of the second derivative).

* `abs_deriv_sub_le`: `|F₁ t - F₁ b| ≤ M |t - b|`;
* `abs_taylor_le`: `|F t - F b - F₁ b (t - b)| ≤ M (b - t)² / 2`.

As in `SandierSerfaty.Certificate.Table.Midpoint`, the derivatives are two-sided derivative witnesses at the
points of the closed cell (the shape in which `Certificate.Table.TupEncl` supplies them); no `iteratedDeriv`.
-/

open Set Filter

public section

namespace SandierSerfaty.Certificate.Query

/-- **First derivative is Lipschitz.** If `F₁' = F₂` on `[a, b]` and `|F₂| ≤ M` there, then
`|F₁ t - F₁ b| ≤ M |t - b|` for `t ∈ [a, b]`. -/
theorem abs_deriv_sub_le {F₁ F₂ : ℝ → ℝ} {a b M : ℝ} (hF₁ : ∀ x ∈ Icc a b, HasDerivAt F₁ (F₂ x) x)
    (hM : ∀ x ∈ Icc a b, |F₂ x| ≤ M) {t : ℝ} (ht : t ∈ Icc a b) (hb : b ∈ Icc a b) :
    |F₁ t - F₁ b| ≤ M * |t - b| := by
  have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le (f := F₁) (f' := F₂) (C := M)
    (fun x hx => (hF₁ x hx).hasDerivWithinAt) (fun x hx => by simpa using hM x hx) hb ht
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- **First-order Taylor bound at the right endpoint.** If `F' = F₁` and `F₁' = F₂` at every point of
`[a, b]` and `|F₂| ≤ M` there, then `|F t - F b - F₁ b (t - b)| ≤ M (b - t)² / 2` for `t ∈ [a, b]`. -/
theorem abs_taylor_le {F F₁ F₂ : ℝ → ℝ} {a b M : ℝ} (hF : ∀ x ∈ Icc a b, HasDerivAt F (F₁ x) x)
    (hF₁ : ∀ x ∈ Icc a b, HasDerivAt F₁ (F₂ x) x) (hM : ∀ x ∈ Icc a b, |F₂ x| ≤ M) {t : ℝ}
    (ht : t ∈ Icc a b) : |F t - F b - F₁ b * (t - b)| ≤ M * (b - t) ^ 2 / 2 := by
  have hbI : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  set h := b - t with hh
  have h0 : 0 ≤ h := by rw [hh]; linarith [ht.2]
  have hp : ∀ s ∈ Icc 0 h, b - s ∈ Icc a b := fun s hs =>
    ⟨by have := hs.2; rw [hh] at this; linarith [ht.1], by linarith [hs.1]⟩
  have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => F (b - s) - F b + F₁ b * s) (-F₁ (b - s) + F₁ b) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => F (b - s)) (-F₁ (b - s)) s := by
      have := HasDerivAt.comp s (hF (b - s) (hp s hs)) ((hasDerivAt_id s).const_sub b)
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun s : ℝ => F₁ b * s) (F₁ b) s := by
      simpa using (hasDerivAt_id s).const_mul (F₁ b)
    have h3 := (h1.sub_const (F b)).add h2
    exact h3
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
    (f := fun s => F (b - s) - F b + F₁ b * s) (f' := fun s => -F₁ (b - s) + F₁ b)
    (B := fun s => M * s ^ 2 / 2) (B' := fun s => M * s)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp)
    (fun s => by
      have := ((hasDerivAt_pow 2 s).const_mul M).div_const 2
      convert this using 1; push_cast; ring)
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have := abs_deriv_sub_le hF₁ hM (hp s hs') hbI
      have e : |b - s - b| = s := by rw [show b - s - b = -s by ring, abs_neg, abs_of_nonneg hs.1]
      rw [e] at this
      simp only [Real.norm_eq_abs]
      rw [show -F₁ (b - s) + F₁ b = -(F₁ (b - s) - F₁ b) by ring, abs_neg]
      exact this)
  have := key (show h ∈ Icc 0 h from ⟨h0, le_rfl⟩)
  simp only [Real.norm_eq_abs] at this
  have e : b - h = t := by rw [hh]; ring
  rw [e] at this
  have e2 : F t - F b + F₁ b * h = F t - F b - F₁ b * (t - b) := by rw [hh]; ring
  rw [e2] at this
  simpa [Real.norm_eq_abs] using this

end SandierSerfaty.Certificate.Query
