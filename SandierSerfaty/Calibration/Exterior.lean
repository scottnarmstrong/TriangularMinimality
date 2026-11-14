/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorInt

/-!
# The exterior formula `tail:exterior-formula`

paper `tail:constant-region`: for `t ≥ l` all `D_i` vanish and `B` is constant, so the
full infinite-mode functions satisfy
`e(t) = 0` and `f₀(t) = f₀(l) - π B(l) (t² - l²)`.

* `deriv_B_of_ge`: `B' = 0` on `[l, ∞)`, hence `B₁(r) = 1/r` there (the derivatives of `log t` and `S₂(t)` cancel);
* `e_of_ge`: every `Q_i = t D_i' - k_i D_i` vanishes for `t ≥ l`;
* `f₀_of_ge` (`tail:exterior-formula`): the closed form, via `S₁(t) = S₁(l) + B(l)(t² - l²)/2` and
  `S₂(t) = S₂(l) - log(t/l)` (the fundamental theorem of calculus for the primitives of `SectorInt.lean`).
-/

open Set MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

theorem deriv_B_of_ge {r : ℝ} (hr : l ≤ r) : deriv B r = 0 := by
  have h := deriv_deriv_eq_of_eqOn (f := B) (g := fun _ => B l) (s := Ici l) (U := Ioi 0)
    (uniqueDiffOn_Ici l) isOpen_Ioi (fun x hx => lt_of_lt_of_le l_pos' hx)
    (fun x hx => B_eq_of_ge hx) contDiffOn_B contDiffOn_const
  have e : deriv (fun _ : ℝ => B l) = fun _ => 0 := by funext x; simp
  have := h.1 hr
  rwa [e] at this

theorem B₁_of_ge {r : ℝ} (hr : l ≤ r) : B₁ r = 1 / r := by
  unfold B₁; rw [deriv_B_of_ge hr]; ring

/-- `e(t) = 0` for `t ≥ l` (`tail:exterior-formula`, first part). -/
theorem e_of_ge {t : ℝ} (ht : l ≤ t) : e t = 0 := by
  have : ∀ i, Q i t = 0 := fun i => by
    simp [Q, D_of_ge ht, (deriv_D_of_ge i ht).1]
  simp [e, this]

/-- For `t ≥ l`, `f₀` reduces to the `B`-part. -/
theorem f₀_eq_of_ge {t : ℝ} (ht : l ≤ t) :
    f₀ t = -2 * Real.pi * S₁ t - 1 / 2 * (Real.log t + S₂ t) := by
  simp [f₀, D_of_ge ht]

theorem S₁_of_ge {t : ℝ} (ht : l ≤ t) : S₁ t = S₁ l + B l * (t ^ 2 - l ^ 2) / 2 := by
  have hl := l_pos'
  have hd : ∀ x ∈ uIcc l t, HasDerivAt S₁ (B x * x) x := fun x hx => by
    rw [uIcc_of_le ht] at hx
    exact hasDerivAt_primitive nearZero_S₁ (lt_of_lt_of_le hl hx.1)
  have hi : IntervalIntegrable (fun x => B x * x) volume l t := by
    refine (contDiffOn_integrand_S₁.continuousOn.mono fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le ht] at hx
    exact lt_of_lt_of_le hl hx.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have h2 : ∫ x in l..t, B x * x = ∫ x in l..t, B l * x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le ht] at hx
    simp only [B_eq_of_ge hx.1]
  rw [h2, intervalIntegral.integral_const_mul, integral_id] at h
  linarith

theorem S₂_of_ge {t : ℝ} (ht : l ≤ t) : S₂ t = S₂ l - (Real.log t - Real.log l) := by
  have hl := l_pos'
  have hd : ∀ x ∈ uIcc l t, HasDerivAt S₂ (-2 * B₁ x + x * B₁ x ^ 2) x := fun x hx => by
    rw [uIcc_of_le ht] at hx
    exact hasDerivAt_primitive nearZero_S₂ (lt_of_lt_of_le hl hx.1)
  have hi : IntervalIntegrable (fun x => -2 * B₁ x + x * B₁ x ^ 2) volume l t := by
    refine (contDiffOn_integrand_S₂.continuousOn.mono fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le ht] at hx
    exact lt_of_lt_of_le hl hx.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have h2 : ∫ x in l..t, (-2 * B₁ x + x * B₁ x ^ 2) = ∫ x in l..t, -(x⁻¹) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le ht] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hl hx.1
    simp only [B₁_of_ge hx.1]
    field_simp
    ring
  rw [h2, intervalIntegral.integral_neg, integral_inv_of_pos hl (lt_of_lt_of_le hl ht),
    Real.log_div (lt_of_lt_of_le hl ht).ne' hl.ne'] at h
  linarith

/-- **`tail:exterior-formula`**: for `t ≥ l`, `e(t) = 0` and
`f₀(t) = f₀(l) - π B(l) (t² - l²)`. -/
theorem f₀_of_ge {t : ℝ} (ht : l ≤ t) : f₀ t = f₀ l - Real.pi * B l * (t ^ 2 - l ^ 2) := by
  have hl := l_pos'
  rw [f₀_eq_of_ge ht, f₀_eq_of_ge le_rfl, S₁_of_ge ht, S₂_of_ge ht]
  ring

theorem exterior_formula {t : ℝ} (ht : l ≤ t) :
    e t = 0 ∧ f₀ t = f₀ l - Real.pi * B l * (t ^ 2 - l ^ 2) :=
  ⟨e_of_ge ht, f₀_of_ge ht⟩

end Calibration

end SandierSerfaty

end
