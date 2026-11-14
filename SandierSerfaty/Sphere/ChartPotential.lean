/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Chordal
public import SandierSerfaty.Sphere.LogPotential

/-!
# The chart potential and its inversion (sphere note, Definition 3.3, Lemma 3.8)

* `Sphere.chartPot X`: `h_X(x) = ∑ᵢ g(x - xᵢ) + (n/2) V(x)` (Definition 3.3);
* `Sphere.chartPot_invC`: `h_X ∘ ι = h_{X̃} - ∑ log |xᵢ|` off the singular set (Lemma 3.8);
* `Sphere.potV_invC`: `V (ι x) = V x - 2 log |x|`.
-/

open Complex

public section

namespace SandierSerfaty

namespace Sphere

/-- The chart potential `h_X(x) = ∑ᵢ g(x - xᵢ) + (n/2) V(x)` (Definition 3.3). -/
@[expose] noncomputable def chartPot {n : ℕ} (X : Fin n → ℂ) (x : ℂ) : ℝ :=
  ∑ i, gKer (x - X i) + (n : ℝ) / 2 * potV x

theorem potV_invC {x : ℂ} (hx : x ≠ 0) : potV (invC x) = potV x - 2 * Real.log ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  unfold potV invC
  rw [norm_inv, Complex.norm_conj]
  have : 1 + (‖x‖⁻¹) ^ 2 = (1 + ‖x‖ ^ 2) / ‖x‖ ^ 2 := by field_simp; ring
  rw [this, Real.log_div h1.ne' (by positivity), Real.log_pow]
  push_cast
  ring

theorem invC_invC (x : ℂ) : invC (invC x) = x := by
  unfold invC
  simp

theorem invC_ne_zero {x : ℂ} (hx : x ≠ 0) : invC x ≠ 0 := by
  unfold invC; simpa using hx

/-- **Lemma 3.8** (inversion of the potential). For `X` with all `xᵢ ≠ 0` and `x ≠ 0` not equal to
any `ι xᵢ`, `h_X (ι x) = h_{X̃} x - ∑ᵢ log |xᵢ|`. -/
theorem chartPot_invC {n : ℕ} (X : Fin n → ℂ) (hX : ∀ i, X i ≠ 0) {x : ℂ} (hx : x ≠ 0)
    (hxX : ∀ i, x ≠ invC (X i)) :
    chartPot X (invC x) = chartPot (fun i => invC (X i)) x - ∑ i, Real.log ‖X i‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have key : ∀ i, gKer (invC x - X i) =
      gKer (x - invC (X i)) - Real.log ‖X i‖ + Real.log ‖x‖ := by
    intro i
    have hxi := hX i
    have hxi' : invC (X i) ≠ 0 := invC_ne_zero hxi
    have h0 : invC x - X i = invC x - invC (invC (X i)) := by rw [invC_invC (X i)]
    have hsub : x - invC (X i) ≠ 0 := sub_ne_zero.2 (hxX i)
    have hnorm : ‖invC x - X i‖ = ‖x - invC (X i)‖ / (‖x‖ * ‖invC (X i)‖) := by
      rw [h0]; exact norm_invC_sub hx hxi'
    have hxin : 0 < ‖X i‖ := norm_pos_iff.2 hxi
    have hn' : ‖invC (X i)‖ = ‖X i‖⁻¹ := by unfold invC; rw [norm_inv, Complex.norm_conj]
    have hsn : 0 < ‖x - invC (X i)‖ := norm_pos_iff.2 hsub
    unfold gKer
    rw [hnorm, hn', Real.log_div hsn.ne' (by positivity), Real.log_mul hn.ne' (by positivity),
      Real.log_inv]
    ring
  unfold chartPot
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [potV_invC hx]
  ring

end Sphere

end SandierSerfaty

end
