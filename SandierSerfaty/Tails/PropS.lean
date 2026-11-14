/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.RetainedCore
public import SandierSerfaty.Tails.IntegralJets
public import SandierSerfaty.Calibration.Sector

/-!
# Propagation to `S₁` and `S₂` (paper §6.5)

`ΔS₁ = S₁ - S̃₁ = ∫₀ᵗ ΔB r dr` and `ΔS₂ = S₂ - S̃₂ = ∫₀ᵗ (-2 + r (2 B̃₁ + ΔB₁)) ΔB₁ dr`
(the paper's identity `Δ(-2B₁ + r B₁²) = (-2 + r (2B̃₁ + ΔB₁)) ΔB₁`, paper §6.5), with their jets and

* `jn_dS1_le`: `|ΔS₁|_{2,t} ≤ 3 W_*` (paper §6.5);
* `jn_dS2_le`: `|ΔS₂|_{2,t} ≤ (4 + 8·6000 + 4W_*) W_* < 60000 W_*` (paper §6.5), under the finite premise.
-/

open Set Filter MeasureTheory

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem integral_congr_pos {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (h : ∀ r, 0 < r → f r = g r) :
    ∫ r in (0 : ℝ)..t, f r = ∫ r in (0 : ℝ)..t, g r := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun r hr => h r ?_)
  rw [uIoc_of_le ht.le] at hr
  exact hr.1

/-! ### `ΔS₁` -/

/-- `ΔS₁(t) = ∫₀ᵗ ΔB(r) r dr`. -/
@[expose] noncomputable def dS1 (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, dU0 r * r

@[expose] noncomputable def dS1₁ (t : ℝ) : ℝ := dU0 t * t

@[expose] noncomputable def dS1₂ (t : ℝ) : ℝ := dU1 t * t + dU0 t

theorem jet_dS1 : Jet2 (Ioi 0) (Ioi 0) dS1 dS1₁ dS1₂ :=
  jet_integral nearZero_dU0_mul fun x hx =>
    ((jet_dU.d0 x hx).mul (hasDerivAt_id' x)).congr_deriv (by unfold dS1₂; ring)

theorem S₁_eq {t : ℝ} (ht : 0 < t) : S₁ t = Trunc.S₁ t + dS1 t := by
  unfold S₁ Trunc.S₁ dS1
  rw [← intervalIntegral.integral_add (intervalIntegrable_of_nearZero nearZero_trunc_B_mul ht)
    (intervalIntegrable_of_nearZero nearZero_dU0_mul ht)]
  refine integral_congr_pos ht fun r hr => ?_
  rw [B_eq_trunc_add hr]; ring

theorem jn_dS1_le {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : jn dS1 dS1₁ dS1₂ t ≤ 3 * Wstar := by
  have hw := ww_nonneg
  have hW := ww_le_Wstar
  have h0 : ∀ r, 0 < r → |dU0 r * r| ≤ ww * r := fun r hr => by
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_right (dU_bound hr).1 hr.le
  have hI : |dS1 t| ≤ ww * t ^ 2 / 2 := by
    unfold dS1
    have h1 : ‖∫ r in (0 : ℝ)..t, dU0 r * r‖ ≤ ∫ r in (0 : ℝ)..t, ww * r := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.le
        (Filter.Eventually.of_forall fun r hr => ?_) ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      rw [Real.norm_eq_abs]; exact h0 r hr.1
    rw [intervalIntegral.integral_const_mul, integral_id] at h1
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (le_of_eq ?_)
    ring
  have h1 : |dS1₁ t| ≤ ww * t := h0 t ht
  have h2 : |dS1₂ t| ≤ ww * t + ww := by
    unfold dS1₂
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos ht]
    have := dU_bound ht
    nlinarith [this.1, this.2.1, abs_nonneg (dU0 t), abs_nonneg (dU1 t)]
  unfold jn
  nlinarith [mul_nonneg hw (sq_nonneg t), mul_nonneg hw ht.le, mul_nonneg hw (sub_nonneg.2 ht1)]

/-! ### `ΔS₂` -/

@[expose] noncomputable def dY (r : ℝ) : ℝ := 2 * Trunc.B₁ r + dU1 r

@[expose] noncomputable def dY₁ (r : ℝ) : ℝ := 2 * Bt1d r + dU2 r

@[expose] noncomputable def dX (r : ℝ) : ℝ := -2 + r * dY r

@[expose] noncomputable def dX₁ (r : ℝ) : ℝ := dY r + r * dY₁ r

/-- The integrand `(-2 + r (2 B̃₁ + ΔB₁)) ΔB₁` of `ΔS₂`. -/
@[expose] noncomputable def dφ (r : ℝ) : ℝ := dX r * dU1 r

@[expose] noncomputable def dφ₁ (r : ℝ) : ℝ := dX₁ r * dU1 r + dX r * dU2 r

/-- `ΔS₂(t) = ∫₀ᵗ (-2 + r (2 B̃₁ + ΔB₁)) ΔB₁ dr`. -/
@[expose] noncomputable def dS2 (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, dφ r

theorem hasDerivAt_dφ {x : ℝ} (hx : 0 < x) : HasDerivAt dφ (dφ₁ x) x := by
  have hB := jet_Bt1.d0 x hx
  have hU1 := jet_dU.d1 x hx
  have hY : HasDerivAt dY (dY₁ x) x := by
    refine ((hB.const_mul 2).add hU1).congr_deriv ?_
    unfold dY₁; ring
  have hX : HasDerivAt dX (dX₁ x) x := by
    have := (hasDerivAt_id' x).mul hY
    refine (this.const_add (-2)).congr_deriv ?_
    unfold dX₁; ring
  exact hX.mul hU1

theorem nearZero_dφ (hc : FiniteCore) : NearZero dφ := by
  have h1 := (nearZero_Trunc_B₁ hc).const_mul 2
  have h2 := h1.add nearZero_dU1
  have h3 := (NearZero.id_mul h2).add (NearZero.const (-2))
  exact (h3.mul nearZero_dU1).congr_pos fun r _ => by unfold dφ dX dY; ring

theorem jet_dS2 (hc : FiniteCore) : Jet2 (Ioi 0) (Ioi 0) dS2 dφ dφ₁ :=
  jet_integral (nearZero_dφ hc) fun _ hx => hasDerivAt_dφ hx

theorem S₂_eq (hc : FiniteCore) {t : ℝ} (ht : 0 < t) : S₂ t = Trunc.S₂ t + dS2 t := by
  have hn := nearZero_Trunc_B₁ hc
  have hI : NearZero fun r => -2 * Trunc.B₁ r + r * Trunc.B₁ r ^ 2 :=
    ((hn.const_mul (-2)).add (NearZero.id_mul (hn.mul hn))).congr_pos fun r _ => by ring
  unfold S₂ Trunc.S₂ dS2
  rw [← intervalIntegral.integral_add (intervalIntegrable_of_nearZero hI ht)
    (intervalIntegrable_of_nearZero (nearZero_dφ hc) ht)]
  refine integral_congr_pos ht fun r hr => ?_
  rw [B₁_eq_trunc_add hr]; unfold dφ dX dY; ring

theorem jn₁_dφ_le (hc : FiniteCore) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |dφ r| + |dφ₁ r| ≤ (24002 + Wstar) * Wstar := by
  have hw := ww_nonneg
  have hW := ww_le_Wstar
  have hB := B₁_bound_all hc hr
  obtain ⟨u0, u1, u2⟩ := dU_bound hr
  have hY : |dY r| + |dY₁ r| ≤ 12000 + 2 * ww := by
    unfold dY dY₁
    have a1 := abs_add_le (2 * Trunc.B₁ r) (dU1 r)
    have a2 := abs_add_le (2 * Bt1d r) (dU2 r)
    simp only [abs_mul, abs_two] at a1 a2
    linarith
  have hX : |dX r| + |dX₁ r| ≤ 2 + 2 * (12000 + 2 * ww) := by
    have hY0 := abs_nonneg (dY r)
    have hY1 := abs_nonneg (dY₁ r)
    have e1 : |dX r| ≤ 2 + r * |dY r| := by
      unfold dX
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_two, abs_mul, abs_of_pos hr]
    have e2 : |dX₁ r| ≤ |dY r| + r * |dY₁ r| := by
      unfold dX₁
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hr]
    nlinarith [mul_nonneg hY0 (sub_nonneg.2 hr1), mul_nonneg hY1 (sub_nonneg.2 hr1)]
  have hM := jn₁_mul_le (dX r) (dX₁ r) (dU1 r) (dU2 r)
  have e : |dφ r| + |dφ₁ r| = |dX r * dU1 r| + |dX₁ r * dU1 r + dX r * dU2 r| := rfl
  rw [e]
  refine hM.trans ?_
  have hX0 := abs_nonneg (dX r)
  have hX1 := abs_nonneg (dX₁ r)
  have hd : |dU1 r| + |dU2 r| ≤ 2 * ww := by linarith
  calc (|dX r| + |dX₁ r|) * (|dU1 r| + |dU2 r|)
      ≤ (2 + 2 * (12000 + 2 * ww)) * (2 * ww) :=
        mul_le_mul hX hd (by positivity) (by positivity)
    _ = (24002 + 4 * ww) * (2 * ww) := by ring
    _ ≤ (24002 + Wstar) * Wstar := by
        have : Wstar = 4 * ww := rfl
        rw [this]; nlinarith

theorem jn_dS2_le (hc : FiniteCore) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    jn dS2 dφ dφ₁ t ≤ 2 * ((24002 + Wstar) * Wstar) := by
  set M := (24002 + Wstar) * Wstar with hMdef
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Wstar := by unfold Wstar; linarith [ww_nonneg]
    positivity
  have hI : |dS2 t| ≤ M * t := by
    unfold dS2
    have h1 : ‖∫ r in (0 : ℝ)..t, dφ r‖ ≤ ∫ r in (0 : ℝ)..t, M := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.le
        (Filter.Eventually.of_forall fun r hr => ?_) intervalIntegrable_const
      rw [Real.norm_eq_abs]
      have := jn₁_dφ_le hc hr.1 (hr.2.trans ht1)
      linarith [abs_nonneg (dφ₁ r)]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, Real.norm_eq_abs] at h1
    linarith
  have h2 := jn₁_dφ_le hc ht ht1
  unfold jn
  have := abs_nonneg (dφ₁ t)
  nlinarith

end Tails

end SandierSerfaty

end
