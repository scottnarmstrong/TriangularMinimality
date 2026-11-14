/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.ThetaProduct
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The theta product and its logarithmic potential

Let `τ` have positive imaginary part, `e(w) = exp (2 π i w)` and `Q = e(τ)`. The theta product
`θ(w) = (1 - e(-w)) ∏ₙ (1 - Qⁿ⁺¹ e(w)) ∏ₙ (1 - Qⁿ⁺¹ e(-w))` (Jacobi's `θ₁`, up to a constant factor)
is entire, `1`-periodic, quasi-periodic under `w ↦ w + τ`
(`θ(w + τ) = -Q⁻¹ e(-w) θ(w)`), vanishes exactly on `ℤ + ℤ τ` and has a simple zero at `0`.
Consequently `thetaGreen τ w = -log ‖θ(w)‖ + π (Im w)² / Im τ + π Im w` is `ℤ + ℤ τ`-periodic off the
zeros; it is the single-charge Green function of the torus `ℂ / (ℤ + ℤ τ)` in the normalized coordinate
(used in `SandierSerfaty.Torus.PotentialExists`).
-/

open Filter Topology Metric

public section

namespace SandierSerfaty

namespace Torus

/-- `e(w) = exp (2 π i w)`. -/
@[expose] noncomputable def eF (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)

theorem eF_add (a b : ℂ) : eF (a + b) = eF a * eF b := by
  simp only [eF, mul_add, Complex.exp_add]

theorem eF_neg (w : ℂ) : eF (-w) = (eF w)⁻¹ := by
  simp only [eF, mul_neg, Complex.exp_neg]

theorem eF_ne_zero (w : ℂ) : eF w ≠ 0 := Complex.exp_ne_zero _

theorem eF_zero : eF 0 = 1 := by simp [eF]

theorem eF_int (n : ℤ) : eF n = 1 := by
  simp only [eF]
  have := Complex.exp_int_mul_two_pi_mul_I n
  rw [← this]; congr 1; ring

theorem eF_eq_one_iff {w : ℂ} : eF w = 1 ↔ ∃ k : ℤ, w = k := by
  rw [eF, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2
    rw [hk]; ring
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem eF_nat_mul (n : ℕ) (w : ℂ) : eF (n * w) = eF w ^ n := by
  simp only [eF, ← Complex.exp_nat_mul]
  congr 1; ring

theorem norm_eF (w : ℂ) : ‖eF w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
  simp [eF, Complex.norm_exp]

theorem norm_eF_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖eF τ‖ < 1 := by
  rw [norm_eF, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

/-- The theta product `θ(w) = (1 - e(-w)) ∏ₙ (1 - Qⁿ⁺¹ e(w)) ∏ₙ (1 - Qⁿ⁺¹ e(-w))`, `Q = e(τ)`. -/
@[expose] noncomputable def theta (τ w : ℂ) : ℂ :=
  (1 - eF (-w)) * thetaR (eF τ) (eF w) * thetaR (eF τ) (eF (-w))

theorem differentiable_eF : Differentiable ℂ eF := by
  unfold eF; fun_prop

theorem differentiable_theta {τ : ℂ} (hτ : 0 < τ.im) : Differentiable ℂ (theta τ) := by
  have hR := differentiable_thetaR (norm_eF_lt_one hτ)
  have h2 : Differentiable ℂ (fun w => eF (-w)) := differentiable_eF.comp differentiable_neg
  unfold theta
  exact (((differentiable_const _).sub h2).mul (hR.comp differentiable_eF)).mul (hR.comp h2)

theorem eF_add_one (w : ℂ) : eF (w + 1) = eF w := by
  have := eF_int 1
  simp only [Int.cast_one] at this
  rw [eF_add, this, mul_one]

theorem theta_add_one (τ w : ℂ) : theta τ (w + 1) = theta τ w := by
  have h1 : eF (-(w + 1)) = eF (-w) := by
    rw [neg_add, eF_add]
    have := eF_int (-1)
    simp only [Int.cast_neg, Int.cast_one] at this
    rw [this, mul_one]
  simp only [theta, h1, eF_add_one]

theorem theta_add_tau {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) :
    theta τ (w + τ) = -(eF τ)⁻¹ * eF (-w) * theta τ w := by
  have hQ := norm_eF_lt_one hτ
  set Q := eF τ with hQdef
  have hQ0 : Q ≠ 0 := eF_ne_zero τ
  set y := eF w with hy
  set y' := eF (-w) with hy'
  have hyy : y * y' = 1 := by
    rw [hy, hy', eF_neg]; exact mul_inv_cancel₀ (eF_ne_zero w)
  have h1 : eF (w + τ) = Q * y := by rw [eF_add, mul_comm]
  have h2 : eF (-(w + τ)) = Q⁻¹ * y' := by
    rw [neg_add, eF_add, eF_neg τ, mul_comm]
  have h3 : thetaR Q y = (1 - Q * y) * thetaR Q (Q * y) := thetaR_eq hQ y
  have h4 : thetaR Q (Q⁻¹ * y') = (1 - y') * thetaR Q y' := by
    have := thetaR_eq hQ (Q⁻¹ * y')
    rw [← mul_assoc, mul_inv_cancel₀ hQ0, one_mul] at this
    exact this
  unfold theta
  rw [h1, h2, h4]
  rw [← hQdef, ← hy, ← hy', h3]
  have h5 : 1 - Q⁻¹ * y' = -Q⁻¹ * y' * (1 - Q * y) := by
    have : Q⁻¹ * Q = 1 := inv_mul_cancel₀ hQ0
    linear_combination (-(y * y')) * this - hyy
  rw [h5]
  ring

theorem theta_add_tau_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) :
    theta τ (w + τ) = 0 ↔ theta τ w = 0 := by
  rw [theta_add_tau hτ]
  have h1 : -(eF τ)⁻¹ * eF (-w) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 (inv_ne_zero (eF_ne_zero τ))) (eF_ne_zero _)
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h1
    · exact h
  · intro h; rw [h, mul_zero]

theorem theta_zero (τ : ℂ) : theta τ 0 = 0 := by
  simp [theta, eF_zero]

theorem theta_add_int (τ : ℂ) (w : ℂ) (n : ℤ) : theta τ (w + n) = theta τ w := by
  have hp : Function.Periodic (theta τ) 1 := fun w => theta_add_one τ w
  have := (hp.int_mul n) w
  simpa using this

theorem theta_add_int_mul_tau_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) (n : ℤ) :
    theta τ (w + n * τ) = 0 ↔ theta τ w = 0 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : w + ((k : ℂ) + 1) * τ = (w + k * τ) + τ := by ring
    push_cast at ih ⊢
    rw [this, theta_add_tau_eq_zero_iff hτ, ih]
  | pred k ih =>
    have : w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * τ + τ = w + ((-(k : ℤ) : ℤ) : ℂ) * τ := by
      push_cast; ring
    rw [← ih, ← this, theta_add_tau_eq_zero_iff hτ]

/-- The zeros of the theta product are exactly the lattice `ℤ + ℤ τ`. -/
theorem theta_eq_zero_iff {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) :
    theta τ w = 0 ↔ ∃ m n : ℤ, w = m + n * τ := by
  have hQ := norm_eF_lt_one hτ
  constructor
  · intro h
    unfold theta at h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · have h1 : eF (-w) = 1 := by linear_combination -h
        obtain ⟨k, hk⟩ := eF_eq_one_iff.1 h1
        exact ⟨-k, 0, by push_cast; linear_combination -hk⟩
      · by_contra hne
        have := (thetaR_ne_zero_iff hQ (eF w)).2 ?_
        · exact this h
        intro n hn
        apply hne
        have h1 : eF (((n + 1 : ℕ) : ℂ) * τ + w) = 1 := by
          rw [eF_add, eF_nat_mul]; linear_combination -hn
        obtain ⟨k, hk⟩ := eF_eq_one_iff.1 h1
        exact ⟨k, -((n + 1 : ℕ) : ℤ), by push_cast at hk ⊢; linear_combination hk⟩
    · by_contra hne
      have := (thetaR_ne_zero_iff hQ (eF (-w))).2 ?_
      · exact this h
      intro n hn
      apply hne
      have h1 : eF (((n + 1 : ℕ) : ℂ) * τ + -w) = 1 := by
        rw [eF_add, eF_nat_mul]; linear_combination -hn
      obtain ⟨k, hk⟩ := eF_eq_one_iff.1 h1
      exact ⟨-k, ((n + 1 : ℕ) : ℤ), by push_cast at hk ⊢; linear_combination -hk⟩
  · rintro ⟨m, n, rfl⟩
    have h0 : theta τ (0 + n * τ) = 0 :=
      (theta_add_int_mul_tau_eq_zero_iff hτ 0 n).2 (theta_zero τ)
    rw [zero_add] at h0
    rw [add_comm, theta_add_int, h0]

theorem thetaR_one_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : thetaR (eF τ) 1 ≠ 0 := by
  have hQ := norm_eF_lt_one hτ
  rw [thetaR_ne_zero_iff hQ]
  intro n hn
  have : ‖eF τ ^ (n + 1) * 1‖ < 1 := by
    rw [mul_one, norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hQ (by omega)
  have h1 : eF τ ^ (n + 1) * 1 = 1 := by linear_combination -hn
  rw [h1] at this
  simp at this

/-- The derivative of the theta product at `0` is nonzero: a simple zero. -/
theorem hasDerivAt_theta_zero {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (theta τ) (2 * Real.pi * Complex.I * (thetaR (eF τ) 1 * thetaR (eF τ) 1)) 0 := by
  have hQ := norm_eF_lt_one hτ
  have hR := differentiable_thetaR hQ
  have hM : Differentiable ℂ (fun w => thetaR (eF τ) (eF w) * thetaR (eF τ) (eF (-w))) :=
    (hR.comp differentiable_eF).mul (hR.comp (differentiable_eF.comp differentiable_neg))
  have h1 : HasDerivAt (fun w => 1 - eF (-w)) (2 * Real.pi * Complex.I) 0 := by
    have h0 : HasDerivAt (fun w : ℂ => 2 * Real.pi * Complex.I * (-w))
        (2 * Real.pi * Complex.I * (-1)) 0 :=
      ((hasDerivAt_id (0 : ℂ)).neg).const_mul _
    have h2 := h0.cexp
    have h3 := h2.const_sub 1
    have e : (fun w : ℂ => 1 - eF (-w)) =
        fun x => 1 - Complex.exp (2 * Real.pi * Complex.I * -x) := by
      funext x; simp [eF]
    rw [e]
    convert h3 using 1
    simp
  have h4 := h1.mul (hM 0).hasDerivAt
  have e : theta τ = fun w => (1 - eF (-w)) * (thetaR (eF τ) (eF w) * thetaR (eF τ) (eF (-w))) := by
    funext w; simp only [theta]; ring
  rw [e]
  convert h4 using 1
  simp [eF_zero]

/-- The Laurent expansion at a lattice point: `log ‖θ(w)‖ - log ‖w‖` has a finite limit at `0`. -/
theorem tendsto_log_norm_theta {τ : ℂ} (hτ : 0 < τ.im) :
    ∃ c : ℝ, Tendsto (fun w : ℂ => Real.log ‖theta τ w‖ - Real.log ‖w‖) (𝓝[≠] 0) (𝓝 c) := by
  have hd := hasDerivAt_theta_zero hτ
  set d : ℂ := 2 * Real.pi * Complex.I * (thetaR (eF τ) 1 * thetaR (eF τ) 1) with hdd
  have hd0 : d ≠ 0 := by
    have := thetaR_one_ne_zero hτ
    simp [hdd, Real.pi_ne_zero, this]
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hl : Tendsto (fun w : ℂ => Real.log ‖slope (theta τ) 0 w‖) (𝓝[≠] 0)
      (𝓝 (Real.log ‖d‖)) := by
    have hc : ContinuousAt (fun z : ℂ => Real.log ‖z‖) d :=
      (Real.continuousAt_log (norm_ne_zero_iff.2 hd0)).comp (continuous_norm.continuousAt)
    exact hc.tendsto.comp hs
  refine ⟨Real.log ‖d‖, hl.congr' ?_⟩
  have hne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), slope (theta τ) 0 w ≠ 0 :=
    hs.eventually_ne hd0
  filter_upwards [hne, self_mem_nhdsWithin] with w hw hw0
  have hw0' : w ≠ 0 := hw0
  have hθ : theta τ w ≠ 0 := by
    intro h
    apply hw
    simp [slope_def_field, h, theta_zero]
  rw [slope_def_field, theta_zero, sub_zero, sub_zero, norm_div, Real.log_div]
  · exact norm_ne_zero_iff.2 hθ
  · exact norm_ne_zero_iff.2 hw0'

/-- The theta product does not vanish in a punctured neighbourhood of `0`. -/
theorem eventually_theta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    ∀ᶠ w in 𝓝[≠] (0 : ℂ), theta τ w ≠ 0 := by
  have hd := hasDerivAt_theta_zero hτ
  set d : ℂ := 2 * Real.pi * Complex.I * (thetaR (eF τ) 1 * thetaR (eF τ) 1) with hdd
  have hd0 : d ≠ 0 := by
    have := thetaR_one_ne_zero hτ
    simp [hdd, Real.pi_ne_zero, this]
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), slope (theta τ) 0 w ≠ 0 := hs.eventually_ne hd0
  filter_upwards [hne] with w hw h
  apply hw
  simp [slope_def_field, h, theta_zero]

/-- The logarithmic potential of the theta product, in the normalized coordinate `w`. -/
@[expose] noncomputable def thetaGreen (τ w : ℂ) : ℝ :=
  -Real.log ‖theta τ w‖ + Real.pi * w.im ^ 2 / τ.im + Real.pi * w.im

/-- `thetaGreen`, with the value `0` at the zeros of the theta product. -/
@[expose] noncomputable def thetaGreen0 (τ w : ℂ) : ℝ := if theta τ w = 0 then 0 else thetaGreen τ w

theorem thetaGreen_add_one (τ w : ℂ) : thetaGreen τ (w + 1) = thetaGreen τ w := by
  simp [thetaGreen, theta_add_one]

theorem thetaGreen_add_tau {τ : ℂ} (hτ : 0 < τ.im) {w : ℂ} (hw : theta τ w ≠ 0) :
    thetaGreen τ (w + τ) = thetaGreen τ w := by
  have hQ0 : eF τ ≠ 0 := eF_ne_zero τ
  have hn : ‖theta τ (w + τ)‖ = ‖eF τ‖⁻¹ * ‖eF (-w)‖ * ‖theta τ w‖ := by
    rw [theta_add_tau hτ, norm_mul, norm_mul, norm_neg, norm_inv]
  have h1 : Real.log ‖theta τ (w + τ)‖ =
      2 * Real.pi * τ.im + 2 * Real.pi * w.im + Real.log ‖theta τ w‖ := by
    have hθ : ‖theta τ w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    have h2 : ‖eF τ‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 hQ0)
    have h3 : ‖eF (-w)‖ ≠ 0 := norm_ne_zero_iff.2 (eF_ne_zero _)
    rw [hn, Real.log_mul (mul_ne_zero h2 h3) hθ, Real.log_mul h2 h3, Real.log_inv, norm_eF,
      norm_eF, Real.log_exp, Real.log_exp]
    simp
  simp only [thetaGreen, h1, Complex.add_im]
  have hτ' : τ.im ≠ 0 := hτ.ne'
  field_simp
  ring

theorem thetaGreen0_add_one (τ w : ℂ) : thetaGreen0 τ (w + 1) = thetaGreen0 τ w := by
  simp [thetaGreen0, theta_add_one, thetaGreen_add_one]

theorem thetaGreen0_add_tau {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) :
    thetaGreen0 τ (w + τ) = thetaGreen0 τ w := by
  by_cases hw : theta τ w = 0
  · have : theta τ (w + τ) = 0 := (theta_add_tau_eq_zero_iff hτ w).2 hw
    simp [thetaGreen0, hw, this]
  · have : theta τ (w + τ) ≠ 0 := fun h => hw ((theta_add_tau_eq_zero_iff hτ w).1 h)
    simp [thetaGreen0, hw, this, thetaGreen_add_tau hτ hw]

theorem thetaGreen0_add_int_add_int_mul {τ : ℂ} (hτ : 0 < τ.im) (w : ℂ) (m n : ℤ) :
    thetaGreen0 τ (w + (m + n * τ)) = thetaGreen0 τ w := by
  have h1 : Function.Periodic (thetaGreen0 τ) 1 := fun w => thetaGreen0_add_one τ w
  have h2 : Function.Periodic (thetaGreen0 τ) τ := fun w => thetaGreen0_add_tau hτ w
  have h3 := (h1.int_mul m).add_period (h2.int_mul n)
  simpa using h3 w

end Torus

end SandierSerfaty

end
