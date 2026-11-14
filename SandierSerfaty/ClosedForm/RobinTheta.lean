/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.GreenLocal
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The regular part of the theta Green function at `0`, explicitly

The closed-form note's Lemma B3(c). For `Im τ > 0` and `p ≠ 0`:

* `SandierSerfaty.ClosedForm.tendsto_greenOne_add_log_explicit`:
  `greenOne p τ z + log ‖z‖ → -log (2 π ‖Π‖²) + log ‖p‖` as `z → 0`, where `Π = ∏ₙ (1 - Qⁿ⁺¹)`
  (`= thetaR (eF τ) 1`), because `θ'(0) = 2 π i Π²`;
* `SandierSerfaty.ClosedForm.norm_discriminant_eq_thetaR`: `‖Δ(τ)‖ = e^{-2 π Im τ} ‖Π‖²⁴`, from Mathlib's
  `ModularForm.discriminant_eq_q_prod`.
-/

open Filter Topology Complex
open SandierSerfaty.Torus

public section

namespace SandierSerfaty

namespace ClosedForm

/-- The derivative of the theta product at `0` (`θ'(0) = 2 π i Π²`). -/
@[expose] noncomputable def thetaDeriv0 (τ : ℂ) : ℂ :=
  2 * Real.pi * Complex.I * (thetaR (eF τ) 1 * thetaR (eF τ) 1)

theorem thetaDeriv0_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : thetaDeriv0 τ ≠ 0 := by
  have := thetaR_one_ne_zero hτ
  simp [thetaDeriv0, Real.pi_ne_zero, this]

theorem norm_thetaDeriv0 (τ : ℂ) :
    ‖thetaDeriv0 τ‖ = 2 * Real.pi * ‖thetaR (eF τ) 1‖ ^ 2 := by
  simp only [thetaDeriv0, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_ofNat, Real.norm_of_nonneg Real.pi_pos.le]
  ring

/-- `log ‖θ w‖ - log ‖w‖ → log ‖θ'(0)‖` as `w → 0`. -/
theorem tendsto_log_norm_theta_sub {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto (fun w : ℂ => Real.log ‖theta τ w‖ - Real.log ‖w‖) (𝓝[≠] 0)
      (𝓝 (Real.log ‖thetaDeriv0 τ‖)) := by
  have hd := hasDerivAt_theta_zero hτ
  have hd0 := thetaDeriv0_ne_zero hτ
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hl : Tendsto (fun w : ℂ => Real.log ‖slope (theta τ) 0 w‖) (𝓝[≠] 0)
      (𝓝 (Real.log ‖thetaDeriv0 τ‖)) := by
    have hc : ContinuousAt (fun z : ℂ => Real.log ‖z‖) (thetaDeriv0 τ) :=
      (Real.continuousAt_log (norm_ne_zero_iff.2 hd0)).comp (continuous_norm.continuousAt)
    exact hc.tendsto.comp hs
  refine hl.congr' ?_
  have hne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), slope (theta τ) 0 w ≠ 0 := hs.eventually_ne hd0
  filter_upwards [hne, self_mem_nhdsWithin] with w hw hw0
  have hw0' : w ≠ 0 := hw0
  have hθ : theta τ w ≠ 0 := by
    intro h
    apply hw
    simp [slope_def_field, h, theta_zero]
  rw [slope_def_field, theta_zero, sub_zero, sub_zero, norm_div, Real.log_div]
  · exact norm_ne_zero_iff.2 hθ
  · exact norm_ne_zero_iff.2 hw0'

/-- The regular part of `greenOne p τ` at `0`, explicitly. -/
theorem tendsto_greenOne_add_log_explicit {τ p : ℂ} (hτ : 0 < τ.im) (hp : p ≠ 0) :
    Tendsto (fun z : ℂ => greenOne p τ z + Real.log ‖z‖) (𝓝[≠] 0)
      (𝓝 (-Real.log ‖thetaDeriv0 τ‖ + Real.log ‖p‖)) := by
  have hc₀ := tendsto_log_norm_theta_sub hτ
  have hmap : Tendsto (fun z : ℂ => z / p) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => z / p) (𝓝 0) (𝓝 (0 / p)) :=
        (continuous_id.div_const p).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hp] using hz
  have hq : Tendsto (fun z : ℂ => Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z) (𝓝 0)
      (𝓝 0) := by
    have hc : Continuous fun z : ℂ => Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z := by
      fun_prop
    simpa using hc.tendsto 0
  have hlim : Tendsto (fun z : ℂ => -(Real.log ‖theta τ (z / p)‖ - Real.log ‖z / p‖) +
      (Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z) + Real.log ‖p‖) (𝓝[≠] 0)
      (𝓝 (-Real.log ‖thetaDeriv0 τ‖ + 0 + Real.log ‖p‖)) :=
    (((hc₀.comp hmap).neg).add (hq.mono_left nhdsWithin_le_nhds)).add tendsto_const_nhds
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmap.eventually (eventually_theta_ne_zero hτ), self_mem_nhdsWithin]
    with z hz hz0
  have hz0' : z ≠ 0 := hz0
  rw [greenOne_eq hz]
  have h1 : ‖z / p‖ ≠ 0 := norm_ne_zero_iff.2 (div_ne_zero hz0' hp)
  have h2 : ‖p‖ ≠ 0 := norm_ne_zero_iff.2 hp
  have h3 : Real.log ‖z‖ = Real.log ‖z / p‖ + Real.log ‖p‖ := by
    rw [← Real.log_mul h1 h2, norm_div, div_mul_cancel₀ _ h2]
  rw [h3]
  ring

/-- The discriminant in terms of the theta product's `Π = ∏ₙ (1 - Qⁿ⁺¹)`:
`‖Δ(τ)‖ = e^{-2 π Im τ} ‖Π‖²⁴`. -/
theorem norm_discriminant_eq_thetaR (z : UpperHalfPlane) :
    ‖ModularForm.discriminant z‖ =
      Real.exp (-(2 * Real.pi * (z : ℂ).im)) * ‖thetaR (eF (z : ℂ)) 1‖ ^ 24 := by
  have hz : 0 < (z : ℂ).im := z.im_pos
  have hQ := norm_eF_lt_one hz
  rw [ModularForm.discriminant_eq_q_prod, norm_mul]
  have hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ = Real.exp (-(2 * Real.pi * (z : ℂ).im)) := by
    simp [Function.Periodic.qParam, Complex.norm_exp]
  have hprod : ∏' n : ℕ, (1 - ModularForm.eta_q n z) ^ 24 = thetaR (eF (z : ℂ)) 1 ^ 24 := by
    have hm : Multipliable fun n : ℕ => 1 - eF (z : ℂ) ^ (n + 1) * 1 :=
      multipliable_thetaR hQ 1
    rw [thetaR, ← hm.tprod_pow]
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_pow]
    simp [eF]
  rw [hq, hprod, norm_pow]

end ClosedForm

end SandierSerfaty

end
