/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.GreenLiouville
public import SandierSerfaty.ClosedForm.Eisenstein
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The Taylor series of the holomorphic part of `Ĝ`

Ingredients of the proof of `cal:green-expansion`, part 4.

* `hexG_eq_zero_of_not_dvd`: `G_n(ℤ + ℤρ) = 0` unless `6 ∣ n` (rotation by `ρ` preserves the lattice), and `G_n` is real (reflection symmetry; `conj_hexG`).
* `deriv_eq_zero_of_re_eq_zero`: a holomorphic function with vanishing real part has zero derivative.
* `deriv_eq_zero_of_rot`: if `Re F (ρ w) = Re F w` on the unit disc then `F'(0) = F''(0) = 0`.
* `exists_green_series`: with `Ĝ = thetaGreen0 ρ`, there are `C` and a function `Φ`, holomorphic on the
  unit disc, with `Ĝ w = - log ‖w‖ + C + (π / (2 Im ρ)) ‖w‖² + Re Φ w` for `0 < ‖w‖ < 1` and
  `Φ w = ∑_{m ≥ 1} (G_{6m} / (6m)) w^{6m}` there; also `Ĝ w + log ‖w‖ → C` as `w → 0`. This is the paper's
  expansion in the coordinate `w = z / a`. `Φ = F - F 0`, where `F'' = ℘[L - 0]` (Liouville and rotation
  symmetry), so the Taylor coefficients are read off from Mathlib's `iteratedDeriv_weierstrassPExcept_self`.
-/

open Filter Topology Metric Complex

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm Torus

theorem rho_pow_ne_one {n : ℕ} (hn : ¬ 6 ∣ n) : rho ^ n ≠ 1 := by
  have h6 := rho_pow_six
  have hn' : n = 6 * (n / 6) + n % 6 := (Nat.div_add_mod n 6).symm
  have hr : rho ^ n = rho ^ (n % 6) := by
    conv_lhs => rw [hn', pow_add, pow_mul, h6, one_pow, one_mul]
  rw [hr]
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hne : n % 6 ≠ 0 := fun h => hn (Nat.dvd_of_mod_eq_zero h)
  have h1 : rho ≠ 1 := by
    intro h
    have := rho_im
    rw [h] at this
    simp at this
    have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  interval_cases (n % 6)
  · exact absurd rfl hne
  · simpa using h1
  · exact rho_sq_ne_one
  · rw [rho_cube]; norm_num
  · exact rho_pow_four_ne_one
  · intro h
    apply h1
    have : rho ^ 5 * rho = 1 := by rw [← pow_succ, h6]
    rw [h, one_mul] at this
    exact this

theorem hexG_eq_zero_of_not_dvd {n : ℕ} (hn : ¬ 6 ∣ n) : hexPair.G n = 0 := by
  have h := hexG_rot n
  have hρ : rho ^ n ≠ 1 := rho_pow_ne_one hn
  have hρ0 : rho ^ n ≠ 0 := pow_ne_zero _ rho_ne_zero
  have : (1 - (rho ^ n)⁻¹) * hexPair.G n = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · exfalso
    apply hρ
    have : (rho ^ n)⁻¹ = 1 := by linear_combination -h1
    simpa using this
  · exact h1

theorem hexG_im (n : ℕ) : (hexPair.G n).im = 0 := by
  have := conj_hexG n
  have h := congrArg Complex.im this
  simp only [Complex.conj_im] at h
  linarith

/-- A function with vanishing real part near `w` has zero derivative there. -/
theorem deriv_eq_zero_of_re_eq_zero {D : ℂ → ℂ} {w : ℂ} (hD : DifferentiableAt ℂ D w)
    (h : ∀ᶠ x in 𝓝 w, (D x).re = 0) : deriv D w = 0 := by
  have h1 : HasFDerivAt D ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv D w)).restrictScalars ℝ) w :=
    hD.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have h2 := Complex.reCLM.hasFDerivAt.comp w h1
  have h3 : HasFDerivAt (Complex.reCLM ∘ D) (0 : ℂ →L[ℝ] ℝ) w := by
    have : HasFDerivAt (fun _ : ℂ => (0 : ℝ)) (0 : ℂ →L[ℝ] ℝ) w := hasFDerivAt_const _ _
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [h] with x hx
    simpa using hx
  have h4 := h2.unique h3
  have e1 := congrArg (fun L => L 1) h4
  have e2 := congrArg (fun L => L Complex.I) h4
  simp at e1 e2
  apply Complex.ext
  · simpa using e1
  · simpa using e2

/-- If `Re F (ρ w) = Re F w` on the unit disc, then `F'(0) = F''(0) = 0`. -/
theorem deriv_eq_zero_of_rot {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hre : ∀ w ∈ ball (0 : ℂ) 1, (F (rho * w)).re = (F w).re) :
    deriv F 0 = 0 ∧ deriv (deriv F) 0 = 0 := by
  have hρ1 : ‖rho‖ = 1 := norm_rho
  have hmem : ∀ w ∈ ball (0 : ℂ) 1, rho * w ∈ ball (0 : ℂ) 1 := by
    intro w hw
    simpa [norm_mul, hρ1] using hw
  have hFa : ∀ w ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ F w := fun w hw =>
    hF.differentiableAt (isOpen_ball.mem_nhds hw)
  have hdF : DifferentiableOn ℂ (deriv F) (ball 0 1) := hF.deriv isOpen_ball
  have hdFa : ∀ w ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ (deriv F) w := fun w hw =>
    hdF.differentiableAt (isOpen_ball.mem_nhds hw)
  have hd2 : DifferentiableOn ℂ (deriv (deriv F)) (ball 0 1) := hdF.deriv isOpen_ball
  -- step A
  have hA : ∀ w ∈ ball (0 : ℂ) 1, rho * deriv F (rho * w) = deriv F w := by
    intro w hw
    have h1 : HasDerivAt (fun x => F (rho * x) - F x) (deriv F (rho * w) * rho - deriv F w) w := by
      have hc : HasDerivAt (fun x => F (rho * x)) (deriv F (rho * w) * rho) w := by
        have := (hFa _ (hmem w hw)).hasDerivAt.comp w ((hasDerivAt_id' w).const_mul rho)
        exact this.congr_deriv (by ring)
      exact hc.sub (hFa w hw).hasDerivAt
    have h2 : deriv (fun x => F (rho * x) - F x) w = 0 := by
      refine deriv_eq_zero_of_re_eq_zero h1.differentiableAt ?_
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx
      simp [hre x hx]
    rw [h1.deriv] at h2
    linear_combination h2
  -- step B
  have hB : ∀ w ∈ ball (0 : ℂ) 1, rho * rho * deriv (deriv F) (rho * w) = deriv (deriv F) w := by
    intro w hw
    have h1 : HasDerivAt (fun x => rho * deriv F (rho * x) - deriv F x)
        (rho * (deriv (deriv F) (rho * w) * rho) - deriv (deriv F) w) w := by
      have hc : HasDerivAt (fun x => deriv F (rho * x)) (deriv (deriv F) (rho * w) * rho) w := by
        have := (hdFa _ (hmem w hw)).hasDerivAt.comp w ((hasDerivAt_id' w).const_mul rho)
        exact this.congr_deriv (by ring)
      exact (hc.const_mul rho).sub (hdFa w hw).hasDerivAt
    have h2 : deriv (fun x => rho * deriv F (rho * x) - deriv F x) w = 0 := by
      have : (fun x => rho * deriv F (rho * x) - deriv F x) =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        filter_upwards [isOpen_ball.mem_nhds hw] with x hx
        simp [hA x hx]
      rw [this.deriv_eq]; simp
    rw [h1.deriv] at h2
    linear_combination h2
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hA0 := hA 0 h0
  have hB0 := hB 0 h0
  simp only [mul_zero] at hA0 hB0
  have hρ1' : rho - 1 ≠ 0 := sub_ne_zero.2 (by
    intro h
    have := rho_pow_ne_one (n := 1) (by norm_num)
    exact this (by simpa using h))
  have hρ2' : rho ^ 2 - 1 ≠ 0 := sub_ne_zero.2 rho_sq_ne_one
  constructor
  · have : (rho - 1) * deriv F 0 = 0 := by linear_combination hA0
    exact (mul_eq_zero.1 this).resolve_left hρ1'
  · have : (rho ^ 2 - 1) * deriv (deriv F) 0 = 0 := by linear_combination hB0
    exact (mul_eq_zero.1 this).resolve_left hρ2'

/-- Nonzero points of the unit disc are not lattice points. -/
theorem notMem_hexLattice_of_norm_lt_one {w : ℂ} (hw1 : ‖w‖ < 1) (hw0 : w ≠ 0) :
    w ∉ hexPair.lattice := fun h =>
  absurd (one_le_norm_of_mem_hexLattice h hw0) (not_le.2 hw1)

theorem iteratedDeriv_two_add_green {F : ℂ → ℂ}
    (hF2 : ∀ w ∈ ball (0 : ℂ) 1, deriv (deriv F) w = hexPair.weierstrassPExcept 0 w) (m : ℕ) :
    iteratedDeriv (m + 2) F 0 =
      if m = 0 then 0 else ((m + 1).factorial : ℂ) * hexPair.G (m + 2) := by
  have h1 : iteratedDeriv (m + 2) F = iteratedDeriv m (deriv (deriv F)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have h2 : deriv (deriv F) =ᶠ[𝓝 0] hexPair.weierstrassPExcept 0 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with x hx
    exact hF2 x hx
  rw [h1, h2.iteratedDeriv_eq, hexPair.iteratedDeriv_weierstrassPExcept_self]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ↓reduceIte, PeriodPair.sumInvPow_zero]

/-- **The Taylor series of the theta Green function of the hexagonal lattice.** -/
theorem exists_green_series :
    ∃ (C : ℝ) (Φ : ℂ → ℂ),
      Tendsto (fun w : ℂ => thetaGreen0 rho w + Real.log ‖w‖) (𝓝[≠] 0) (𝓝 C) ∧
      DifferentiableOn ℂ Φ (ball 0 1) ∧
      (∀ w ∈ ball (0 : ℂ) 1,
        HasSum (fun m : ℕ => hexPair.G (6 * (m + 1)) / ((6 * (m + 1) : ℕ) : ℂ) *
            w ^ (6 * (m + 1))) (Φ w)) ∧
      ∀ w ∈ ball (0 : ℂ) 1, w ≠ 0 →
        thetaGreen0 rho w =
          -Real.log ‖w‖ + C + Real.pi / (2 * rho.im) * ‖w‖ ^ 2 + (Φ w).re := by
  obtain ⟨F, C₀, hFd, hF2, hG⟩ := exists_green_holomorphic_part
  obtain ⟨κ, hκ⟩ := exists_deriv_thetaQlog_eq
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- rotation invariance of `Re F`
  have hre : ∀ w ∈ ball (0 : ℂ) 1, (F (rho * w)).re = (F w).re := by
    intro w hw
    by_cases hw0 : w = 0
    · simp [hw0]
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hρw : rho * w ∈ ball (0 : ℂ) 1 := by simpa [norm_mul, norm_rho] using hw
    have hρw0 : rho * w ≠ 0 := mul_ne_zero rho_ne_zero hw0
    have e1 := hG w hw hw0
    have e2 := hG (rho * w) hρw hρw0
    rw [thetaGreen0_rho_mul (notMem_hexLattice_of_norm_lt_one hw1 hw0), e1] at e2
    simp only [norm_mul, norm_rho, one_mul] at e2
    linarith
  obtain ⟨hF1, hFdd⟩ := deriv_eq_zero_of_rot hFd hre
  -- `F'' = ℘[L - 0]`
  have hF2' : ∀ w ∈ ball (0 : ℂ) 1, deriv (deriv F) w = hexPair.weierstrassPExcept 0 w := by
    intro w hw
    have e0 := hF2 0 h0
    rw [hFdd] at e0
    have e0' := hκ 0 h0
    rw [hF2 w hw]
    have e1 := hκ w hw
    simp only [PeriodPair.weierstrassPExcept_zero, zero_add] at e0'
    linear_combination e1 - e0 - e0'
  have hC : ∀ w ∈ ball (0 : ℂ) 1,
      HasSum (fun m : ℕ => hexPair.G (6 * (m + 1)) / ((6 * (m + 1) : ℕ) : ℂ) *
        w ^ (6 * (m + 1))) (F w - F 0) := by
    intro w hw
    have hT := Complex.hasSum_taylorSeries_on_ball hFd hw
    simp only [sub_zero] at hT
    set T : ℕ → ℂ := fun n =>
      if n = 0 then F 0 else if 6 ∣ n then hexPair.G n / (n : ℂ) * w ^ n else 0 with hTdef
    have hterm : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ • w ^ n • iteratedDeriv n F 0 = T n := by
      intro n
      match n with
      | 0 => simp [hTdef]
      | 1 => simp [hTdef, iteratedDeriv_one, hF1]
      | m + 2 =>
        rw [iteratedDeriv_two_add_green hF2' m]
        by_cases hm : m = 0
        · subst hm
          simp [hTdef]
        · by_cases h6 : 6 ∣ m + 2
          · have hne : m + 2 ≠ 0 := by omega
            have h2 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hne
            have h1 : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
            have hf : ((m + 2).factorial : ℂ) = ((m + 2 : ℕ) : ℂ) * ((m + 1).factorial : ℂ) := by
              rw [Nat.factorial_succ (m + 1)]; push_cast; ring
            simp only [hTdef, hm, hne, h6, ↓reduceIte, smul_eq_mul]
            rw [hf]
            field_simp
          · have : hexPair.G (m + 2) = 0 := hexG_eq_zero_of_not_dvd h6
            simp [hTdef, hm, h6, this]
    have hT' : HasSum T (F w) := by
      convert hT using 1
      funext n
      exact (hterm n).symm
    have hinj : Function.Injective (fun m : ℕ => 6 * m) := fun a b h => by simpa using h
    have hsupp : ∀ n ∉ Set.range (fun m : ℕ => 6 * m), T n = 0 := by
      intro n hn
      have h0 : n ≠ 0 := fun h => hn ⟨0, by simp [h]⟩
      have h6 : ¬ 6 ∣ n := fun ⟨k, hk⟩ => hn ⟨k, hk.symm⟩
      simp [hTdef, h0, h6]
    have hT6 : HasSum (fun m : ℕ => T (6 * m)) (F w) := (hinj.hasSum_iff hsupp).2 hT'
    have hT7 := (hasSum_nat_add_iff' 1).2 hT6
    have hT0 : T (6 * 0) = F 0 := by simp [hTdef]
    simp only [Finset.sum_range_one, hT0] at hT7
    convert hT7 using 1
    funext m
    have hn : (6 * (m + 1) : ℕ) ≠ 0 := by omega
    have h6 : 6 ∣ 6 * (m + 1) := dvd_mul_right 6 _
    simp only [hTdef, hn, h6, ↓reduceIte]
  refine ⟨C₀ + (F 0).re, fun w => F w - F 0, ?_, hFd.sub_const _, hC, ?_⟩
  · have hFc : ContinuousAt F 0 := (hFd.differentiableAt (isOpen_ball.mem_nhds h0)).continuousAt
    have hlim : Tendsto (fun w : ℂ => C₀ + Real.pi / (2 * rho.im) * ‖w‖ ^ 2 + (F w).re) (𝓝 0)
        (𝓝 (C₀ + Real.pi / (2 * rho.im) * ‖(0 : ℂ)‖ ^ 2 + (F 0).re)) :=
      ((continuous_const.add (continuous_const.mul (continuous_norm.pow 2))).continuousAt.tendsto).add
        (Complex.continuous_re.continuousAt.tendsto.comp hFc.tendsto)
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at hlim
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds h0),
      self_mem_nhdsWithin] with w hw hw0
    rw [hG w hw hw0]
    ring
  · intro w hw hw0
    rw [hG w hw hw0]
    simp only [Complex.sub_re]
    ring

end Calibration

end SandierSerfaty

end
