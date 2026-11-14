/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.GreenLog
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.Complex.Liouville

/-!
# Liouville: `(log q)''` and the Weierstrass `℘` of the hexagonal lattice

Ingredients of the proof of `cal:green-expansion`, part 3.

For `θ = theta ρ` put `ℓ = θ'/θ` (holomorphic off the lattice `L = ℤ + ℤρ`). Quasi-periodicity of `θ`
gives `ℓ (w + 1) = ℓ w` and `ℓ (w + ρ) = ℓ w - 2πi`, so `ℓ'` is `L`-periodic. Near `0`,
`ℓ' = - w⁻² + (q'/q)'` and `℘ = w⁻² + ℘[L - 0]`, so `Φ = - ℓ' - ℘` is periodic and extends
holomorphically to the lattice points. It is bounded (continuous and periodic), hence constant by
Liouville. Consequently there is a constant `κ` with `- (q'/q)' = ℘[L - 0] + κ` on the unit disc
(`exists_deriv_thetaQlog_eq`). The paper's phrase "the difference is holomorphic and periodic, hence
constant" is this statement.
-/

open Filter Topology Metric Complex

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm Torus

theorem theta_eq_zero_iff_mem (w : ℂ) : theta rho w = 0 ↔ w ∈ hexPair.lattice := by
  rw [theta_eq_zero_iff rho_im_pos, mem_hexPair_lattice]
  constructor
  · rintro ⟨m, n, h⟩; exact ⟨n, m, by rw [h]; ring⟩
  · rintro ⟨m, n, h⟩; exact ⟨n, m, by rw [← h]; ring⟩

/-- The logarithmic derivative `θ'/θ` of the theta product. -/
@[expose] noncomputable def thetaLog (w : ℂ) : ℂ := deriv (theta rho) w / theta rho w

theorem hasDerivAt_eF (w : ℂ) : HasDerivAt eF (2 * Real.pi * Complex.I * eF w) w := by
  have h := ((hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
  have e : eF = fun x => Complex.exp (2 * Real.pi * Complex.I * id x) := rfl
  rw [e]
  convert h using 1
  simp only [id]
  ring

theorem deriv_theta_add_one (w : ℂ) : deriv (theta rho) (w + 1) = deriv (theta rho) w := by
  have h : (fun x => theta rho (x + 1)) = theta rho := funext fun x => theta_add_one rho x
  rw [← deriv_comp_add_const, h]

theorem thetaLog_add_one (w : ℂ) : thetaLog (w + 1) = thetaLog w := by
  simp [thetaLog, deriv_theta_add_one, theta_add_one]

theorem thetaLog_add_rho {w : ℂ} (hw : theta rho w ≠ 0) :
    thetaLog (w + rho) = thetaLog w - 2 * Real.pi * Complex.I := by
  have hτ := rho_im_pos
  set c : ℂ → ℂ := fun x => -(eF rho)⁻¹ * eF (-x) with hc
  have hcd : HasDerivAt c (-(eF rho)⁻¹ * (eF (-w) * (-(2 * Real.pi * Complex.I)))) w := by
    have h1 : HasDerivAt (fun x => eF (-x)) (2 * Real.pi * Complex.I * eF (-w) * (-1)) w :=
      (hasDerivAt_eF (-w)).comp w (hasDerivAt_id w).neg
    have := h1.const_mul (-(eF rho)⁻¹)
    convert this using 1
    ring
  have hf : (fun x => theta rho (x + rho)) = fun x => c x * theta rho x := by
    funext x; exact theta_add_tau hτ x
  have hθd : HasDerivAt (theta rho) (deriv (theta rho) w) w :=
    ((differentiable_theta hτ) w).hasDerivAt
  have h2 : deriv (theta rho) (w + rho) =
      -(eF rho)⁻¹ * (eF (-w) * (-(2 * Real.pi * Complex.I))) * theta rho w +
        c w * deriv (theta rho) w := by
    have h4 : deriv (fun x => theta rho (x + rho)) w = deriv (theta rho) (w + rho) :=
      deriv_comp_add_const (theta rho) rho w
    rw [← h4, hf]
    exact (hcd.mul hθd).deriv
  have h3 : theta rho (w + rho) = c w * theta rho w := by
    have := congrFun hf w
    simpa using this
  unfold thetaLog
  rw [h2, h3]
  have he1 := eF_ne_zero rho
  have he2 := eF_ne_zero (-w)
  have hc' : c w = -(eF rho)⁻¹ * eF (-w) := rfl
  rw [hc']
  field_simp
  ring

theorem isOpen_theta_ne_zero : IsOpen {w : ℂ | theta rho w ≠ 0} :=
  isOpen_ne_fun (differentiable_theta rho_im_pos).continuous continuous_const

theorem differentiableOn_thetaLog : DifferentiableOn ℂ thetaLog {w : ℂ | theta rho w ≠ 0} := by
  intro w hw
  have hd : Differentiable ℂ (deriv (theta rho)) := (differentiable_theta rho_im_pos).deriv
  exact (((hd w).div ((differentiable_theta rho_im_pos) w) hw)).differentiableWithinAt

theorem deriv_thetaLog_add_one (w : ℂ) : deriv thetaLog (w + 1) = deriv thetaLog w := by
  have h : (fun x => thetaLog (x + 1)) = thetaLog := funext thetaLog_add_one
  rw [← deriv_comp_add_const, h]

theorem deriv_thetaLog_add_rho {w : ℂ} (hw : theta rho w ≠ 0) :
    deriv thetaLog (w + rho) = deriv thetaLog w := by
  rw [← deriv_comp_add_const]
  have : (fun x => thetaLog (x + rho)) =ᶠ[𝓝 w] fun x => thetaLog x - 2 * Real.pi * Complex.I := by
    filter_upwards [isOpen_theta_ne_zero.mem_nhds hw] with x hx
    exact thetaLog_add_rho hx
  rw [this.deriv_eq, deriv_sub_const]

/-- `deriv ℓ`, set to `0` at the zeros of `θ`. -/
@[expose] noncomputable def thetaLogDeriv (w : ℂ) : ℂ :=
  if theta rho w = 0 then 0 else deriv thetaLog w

theorem thetaLogDeriv_add_one (w : ℂ) : thetaLogDeriv (w + 1) = thetaLogDeriv w := by
  unfold thetaLogDeriv
  by_cases h : theta rho w = 0
  · simp [h, theta_add_one]
  · simp [h, theta_add_one, deriv_thetaLog_add_one]

theorem thetaLogDeriv_add_rho (w : ℂ) : thetaLogDeriv (w + rho) = thetaLogDeriv w := by
  unfold thetaLogDeriv
  by_cases h : theta rho w = 0
  · have : theta rho (w + rho) = 0 := (theta_add_tau_eq_zero_iff rho_im_pos w).2 h
    simp [h, this]
  · have : theta rho (w + rho) ≠ 0 := fun h' => h ((theta_add_tau_eq_zero_iff rho_im_pos w).1 h')
    simp [h, this, deriv_thetaLog_add_rho h]

theorem thetaLogDeriv_add_lattice {l : ℂ} (hl : l ∈ hexPair.lattice) (w : ℂ) :
    thetaLogDeriv (w + l) = thetaLogDeriv w := by
  obtain ⟨m, n, rfl⟩ := mem_hexPair_lattice.1 hl
  have h1 : Function.Periodic thetaLogDeriv 1 := thetaLogDeriv_add_one
  have h2 : Function.Periodic thetaLogDeriv rho := thetaLogDeriv_add_rho
  have h3 := (h2.int_mul m).add_period (h1.int_mul n)
  simpa using h3 w

/-- The function `Ψ₀ = - (q'/q)' - ℘[L - 0]`, holomorphic on the unit disc. -/
@[expose] noncomputable def psiZero (w : ℂ) : ℂ :=
  -deriv thetaQlog w - hexPair.weierstrassPExcept 0 w

/-- `Φ = - ℓ' - ℘`, with the value `Ψ₀ 0` at the lattice points. -/
@[expose] noncomputable def phiElliptic (w : ℂ) : ℂ :=
  if theta rho w = 0 then psiZero 0 else -deriv thetaLog w - hexPair.weierstrassP w

theorem phiElliptic_add_lattice {l : ℂ} (hl : l ∈ hexPair.lattice) (w : ℂ) :
    phiElliptic (w + l) = phiElliptic w := by
  have hzero : theta rho (w + l) = 0 ↔ theta rho w = 0 := by
    rw [theta_eq_zero_iff_mem, theta_eq_zero_iff_mem]
    exact ⟨fun h => by simpa using hexPair.lattice.sub_mem h hl,
      fun h => hexPair.lattice.add_mem h hl⟩
  unfold phiElliptic
  by_cases h : theta rho w = 0
  · simp [h, hzero.2 h]
  · have h' : theta rho (w + l) ≠ 0 := fun h'' => h (hzero.1 h'')
    simp only [h, h', ↓reduceIte]
    have e1 := thetaLogDeriv_add_lattice hl w
    unfold thetaLogDeriv at e1
    simp only [h, h', ↓reduceIte] at e1
    rw [e1]
    have := hexPair.weierstrassP_add_coe w ⟨l, hl⟩
    simp only at this
    rw [this]

theorem exists_ball_eq_psiZero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    phiElliptic w = psiZero w := by
  by_cases hw0 : w = 0
  · subst hw0
    simp [phiElliptic, theta_zero]
  · have hw1 : ‖w‖ < 1 := by simpa using hw
    have hθ : theta rho w ≠ 0 := theta_ne_zero_of_norm_lt_one hw1 hw0
    simp only [phiElliptic, hθ, ↓reduceIte]
    -- ℓ = w⁻¹ + q'/q near `w`
    have hev : thetaLog =ᶠ[𝓝 w] fun x => x⁻¹ + thetaQlog x := by
      have hopen : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
      filter_upwards [hopen.mem_nhds ⟨hw, hw0⟩] with x hx
      have hx1 : ‖x‖ < 1 := by simpa using hx.1
      have hx0 : x ≠ 0 := hx.2
      have hqx := thetaQ_ne_zero_of_norm_lt_one hx1
      have hθ' : theta rho = fun y => y * thetaQ y := funext theta_eq_mul_thetaQ
      have hd : deriv (theta rho) x = thetaQ x + x * deriv thetaQ x := by
        rw [hθ']
        have h : HasDerivAt (fun y => y * thetaQ y) (1 * thetaQ x + x * deriv thetaQ x) x :=
          (hasDerivAt_id' x).mul (differentiable_thetaQ x).hasDerivAt
        rw [h.deriv]; ring
      unfold thetaLog thetaQlog
      rw [hd, theta_eq_mul_thetaQ]
      field_simp
    have hdq : DifferentiableAt ℂ thetaQlog w :=
      differentiableOn_thetaQlog.differentiableAt (isOpen_ball.mem_nhds hw)
    have hderiv : deriv thetaLog w = -(w ^ 2)⁻¹ + deriv thetaQlog w := by
      rw [hev.deriv_eq]
      exact ((hasDerivAt_inv hw0).add hdq.hasDerivAt).deriv
    have hP := hexPair.weierstrassPExcept_def (0 : hexPair.lattice) w
    simp only [ZeroMemClass.coe_zero] at hP
    unfold psiZero
    rw [hderiv, hP]
    simp only [zero_pow two_ne_zero, div_zero, sub_zero, one_div]
    ring

theorem differentiableOn_psiZero : DifferentiableOn ℂ psiZero (ball 0 1) := by
  have h1 : DifferentiableOn ℂ (deriv thetaQlog) (ball 0 1) :=
    differentiableOn_thetaQlog.deriv isOpen_ball
  have h2 : DifferentiableOn ℂ (hexPair.weierstrassPExcept 0) (ball 0 1) := by
    refine (hexPair.differentiableOn_weierstrassPExcept 0).mono ?_
    intro x hx hx'
    have hx1 : ‖x‖ < 1 := by simpa using hx
    have hmem : x ∈ hexPair.lattice ∧ x ≠ 0 := by simpa using hx'
    exact absurd (one_le_norm_of_mem_hexLattice hmem.1 hmem.2) (not_le.2 hx1)
  exact h1.neg.sub h2

theorem differentiable_phiElliptic : Differentiable ℂ phiElliptic := by
  have hball : DifferentiableAt ℂ phiElliptic 0 := by
    have h : phiElliptic =ᶠ[𝓝 0] psiZero := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with x hx
      exact exists_ball_eq_psiZero hx
    exact (differentiableOn_psiZero.differentiableAt (isOpen_ball.mem_nhds
      (mem_ball_self one_pos))).congr_of_eventuallyEq h
  intro w
  by_cases hw : theta rho w = 0
  · have hmem : w ∈ hexPair.lattice := (theta_eq_zero_iff_mem w).1 hw
    have hfun : phiElliptic = fun x => phiElliptic (x - w) := by
      funext x
      have := phiElliptic_add_lattice hmem (x - w)
      rw [sub_add_cancel] at this
      exact this
    have h0 : DifferentiableAt ℂ phiElliptic ((fun x : ℂ => x - w) w) := by simpa using hball
    have h1 := DifferentiableAt.comp (g := phiElliptic) (f := fun x : ℂ => x - w) w h0 (by fun_prop)
    have h2 : (phiElliptic ∘ fun x : ℂ => x - w) = phiElliptic := hfun.symm
    rwa [h2] at h1
  · have hopen := isOpen_theta_ne_zero.mem_nhds hw
    have hev : phiElliptic =ᶠ[𝓝 w] fun x => -deriv thetaLog x - hexPair.weierstrassP x := by
      filter_upwards [hopen] with x hx
      simp [phiElliptic, show theta rho x ≠ 0 from hx]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have h1 : DifferentiableAt ℂ (deriv thetaLog) w :=
      (differentiableOn_thetaLog.deriv isOpen_theta_ne_zero).differentiableAt hopen
    have hnot : w ∉ hexPair.lattice := fun h => hw ((theta_eq_zero_iff_mem w).2 h)
    have h2 : DifferentiableAt ℂ hexPair.weierstrassP w :=
      hexPair.differentiableOn_weierstrassP.differentiableAt
        (hexPair.isClosed_lattice.isOpen_compl.mem_nhds hnot)
    exact h1.neg.sub h2

/-- **Liouville.** `Φ` is constant. -/
theorem phiElliptic_const (z w : ℂ) : phiElliptic z = phiElliptic w := by
  have hcont : Continuous phiElliptic := differentiable_phiElliptic.continuous
  have hcompact := IsZLattice.isCompact_range_of_periodic hexPair.lattice phiElliptic hcont
    (fun z l hl => phiElliptic_add_lattice hl z)
  exact differentiable_phiElliptic.apply_eq_apply_of_bounded hcompact.isBounded z w

/-- **The Liouville step** of `cal:green-expansion`: `- (q'/q)' = ℘[L - 0] + κ` on the unit disc. -/
theorem exists_deriv_thetaQlog_eq :
    ∃ κ : ℂ, ∀ w ∈ ball (0 : ℂ) 1, -deriv thetaQlog w = hexPair.weierstrassPExcept 0 w + κ := by
  refine ⟨psiZero 0, fun w hw => ?_⟩
  have h1 := phiElliptic_const w 0
  rw [exists_ball_eq_psiZero hw, exists_ball_eq_psiZero (mem_ball_self one_pos)] at h1
  unfold psiZero at h1 ⊢
  linear_combination h1

end Calibration

end SandierSerfaty

end
