/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.WeierstrassHex
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Topology.Compactness.Lindelof

/-!
# `℘'' = 6 ℘²` for the hexagonal lattice

The closed-form note's Lemma C4: on `U = ℂ \ Λ` the function
`℘'(℘'' - 6℘²)` vanishes (differentiate `℘'² = 4℘³ - g₃`), and `℘'(p) ≠ 0` at the point `p = (1 + ρ)/3`
because `℘'(p)² = -g₃ ≠ 0`; the identity theorem on the connected open set `U` gives `℘'' = 6℘²`.
-/

open Complex Filter Topology
open scoped PeriodPair

public section

namespace SandierSerfaty

namespace ClosedForm

/-- The complement of the hexagonal lattice. -/
@[expose] def hexU : Set ℂ := (hexPair.lattice : Set ℂ)ᶜ

theorem isOpen_hexU : IsOpen hexU := hexPair.isClosed_lattice.isOpen_compl

theorem isPreconnected_hexU : IsPreconnected hexU := by
  have hc : (hexPair.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := hexPair.lattice)
  exact (hc.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

theorem analyticOnNhd_wp : AnalyticOnNhd ℂ ℘[hexPair] hexU := hexPair.analyticOnNhd_weierstrassP

theorem analyticOnNhd_dwp : AnalyticOnNhd ℂ ℘'[hexPair] hexU := hexPair.analyticOnNhd_derivWeierstrassP

theorem hasDerivAt_wp {z : ℂ} (hz : z ∈ hexU) : HasDerivAt ℘[hexPair] (℘'[hexPair] z) z := by
  have h := (analyticOnNhd_wp z hz).differentiableAt.hasDerivAt
  rwa [PeriodPair.deriv_weierstrassP] at h

theorem hasDerivAt_dwp {z : ℂ} (hz : z ∈ hexU) :
    HasDerivAt ℘'[hexPair] (deriv ℘'[hexPair] z) z :=
  (analyticOnNhd_dwp z hz).differentiableAt.hasDerivAt

theorem dwp_sq {z : ℂ} (hz : z ∈ hexU) :
    ℘'[hexPair] z ^ 2 = 4 * ℘[hexPair] z ^ 3 - hexPair.g₃ := by
  have h := hexPair.derivWeierstrassP_sq z hz
  rw [hexPair_g₂] at h
  linear_combination h

/-- `℘'(℘'' - 6 ℘²) = 0` on `U`. -/
theorem dwp_mul_eq_zero {z : ℂ} (hz : z ∈ hexU) :
    ℘'[hexPair] z * (deriv ℘'[hexPair] z - 6 * ℘[hexPair] z ^ 2) = 0 := by
  have h1 : HasDerivAt (fun w => ℘'[hexPair] w ^ 2) (2 * ℘'[hexPair] z * deriv ℘'[hexPair] z) z := by
    refine ((hasDerivAt_dwp hz).pow 2).congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun w => 4 * ℘[hexPair] w ^ 3 - hexPair.g₃)
      (4 * (3 * ℘[hexPair] z ^ 2 * ℘'[hexPair] z)) z := by
    have := ((hasDerivAt_wp hz).pow 3).const_mul 4
    simpa using this.sub_const hexPair.g₃
  have hev : (fun w => ℘'[hexPair] w ^ 2) =ᶠ[𝓝 z] fun w => 4 * ℘[hexPair] w ^ 3 - hexPair.g₃ := by
    filter_upwards [isOpen_hexU.mem_nhds hz] with w hw using dwp_sq hw
  have := h1.unique (h2.congr_of_eventuallyEq hev)
  linear_combination this / 2

/-- C4: `℘'' = 6 ℘²` off the lattice. -/
theorem deriv_dwp_eq {z : ℂ} (hz : z ∈ hexU) :
    deriv ℘'[hexPair] z = 6 * ℘[hexPair] z ^ 2 := by
  have hp : pt ∈ hexU := pt_not_mem
  have hF : AnalyticOnNhd ℂ (fun w => deriv ℘'[hexPair] w - 6 * ℘[hexPair] w ^ 2) hexU :=
    analyticOnNhd_dwp.deriv.sub ((analyticOnNhd_wp.pow 2).const_smul (c := (6 : ℂ)) |>.congr
      isOpen_hexU (fun w _ => by simp))
  have hne : ℘'[hexPair] pt ≠ 0 := by
    intro h
    have := derivWeierstrassP_pt_sq
    rw [h] at this
    exact hexPair_g₃_ne_zero (by linear_combination this)
  have hev : ∀ᶠ w in 𝓝 pt, ℘'[hexPair] w ≠ 0 :=
    (analyticOnNhd_dwp pt hp).continuousAt.eventually_ne hne
  have hz0 : (fun w => deriv ℘'[hexPair] w - 6 * ℘[hexPair] w ^ 2) =ᶠ[𝓝 pt] 0 := by
    filter_upwards [hev, isOpen_hexU.mem_nhds hp] with w hw hwU
    exact (mul_eq_zero.1 (dwp_mul_eq_zero hwU)).resolve_left hw
  have := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_hexU hp hz0 hz
  simpa [sub_eq_zero] using this

end ClosedForm

end SandierSerfaty
