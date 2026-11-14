/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.ThetaMean
public import SandierSerfaty.ClosedForm.RobinTheta
public import SandierSerfaty.Calibration.GreenSymmetry
public import SandierSerfaty.ClosedForm.Eisenstein

/-!
# The Robin constant of the triangular lattice

The closed-form note's Part B, Theorem B: with `ρ = e^{iπ/3}`, `b = Im ρ = √3/2` and
`a = √(2/√3) = b^{-1/2}` (so `Λ_△ = a (ℤ + ℤ ρ)`),

`R_△ = torusRobin Λ_△ = -log (2 π √b) - (1/12) log ‖Δ(ρ)‖`

(`SandierSerfaty.ClosedForm.torusRobin_triangularLattice`).

## Route

On main, `torusGreen Λ_△ = greenOne a ρ - c` off the lattice (`Calibration.exists_torusGreen_eq_greenOne_sub`)
for some constant `c`, with `greenOne a ρ z = Ĝ_ρ (z / a)` the theta Green function. Then:

* `triangular_const_eq`: `c = -π b / 6`. The mean of `torusGreen Λ_△` over the fundamental domain
  `V = [0, a) × [0, a b)` vanishes, while the mean of `greenOne a ρ` over `V` is `-π b / 6`
  (`integral_greenOne_rect`, Jensen on horizontal slices); `V` has area `a² b = 1`.
* `tendsto_greenOne_add_log_explicit`: the regular part of `greenOne a ρ` at `0` is
  `-log (2 π ‖Π‖²) + log a` with `Π = ∏ₙ (1 - qⁿ)`, `q = e^{2π i ρ}`.
* `norm_discriminant_eq_thetaR`: `‖Δ(ρ)‖ = e^{-2 π b} ‖Π‖²⁴`.
-/

open Filter Topology MeasureTheory Set Complex
open SandierSerfaty.Torus SandierSerfaty.Calibration

public section

namespace SandierSerfaty

namespace ClosedForm

/-- `Λ_△ = a (ℤ + ℤ ρ)`. -/
theorem mem_triangularLattice_iff (z : ℂ) :
    z ∈ triangularLattice ↔ ∃ m n : ℤ, z = (a : ℂ) * (m + n * rho) := by
  rw [← triPair_lattice, PeriodPair.mem_lattice, triPair_ω₁, triPair_ω₂]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by rw [← h]; ring⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by rw [h]; ring⟩

theorem a_sq_mul_rho_im : a ^ 2 * rho.im = 1 := by
  rw [a_sq, rho_im]
  have := sqrt_three_pos
  field_simp

/-- The rectangle `[0, a) × [0, a b)`, a fundamental domain of `Λ_△`. -/
@[expose] def triRect : Set ℂ := {z : ℂ | z.re ∈ Ico 0 a ∧ z.im ∈ Ico 0 (a * rho.im)}

theorem isAddFundamentalDomain_triRect :
    IsAddFundamentalDomain triangularLattice triRect volume :=
  isAddFundamentalDomain_rect triangularLattice a_pos rho_im_pos mem_triangularLattice_iff

/-- The constant `c` in `torusGreen Λ_△ = greenOne a ρ - c` is `-π b / 6`. -/
theorem triangular_const_eq {c : ℝ}
    (hc : ∀ z, z ∉ triangularLattice → torusGreen triangularLattice z = greenOne (a : ℂ) rho z - c) :
    c = -(Real.pi * rho.im / 6) := by
  set Γ := triangularLattice with hΓ
  have hFD := isAddFundamentalDomain_triRect
  have hTD := (torusDomain_spec Γ).1
  have hvol : volume.real triRect = 1 := by
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain Γ volume hFD]
    exact Torus.covolume_triangularLattice
  have hfin : volume triRect ≠ ⊤ := by
    intro h
    rw [measureReal_def, h] at hvol
    simp at hvol
  have hper : ∀ γ ∈ Γ, ∀ x, torusGreen Γ (x + γ) = torusGreen Γ x :=
    fun γ hγ x => torusGreen_add_period Γ hγ x
  have hper' : ∀ (g : Γ) (x : ℂ), torusGreen Γ (g +ᵥ x) = torusGreen Γ x := fun g x => by
    have : g +ᵥ x = (g : ℂ) + x := rfl
    rw [this, add_comm]; exact hper g g.2 x
  have hIntG : IntegrableOn (torusGreen Γ) triRect :=
    (hFD.integrableOn_iff hTD hper').2 (integrableOn_torusGreen Γ)
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ (Γ : Set ℂ) := (countable_lattice Γ).ae_notMem volume
  have hg : greenOne (a : ℂ) rho =ᵐ[volume.restrict triRect] fun z => torusGreen Γ z + c := by
    filter_upwards [ae_restrict_of_ae hae] with z hz
    have := hc z hz
    linarith
  have hIntgo : IntegrableOn (greenOne (a : ℂ) rho) triRect :=
    (hIntG.add (integrableOn_const hfin (C := c))).congr_fun_ae hg.symm
  have h0 : ∫ z in triRect, torusGreen Γ z = 0 := by
    rw [← (torusDomain_spec Γ).2 triRect hFD _ hper]
    exact integral_torusGreen Γ
  have h1 : ∫ z in triRect, greenOne (a : ℂ) rho z =
      (∫ z in triRect, torusGreen Γ z) + c * volume.real triRect := by
    rw [integral_congr_ae hg, integral_add hIntG (integrableOn_const hfin), setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have h2 := integral_greenOne_rect rho_im_pos a_pos hIntgo
  have h3 : ∫ z in triRect, greenOne (a : ℂ) rho z = -(Real.pi * rho.im / 6) := by
    have : (a * rho.im) ^ 2 = rho.im * (a ^ 2 * rho.im) := by ring
    simp only [triRect]
    rw [h2, this, a_sq_mul_rho_im]
    ring
  rw [h0, hvol] at h1
  linarith

/-- **Theorem B.** `R_△ = -log (2 π) + log a - (1/12) log ‖Δ(ρ)‖`, with `a = b^{-1/2}`. -/
theorem torusRobin_triangularLattice :
    torusRobin triangularLattice =
      -Real.log (2 * Real.pi) + Real.log a -
        (1 / 12) * Real.log ‖ModularForm.discriminant rhoH‖ := by
  obtain ⟨c, hc⟩ := exists_torusGreen_eq_greenOne_sub
  have hcc := triangular_const_eq hc
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have hlim := tendsto_greenOne_add_log_explicit (τ := rho) rho_im_pos ha
  have hlim' : Tendsto (fun z : ℂ => torusGreen triangularLattice z + Real.log ‖z‖) (𝓝[≠] 0)
      (𝓝 (-Real.log ‖thetaDeriv0 rho‖ + Real.log ‖(a : ℂ)‖ - c)) := by
    refine (hlim.sub_const c).congr' ?_
    filter_upwards [eventually_notMem_lattice triangularLattice] with z hz
    rw [hc z hz]
    ring
  have hR := tendsto_nhds_unique (tendsto_torusGreen_add_log triangularLattice) hlim'
  rw [hR, hcc, norm_thetaDeriv0]
  have hP0 : 0 < ‖thetaR (eF rho) 1‖ := norm_pos_iff.2 (thetaR_one_ne_zero rho_im_pos)
  have hΔ := norm_discriminant_eq_thetaR rhoH
  have hrim : (rhoH : ℂ).im = rho.im := rfl
  have hrho : (rhoH : ℂ) = rho := rfl
  rw [hrim, hrho] at hΔ
  have hlogΔ : Real.log ‖ModularForm.discriminant rhoH‖ =
      -(2 * Real.pi * rho.im) + 24 * Real.log ‖thetaR (eF rho) 1‖ := by
    rw [hΔ, Real.log_mul (Real.exp_pos _).ne' (pow_pos hP0 24).ne', Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [Complex.norm_real, Real.norm_of_nonneg a_pos.le,
    Real.log_mul (by positivity) (pow_pos hP0 2).ne', Real.log_pow, hlogΔ]
  push_cast
  ring

end ClosedForm

end SandierSerfaty

end
