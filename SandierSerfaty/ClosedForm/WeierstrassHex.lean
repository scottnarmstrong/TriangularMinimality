/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.Eisenstein

/-!
# Symmetries of `℘` for the hexagonal lattice and the sign of `g₃`

The closed-form note's Lemma C3. Write `℘ = ℘[hexPair]`, `℘' = ℘'[hexPair]`. We prove:

* `weierstrassP_conj`, `derivWeierstrassP_conj`: `℘(z̄) = conj ℘(z)`, `℘'(z̄) = conj ℘'(z)`;
* `weierstrassP_rot`: `℘(ρ z) = ρ⁻² ℘(z)`;
* `hexE`: `e = ℘(1/2)` is real, with `℘'(1/2) = 0` and `4 e³ = g₃`;
* `weierstrassP_pt`: `℘(p) = 0` for `p = (1 + ρ)/3`, and `℘'(p)² = -g₃`;
* `hexG3_pos`, `hexE_pos`: `g₃ > 0` and `e > 0`.
-/

open Complex
open scoped PeriodPair

public section

namespace SandierSerfaty

namespace ClosedForm

/-- C3(a): `℘(z̄) = conj ℘(z)`. -/
theorem weierstrassP_conj (z : ℂ) :
    ℘[hexPair] ((starRingEnd ℂ) z) = (starRingEnd ℂ) (℘[hexPair] z) := by
  unfold PeriodPair.weierstrassP
  rw [Complex.conj_tsum,
    ← conjEquiv.tsum_eq (fun l : hexPair.lattice => 1 / ((starRingEnd ℂ) z - l) ^ 2 - 1 / (l : ℂ) ^ 2)]
  refine tsum_congr fun l => ?_
  simp only [conjEquiv_apply, map_sub, map_div₀, map_pow, map_one]

/-- C3(a): `℘'(z̄) = conj ℘'(z)`. -/
theorem derivWeierstrassP_conj (z : ℂ) :
    ℘'[hexPair] ((starRingEnd ℂ) z) = (starRingEnd ℂ) (℘'[hexPair] z) := by
  unfold PeriodPair.derivWeierstrassP
  rw [map_neg, Complex.conj_tsum,
    ← conjEquiv.tsum_eq (fun l : hexPair.lattice => 2 / ((starRingEnd ℂ) z - l) ^ 3)]
  congr 1
  refine tsum_congr fun l => ?_
  simp only [conjEquiv_apply, map_sub, map_div₀, map_pow, map_ofNat]

/-- C3(b): `℘(ρ z) = ρ⁻² ℘(z)`. -/
theorem weierstrassP_rot (z : ℂ) : ℘[hexPair] (rho * z) = (rho ^ 2)⁻¹ * ℘[hexPair] z := by
  unfold PeriodPair.weierstrassP
  rw [← tsum_mul_left,
    ← rotEquiv.tsum_eq (fun l : hexPair.lattice => 1 / (rho * z - l) ^ 2 - 1 / (l : ℂ) ^ 2)]
  refine tsum_congr fun l => ?_
  simp only [rotEquiv_apply]
  have h := rho_ne_zero
  rw [← mul_sub, mul_pow, mul_pow]
  field_simp

/-- C3(c): `℘` is real on the real axis. -/
theorem weierstrassP_real (x : ℝ) : ∃ r : ℝ, ℘[hexPair] (x : ℂ) = r := by
  have h := weierstrassP_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_real.1 h.symm

/-- C3(c): `℘'` is real on the real axis. -/
theorem derivWeierstrassP_real (x : ℝ) : ∃ r : ℝ, ℘'[hexPair] (x : ℂ) = r := by
  have h := derivWeierstrassP_conj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_real.1 h.symm

theorem half_not_mem : (1 / 2 : ℂ) ∉ hexPair.lattice := by
  have := hexPair.ω₂_div_two_notMem_lattice
  simpa using this

/-- C3(d): `℘'(1/2) = 0`. -/
theorem derivWeierstrassP_half : ℘'[hexPair] (1 / 2 : ℂ) = 0 := by
  have h1 := hexPair.derivWeierstrassP_sub_coe (1 / 2 : ℂ) ⟨1, one_mem_hexLattice⟩
  have h2 := hexPair.derivWeierstrassP_neg (1 / 2 : ℂ)
  simp only at h1
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by ring, h2] at h1
  linear_combination (-1 / 2 : ℂ) * h1

/-- C3(d): the real number `e = ℘(1/2)`. -/
theorem exists_hexE : ∃ e : ℝ, ℘[hexPair] (1 / 2 : ℂ) = e := by
  obtain ⟨r, hr⟩ := weierstrassP_real (1 / 2)
  refine ⟨r, ?_⟩
  rw [← hr]; congr 1; push_cast; ring

/-- The real number `e = ℘(1/2)`. -/
@[expose] noncomputable def hexE : ℝ := (℘[hexPair] (1 / 2 : ℂ)).re

theorem weierstrassP_half : ℘[hexPair] (1 / 2 : ℂ) = (hexE : ℂ) := by
  obtain ⟨e, he⟩ := exists_hexE
  unfold hexE
  rw [he, Complex.ofReal_re]

/-- C3(d): `4 e³ = g₃`. -/
theorem four_mul_hexE_cube : 4 * (hexE : ℂ) ^ 3 = hexPair.g₃ := by
  have h := hexPair.derivWeierstrassP_sq (1 / 2 : ℂ) half_not_mem
  rw [derivWeierstrassP_half, weierstrassP_half, hexPair_g₂] at h
  linear_combination -h

/-- C3(e): `℘(p) = 0`. -/
theorem weierstrassP_pt : ℘[hexPair] pt = 0 := by
  have h1 : ℘[hexPair] (rho ^ 2 * pt) = ℘[hexPair] pt := by
    rw [rho_sq_mul_pt]
    simpa using hexPair.weierstrassP_sub_coe pt ⟨1, one_mem_hexLattice⟩
  have h2 : ℘[hexPair] (rho ^ 2 * pt) = (rho ^ 2)⁻¹ * ((rho ^ 2)⁻¹ * ℘[hexPair] pt) := by
    rw [pow_two, mul_assoc, weierstrassP_rot, weierstrassP_rot, ← pow_two]
  rw [h2] at h1
  have hne : (rho ^ 2)⁻¹ * (rho ^ 2)⁻¹ ≠ 1 := by
    intro h
    apply rho_pow_four_ne_one
    have h' : (rho ^ 2 * rho ^ 2) ≠ 0 := mul_ne_zero (pow_ne_zero _ rho_ne_zero)
      (pow_ne_zero _ rho_ne_zero)
    rw [← mul_inv, inv_eq_one] at h
    rw [← h]; ring
  have : (1 - (rho ^ 2)⁻¹ * (rho ^ 2)⁻¹) * ℘[hexPair] pt = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)

/-- C3(e): `℘'(p)² = -g₃`. -/
theorem derivWeierstrassP_pt_sq : ℘'[hexPair] pt ^ 2 = -hexPair.g₃ := by
  have h := hexPair.derivWeierstrassP_sq pt pt_not_mem
  rw [weierstrassP_pt, hexPair_g₂] at h
  linear_combination h

/-- C3(e): `℘'(p)` is purely imaginary. -/
theorem conj_derivWeierstrassP_pt :
    (starRingEnd ℂ) (℘'[hexPair] pt) = -℘'[hexPair] pt := by
  rw [← derivWeierstrassP_conj, conj_pt]
  have h1 := hexPair.derivWeierstrassP_sub_coe (1 - pt) ⟨1, one_mem_hexLattice⟩
  simp only at h1
  rw [show (1 - pt - 1 : ℂ) = -pt by ring, hexPair.derivWeierstrassP_neg] at h1
  linear_combination -h1

theorem hexG3_eq_normSq : hexPair.g₃ = (Complex.normSq (℘'[hexPair] pt) : ℂ) := by
  have h := derivWeierstrassP_pt_sq
  have h2 := Complex.mul_conj (℘'[hexPair] pt)
  rw [conj_derivWeierstrassP_pt] at h2
  linear_combination h + h2

theorem hexPair_g₃_ne_zero : hexPair.g₃ ≠ 0 := by
  rw [hexPair_g₃]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ pi_ne_zero_complex))
    (by norm_num)) E₆_rhoH_ne_zero

/-- The real number `g₃`. -/
@[expose] noncomputable def hexG3 : ℝ := Complex.normSq (℘'[hexPair] pt)

theorem hexPair_g₃_eq : hexPair.g₃ = (hexG3 : ℂ) := hexG3_eq_normSq

/-- C3(f): `g₃ > 0`. -/
theorem hexG3_pos : 0 < hexG3 := by
  have h0 : 0 ≤ hexG3 := Complex.normSq_nonneg _
  refine lt_of_le_of_ne h0 fun h => hexPair_g₃_ne_zero ?_
  rw [hexPair_g₃_eq, ← h]; simp

/-- C3(f): `e > 0`. -/
theorem hexE_pos : 0 < hexE := by
  have h := four_mul_hexE_cube
  rw [hexPair_g₃_eq] at h
  have h' : 4 * hexE ^ 3 = hexG3 := by exact_mod_cast h
  by_contra hle
  replace hle := not_lt.1 hle
  have : hexE ^ 3 ≤ 0 := by
    have := neg_nonneg.2 hle
    nlinarith [sq_nonneg hexE, mul_nonneg this (sq_nonneg hexE)]
  linarith [hexG3_pos]

/-- `4 e³ = g₃` in `ℝ`. -/
theorem four_mul_hexE_cube_real : 4 * hexE ^ 3 = hexG3 := by
  have h := four_mul_hexE_cube
  rw [hexPair_g₃_eq] at h
  exact_mod_cast h

end ClosedForm

end SandierSerfaty
