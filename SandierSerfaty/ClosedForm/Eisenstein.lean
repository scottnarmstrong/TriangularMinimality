/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.HexLattice
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Eisenstein series of the hexagonal lattice and `Δ(ρ)`

Closed-form note, Lemmas `lem:C1` and `lem:C2`. With `hexPair = (ρ, 1)` and `G_k = hexPair.G k`:

* `hexG_eq` (C1): `G_k = 2 ζ(k) E_k(ρ)` for `k ≥ 3`, `E_k` Mathlib's normalized `ModularForm.E`;
* `hexG_four` (C2a): `G_4 = 0`, `E₄(ρ) = 0`;
* `conj_hexG_six` (C2b): `G_6` is real;
* `discriminant_rhoH` (C2c): `Δ(ρ) = -E₆(ρ)²/1728`, and `E₆(ρ) ≠ 0`;
* `riemannZeta_six` (C2d): `ζ(6) = π⁶/945`, and `g₃ = (8π⁶/27) E₆(ρ)`.
-/

open Complex

public section

namespace SandierSerfaty

namespace ClosedForm

/-- `ρ` as a point of the upper half-plane. -/
@[expose] noncomputable def rhoH : UpperHalfPlane := ⟨rho, rho_im_pos⟩

@[simp] theorem coe_rhoH : (rhoH : ℂ) = rho := rfl

/-- C1, the lattice sum as a sum over `ℤ²`. -/
theorem hexG_eq_tsum_prod (k : ℕ) :
    hexPair.G k = ∑' v : ℤ × ℤ, (((v.1 : ℂ) * rho + v.2) ^ k)⁻¹ := by
  unfold PeriodPair.G
  rw [← (hexPair.latticeEquivProd.symm.toEquiv).tsum_eq]
  refine tsum_congr fun v => ?_
  have := hexPair.latticeEquiv_symm_apply v
  simp only [LinearEquiv.coe_toEquiv, this, hexPair_ω₁, hexPair_ω₂, mul_one]

/-- C1: `G_k = 2 ζ(k) E_k(ρ)` for `k ≥ 3`. -/
theorem hexG_eq {k : ℕ} (hk : 3 ≤ k) :
    hexPair.G k = 2 * riemannZeta k * ModularForm.E hk rhoH := by
  rw [hexG_eq_tsum_prod]
  have h1 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk rhoH
  have h2 : ModularForm.E hk rhoH = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k rhoH := by
    show (1 / 2 : ℂ) • EisensteinSeries.eisensteinSeriesSIF (N := 1) 0 k rhoH = _
    rw [EisensteinSeries.eisensteinSeriesSIF_apply]; rfl
  rw [h2, show (2 : ℂ) * riemannZeta k * (1 / 2 * eisensteinSeries (N := 1) 0 k rhoH) =
    riemannZeta k * eisensteinSeries (N := 1) 0 k rhoH by ring, ← h1]
  rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  refine tsum_congr fun v => ?_
  simp [EisensteinSeries.eisSummand, zpow_neg]

/-- Rotation invariance of the lattice sums: `G_n = ρ⁻ⁿ G_n`. -/
theorem hexG_rot (n : ℕ) : hexPair.G n = (rho ^ n)⁻¹ * hexPair.G n := by
  unfold PeriodPair.G
  rw [← tsum_mul_left, ← rotEquiv.tsum_eq (fun l : hexPair.lattice => ((l : ℂ) ^ n)⁻¹)]
  refine tsum_congr fun l => ?_
  simp only [rotEquiv_apply, mul_pow, mul_inv]

/-- `G_n` is real: `conj G_n = G_n`. -/
theorem conj_hexG (n : ℕ) : (starRingEnd ℂ) (hexPair.G n) = hexPair.G n := by
  unfold PeriodPair.G
  rw [Complex.conj_tsum, ← conjEquiv.tsum_eq (fun l : hexPair.lattice => ((l : ℂ) ^ n)⁻¹)]
  refine tsum_congr fun l => ?_
  simp only [conjEquiv_apply, map_inv₀, map_pow]

/-- C2(a): `G₄ = 0`. -/
theorem hexG_four : hexPair.G 4 = 0 := by
  have h := hexG_rot 4
  have hne : (rho ^ 4)⁻¹ ≠ 1 := by
    intro h1; apply rho_pow_four_ne_one
    simpa using h1
  have : (1 - (rho ^ 4)⁻¹) * hexPair.G 4 = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    have h3 := bernoulli'_three
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]
  have c : Nat.choose 6 2 = 15 := by decide
  have c' : Nat.choose 6 4 = 15 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, bernoulli'_four, h5]

/-- C2(d): `ζ(6) = π⁶/945`. -/
theorem riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
  have h6 : bernoulli (2 * 3) = 1 / 42 := hb
  rw [h6] at h
  norm_num [Nat.factorial] at h
  rw [h]
  ring

theorem pi_ne_zero_complex : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-- C2(a): `E₄(ρ) = 0`. -/
theorem E₄_rhoH : ModularForm.E₄ rhoH = 0 := by
  have h := hexG_eq (k := 4) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  rw [hexG_four, riemannZeta_four] at h
  have hz : (2 : ℂ) * ((Real.pi : ℂ) ^ 4 / 90) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (div_ne_zero (pow_ne_zero _ pi_ne_zero_complex) (by norm_num))
  exact (mul_eq_zero.1 h.symm).resolve_left hz

/-- C2(c): `Δ(ρ) = -E₆(ρ)²/1728`. -/
theorem discriminant_rhoH : ModularForm.discriminant rhoH = -(ModularForm.E₆ rhoH) ^ 2 / 1728 := by
  rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, E₄_rhoH]
  ring

/-- C2(c): `E₆(ρ) ≠ 0`. -/
theorem E₆_rhoH_ne_zero : ModularForm.E₆ rhoH ≠ 0 := by
  intro h
  apply ModularForm.discriminant_ne_zero rhoH
  rw [discriminant_rhoH, h]; ring

/-- C2(d): `g₂ = 0`. -/
theorem hexPair_g₂ : hexPair.g₂ = 0 := by
  unfold PeriodPair.g₂; rw [hexG_four]; ring

/-- C2(d): `g₃ = (8π⁶/27) E₆(ρ)`. -/
theorem hexPair_g₃ : hexPair.g₃ = 8 * (Real.pi : ℂ) ^ 6 / 27 * ModularForm.E₆ rhoH := by
  unfold PeriodPair.g₃
  have h := hexG_eq (k := 6) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  rw [h, riemannZeta_six]
  ring

end ClosedForm

end SandierSerfaty
