/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Constants
public import SandierSerfaty.Torus.Lattice
public import SandierSerfaty.ClosedForm.HexLattice
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# The Green-function coefficients `c_m` through Mathlib's `PeriodPair.G`

paper `cal:coefficients`: `k_m = 6m`, `c_m = k_m⁻¹ ∑_{z ∈ Λ_△ ∖ {0}} z^{-k_m}`.

* `triPair : PeriodPair` is the period pair `(a, a ρ)` with `ρ = (1/2, √3/2)`; its lattice *is*
  `triangularLattice` (`triPair_lattice`, by `rfl`), the lattice of the main statements.
* `coeff m := (triPair.G (6 m)).re / (6 m)`, where `PeriodPair.G n = ∑' l : lattice, (l ^ n)⁻¹`
  (Mathlib's definition). The lattice sum includes `l = 0`, which contributes `(0 ^ n)⁻¹ = 0` for `n > 0`,
  so for `m ≥ 1` this is exactly the paper's sum over `Λ_△ ∖ {0}`. For `m = 0` the value is junk (`0`); the
  auxiliary index `0` carries no coefficient (`b₀ = γ`).
* `triPair_G` relates `triPair.G n` to the hexagonal Eisenstein sums `hexPair.G n` of
  `ClosedForm/Eisenstein.lean` by the scale `a`: `G_n(Λ_△) = a⁻ⁿ G_n(ℤρ + ℤ)`.

Reality of `c_m` and `G_n = 0` for `6 ∤ n` are proved in other modules, not in this one.
-/

open Complex

public section

namespace SandierSerfaty

namespace Calibration

/-- The period pair `(a, a ρ)` of the triangular lattice; its lattice is `triangularLattice`. -/
@[expose] noncomputable def triPair : PeriodPair where
  ω₁ := (√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ)
  ω₂ := (√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)
  indep := by
    have h := (Torus.latticeBasis ((√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ))
      ((√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ))
      (by rw [Torus.triangular_det]; exact one_ne_zero)).linearIndependent
    have e : ⇑(Torus.latticeBasis ((√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ))
        ((√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ))
        (by rw [Torus.triangular_det]; exact one_ne_zero)) =
        ![(√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ), (√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)] := by
      funext i; exact Torus.latticeBasis_apply _ _ _ i
    rwa [e] at h

/-- The lattice of `triPair` is `triangularLattice`. -/
theorem triPair_lattice : triPair.lattice = triangularLattice := rfl

/-- The coefficient `c_m = (Re G_{6m}(Λ_△)) / (6m)` of `cal:coefficients` (see the module docstring). -/
@[expose] noncomputable def coeff (m : ℕ) : ℝ := (triPair.G (6 * m)).re / ((6 * m : ℕ) : ℝ)

theorem triPair_ω₁ : triPair.ω₁ = (a : ℂ) := by
  show ((√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ)) = _
  rw [Complex.real_smul]
  have : (⟨1, 0⟩ : ℂ) = 1 := Complex.ext (by simp) (by simp)
  rw [this]; simp [a]

theorem triPair_ω₂ : triPair.ω₂ = (a : ℂ) * ClosedForm.rho := by
  show ((√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)) = _
  rw [Complex.real_smul, ClosedForm.rho_eq]; rfl

/-- Multiplication by `a` is an equivalence from the hexagonal lattice `ℤρ + ℤ` onto the triangular
lattice (`Λ_△ = a (ℤ + ℤρ)`). -/
noncomputable def hexToTri : ClosedForm.hexPair.lattice ≃ triPair.lattice where
  toFun x := ⟨(a : ℂ) * x, by
    obtain ⟨m, n, hx⟩ := ClosedForm.mem_hexPair_lattice.1 x.2
    refine PeriodPair.mem_lattice.2 ⟨n, m, ?_⟩
    rw [triPair_ω₁, triPair_ω₂, ← hx]; ring⟩
  invFun y := ⟨(a : ℂ)⁻¹ * y, by
    obtain ⟨m, n, hy⟩ := PeriodPair.mem_lattice.1 y.2
    have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
    refine ClosedForm.mem_hexPair_lattice.2 ⟨n, m, ?_⟩
    rw [triPair_ω₁, triPair_ω₂] at hy
    rw [← hy]; field_simp; ring⟩
  left_inv x := by
    have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
    exact Subtype.ext (by simp only; field_simp)
  right_inv y := by
    have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
    exact Subtype.ext (by simp only; field_simp)

/-- `G_n(Λ_△) = a⁻ⁿ G_n(ℤρ + ℤ)`: the triangular Eisenstein sums are the hexagonal ones
(`ClosedForm/Eisenstein.lean`) rescaled by `a`. -/
theorem triPair_G (n : ℕ) : triPair.G n = ((a : ℂ) ^ n)⁻¹ * ClosedForm.hexPair.G n := by
  unfold PeriodPair.G
  rw [← hexToTri.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  show (((a : ℂ) * (x : ℂ)) ^ n)⁻¹ = ((a : ℂ) ^ n)⁻¹ * ((x : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

end Calibration

end SandierSerfaty
