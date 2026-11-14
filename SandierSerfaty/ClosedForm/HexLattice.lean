/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The hexagonal period pair

`rho = e^{iπ/3} = 1/2 + (√3/2) i`, the period pair `hexPair = (ρ, 1)` of Mathlib's `PeriodPair`
(closed-form note, Part C), and the two self-equivalences of its lattice `ℤ ρ + ℤ` that the note
uses: the rotation `ℓ ↦ ρ ℓ` and the conjugation `ℓ ↦ conj ℓ`.
-/

open Complex

public section

namespace SandierSerfaty

namespace ClosedForm

/-- The sixth root of unity `ρ = e^{iπ/3}`. -/
@[expose] noncomputable def rho : ℂ := Complex.exp (↑Real.pi * Complex.I / 3)

theorem rho_re : rho.re = 1 / 2 := by
  have : rho = Complex.exp (↑(Real.pi / 3) * Complex.I) := by
    unfold rho; congr 1; push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]

theorem rho_im : rho.im = √3 / 2 := by
  have : rho = Complex.exp (↑(Real.pi / 3) * Complex.I) := by
    unfold rho; congr 1; push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]

theorem rho_eq : rho = ⟨1 / 2, √3 / 2⟩ := Complex.ext (by simp [rho_re]) (by simp [rho_im])

theorem rho_sq : rho ^ 2 = rho - 1 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [pow_two, rho_re, rho_im] <;> nlinarith [h3]

theorem one_sub_rho_eq : 1 - rho = (starRingEnd ℂ) rho := by
  apply Complex.ext <;> simp [rho_re, rho_im]; norm_num

theorem rho_mul_one_sub : rho * (1 - rho) = 1 := by
  linear_combination -rho_sq

theorem rho_cube : rho ^ 3 = -1 := by
  linear_combination (rho + 1) * rho_sq

theorem rho_ne_zero : rho ≠ 0 := by
  intro h; have := rho_re; rw [h] at this; norm_num at this

theorem rho_sq_ne_one : rho ^ 2 ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [rho_sq] at this
  simp [rho_re] at this
  norm_num at this

theorem rho_pow_four_ne_one : rho ^ 4 ≠ 1 := by
  intro h
  have h4 : rho ^ 4 = -rho := by
    calc rho ^ 4 = rho ^ 3 * rho := by ring
      _ = -rho := by rw [rho_cube]; ring
  rw [h4] at h
  have := congrArg Complex.re h
  simp [rho_re] at this
  norm_num at this

theorem rho_im_pos : 0 < rho.im := by
  rw [rho_im]; positivity

/-- The period pair `(ρ, 1)` of the hexagonal lattice. -/
@[expose] noncomputable def hexPair : PeriodPair where
  ω₁ := rho
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [rho_im, rho_re] at him hre
    have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
    have hs : s = 0 := by
      have h0 : (s • rho + t • (1 : ℂ)).im = 0 := by rw [h]; rfl
      simpa [rho_im] using h0
    subst hs
    simp at hre
    exact ⟨rfl, hre⟩

@[simp] theorem hexPair_ω₁ : hexPair.ω₁ = rho := rfl
@[simp] theorem hexPair_ω₂ : hexPair.ω₂ = 1 := rfl

theorem mem_hexPair_lattice {x : ℂ} :
    x ∈ hexPair.lattice ↔ ∃ m n : ℤ, (m : ℂ) * rho + n = x := by
  rw [PeriodPair.mem_lattice]; simp

theorem one_mem_hexLattice : (1 : ℂ) ∈ hexPair.lattice :=
  hexPair.ω₂_mem_lattice

theorem rho_mul_mem {x : ℂ} (hx : x ∈ hexPair.lattice) : rho * x ∈ hexPair.lattice := by
  obtain ⟨m, n, rfl⟩ := mem_hexPair_lattice.1 hx
  refine mem_hexPair_lattice.2 ⟨m + n, -m, ?_⟩
  push_cast
  linear_combination (-(m : ℂ)) * rho_sq

theorem one_sub_rho_mul_mem {x : ℂ} (hx : x ∈ hexPair.lattice) :
    (1 - rho) * x ∈ hexPair.lattice := by
  obtain ⟨m, n, rfl⟩ := mem_hexPair_lattice.1 hx
  refine mem_hexPair_lattice.2 ⟨-n, m + n, ?_⟩
  push_cast
  linear_combination (m : ℂ) * rho_sq

theorem conj_mem {x : ℂ} (hx : x ∈ hexPair.lattice) :
    (starRingEnd ℂ) x ∈ hexPair.lattice := by
  obtain ⟨m, n, rfl⟩ := mem_hexPair_lattice.1 hx
  refine mem_hexPair_lattice.2 ⟨-m, m + n, ?_⟩
  push_cast
  simp only [map_add, map_mul, map_intCast, ← one_sub_rho_eq]
  ring

/-- Multiplication by `ρ` as a self-equivalence of the lattice. -/
@[expose] noncomputable def rotEquiv : hexPair.lattice ≃ hexPair.lattice where
  toFun x := ⟨rho * x, rho_mul_mem x.2⟩
  invFun x := ⟨(1 - rho) * x, one_sub_rho_mul_mem x.2⟩
  left_inv x := Subtype.ext (by
    simp only; rw [← mul_assoc, mul_comm (1 - rho), rho_mul_one_sub, one_mul])
  right_inv x := Subtype.ext (by
    simp only; rw [← mul_assoc, rho_mul_one_sub, one_mul])

/-- Complex conjugation as a self-equivalence of the lattice. -/
@[expose] noncomputable def conjEquiv : hexPair.lattice ≃ hexPair.lattice where
  toFun x := ⟨(starRingEnd ℂ) x, conj_mem x.2⟩
  invFun x := ⟨(starRingEnd ℂ) x, conj_mem x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

@[simp] theorem rotEquiv_apply (x : hexPair.lattice) : (rotEquiv x : ℂ) = rho * x := rfl
@[simp] theorem conjEquiv_apply (x : hexPair.lattice) :
    (conjEquiv x : ℂ) = (starRingEnd ℂ) x := rfl

/-- The point `p = (1 + ρ)/3`, with `ρ² p = p - 1` and `conj p = 1 - p`. -/
@[expose] noncomputable def pt : ℂ := (1 + rho) / 3

theorem pt_not_mem : pt ∉ hexPair.lattice := by
  have := (hexPair.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 3) (β := 1 / 3)).not.mpr (by
    intro h; have := h.1; simp at this)
  intro hp
  apply this
  convert hp using 1
  simp [pt]; ring

theorem rho_sq_mul_pt : rho ^ 2 * pt = pt - 1 := by
  unfold pt
  linear_combination (1 / 3 : ℂ) * rho_cube + (1 / 3 : ℂ) * rho_sq

theorem conj_pt : (starRingEnd ℂ) pt = 1 - pt := by
  unfold pt
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := Complex.conj_ofReal 3
  rw [map_div₀, map_add, map_one, h3, ← one_sub_rho_eq]
  ring

end ClosedForm

end SandierSerfaty
