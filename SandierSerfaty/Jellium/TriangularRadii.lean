/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.CubeRadius
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic

/-!
# Radii for a lattice with minimal distance at least one

If every nonzero point of a lattice `Γ` has norm at least `1` (as for the triangular lattice, whose
nearest-neighbour distance is `√(2/√3) > 1`), then the nearest-neighbour radius is `¼` at every point
of `Γ` (`SandierSerfaty.nnRadius_eq_quarter`) and so is the radius relative to every square
(`SandierSerfaty.cubeRadius_eq_quarter`).
-/

open Set

public section

namespace SandierSerfaty

theorem nnRadius_eq_quarter {Γ : Submodule ℤ ℂ} (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {p : ℂ}
    (hp : p ∈ Γ) : nnRadius (Γ : Set ℂ) p = 1 / 4 := by
  have h : sInf (insert 1 ((fun q : ℂ ↦ ‖q - p‖) '' ((Γ : Set ℂ) \ {p}))) = 1 := by
    refine IsLeast.csInf_eq ⟨mem_insert _ _, ?_⟩
    intro y hy
    rcases hy with rfl | ⟨q, ⟨hq, hqp⟩, rfl⟩
    · exact le_rfl
    · exact hmin (q - p) (Γ.sub_mem hq hp) (sub_ne_zero.2 hqp)
  unfold nnRadius
  rw [h]; norm_num

theorem cubeRadius_eq_quarter {Γ : Submodule ℤ ℂ} (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {p : ℂ}
    (hp : p ∈ Γ) (ℓ : ℝ) : cubeRadius (Γ : Set ℂ) ℓ p = 1 / 4 := by
  unfold cubeRadius
  rw [nnRadius_eq_quarter hmin hp]
  split_ifs <;> ring

/-- The nonzero points of the triangular lattice have norm at least `1`. -/
theorem triangularLattice_norm_ge_one {γ : ℂ} (hγ : γ ∈ triangularLattice) (h0 : γ ≠ 0) :
    1 ≤ ‖γ‖ := by
  obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.1 hγ
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : √(2 / √3) ^ 2 = 2 / √3 := Real.sq_sqrt (by positivity)
  set s : ℝ := √(2 / √3) with hsd
  have hnorm : ‖m • ((s : ℝ) • (⟨1, 0⟩ : ℂ)) + n • ((s : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ))‖ ^ 2 =
      (2 / √3) * ((m : ℝ) ^ 2 + m * n + n ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, zsmul_eq_mul,
      smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]
    rw [← hs]
    linear_combination ((n : ℝ) ^ 2 * s ^ 2 / 4) * h3sq
  have hq : (1 : ℝ) ≤ (m : ℝ) ^ 2 + m * n + n ^ 2 := by
    have hmn : ¬ (m = 0 ∧ n = 0) := by
      rintro ⟨rfl, rfl⟩; apply h0; simp
    have : (1 : ℤ) ≤ m ^ 2 + m * n + n ^ 2 := by
      by_contra hlt
      push Not at hlt
      have h1 : n ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * m + n), sq_nonneg n]
      have hn : n = 0 := by nlinarith [sq_nonneg n]
      subst hn
      have : m ^ 2 ≤ 0 := by nlinarith
      have hm : m = 0 := by nlinarith [sq_nonneg m]
      exact hmn ⟨hm, rfl⟩
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ 2 / √3 := by
    rw [le_div_iff₀ h3]
    nlinarith [h3sq, h3]
  by_contra hlt
  push Not at hlt
  have hn0 := norm_nonneg (m • ((s : ℝ) • (⟨1, 0⟩ : ℂ)) + n • ((s : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)))
  nlinarith

end SandierSerfaty

end
