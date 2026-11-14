/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.GreenExpansion

/-!
# The shells of the triangular lattice

The geometry of the regular Voronoi hexagon of `Λ_△` (used in the paper's proof of `cal:energy-identity`).
With `ρ = e^{iπ/3}` (`ClosedForm.rho`), `Λ_△ = a (ℤ + ℤ ρ)`, `a = Cal.a`.

* `mem_triangularLattice_iff`: `z ∈ Λ_△ ↔ ∃ m n : ℤ, z = a (m ρ + n)`;
* `rho_mul_mem_tri`: `ρ Λ_△ ⊆ Λ_△`;
* `norm_sq_hex`: `‖m ρ + n‖² = m² + m n + n²`;
* `hex_shell`: a nonzero point `w = m ρ + n` is one of the six units `ρ^j` (`j < 6`) or has `‖w‖² ≥ 3`;
* `tri_shell`: a nonzero lattice point is one of the six vectors `a ρ^j` (norm `a`, the *nearest neighbours*)
  or has `‖z‖² ≥ 3 a²` (there is no shell of norm `√2 a`).
-/

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm

theorem rho_pow_four : rho ^ 4 = -rho := by
  linear_combination rho * rho_cube

theorem rho_pow_five : rho ^ 5 = 1 - rho := by
  linear_combination rho ^ 2 * rho_cube - rho_sq

theorem rho_pow_six_mul (j : ℕ) : (rho ^ j) ^ 6 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, rho_pow_six, one_pow]

theorem norm_rho_pow (j : ℕ) : ‖rho ^ j‖ = 1 := by
  rw [norm_pow, norm_rho, one_pow]

theorem mem_triangularLattice_iff {z : ℂ} :
    z ∈ triangularLattice ↔ ∃ m n : ℤ, z = (a : ℂ) * ((m : ℂ) * rho + n) := by
  rw [← triPair_lattice, PeriodPair.mem_lattice, triPair_ω₁, triPair_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨n, m, by ring⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨n, m, by ring⟩

/-- `Λ_△` is invariant under the rotation by `π/3`. -/
theorem rho_mul_mem_tri {z : ℂ} (hz : z ∈ triangularLattice) : rho * z ∈ triangularLattice := by
  obtain ⟨m, n, rfl⟩ := mem_triangularLattice_iff.1 hz
  refine mem_triangularLattice_iff.2 ⟨m + n, -m, ?_⟩
  push_cast
  linear_combination ((a : ℂ) * (m : ℂ)) * rho_sq

theorem rho_pow_mul_mem_tri {z : ℂ} (hz : z ∈ triangularLattice) (j : ℕ) :
    rho ^ j * z ∈ triangularLattice := by
  induction j with
  | zero => simpa using hz
  | succ j ih =>
    have := rho_mul_mem_tri ih
    rwa [← mul_assoc, ← pow_succ'] at this

theorem norm_sq_hex (m n : ℤ) : ‖(m : ℂ) * rho + n‖ ^ 2 = (m : ℝ) ^ 2 + m * n + n ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im, rho_re, rho_im]
  have : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination ((m : ℝ) ^ 2 / 4) * this

theorem hex_int_cases (m n : ℤ) (h0 : ¬ (m = 0 ∧ n = 0)) (h : m ^ 2 + m * n + n ^ 2 ≤ 2) :
    (m = 0 ∧ n = 1) ∨ (m = 1 ∧ n = 0) ∨ (m = 1 ∧ n = -1) ∨ (m = 0 ∧ n = -1) ∨ (m = -1 ∧ n = 0) ∨
      (m = -1 ∧ n = 1) := by
  have hm1 : m ≤ 1 := by nlinarith [sq_nonneg (m + 2 * n), sq_nonneg n]
  have hm2 : -1 ≤ m := by nlinarith [sq_nonneg (m + 2 * n), sq_nonneg n]
  have hn1 : n ≤ 1 := by nlinarith [sq_nonneg (n + 2 * m), sq_nonneg m]
  have hn2 : -1 ≤ n := by nlinarith [sq_nonneg (n + 2 * m), sq_nonneg m]
  interval_cases m <;> interval_cases n <;> simp_all

/-- A nonzero point `m ρ + n` of the hexagonal lattice is a sixth root of unity or has `‖w‖² ≥ 3`. -/
theorem hex_shell (m n : ℤ) (h0 : ¬ (m = 0 ∧ n = 0)) :
    (∃ j : ℕ, j < 6 ∧ (m : ℂ) * rho + n = rho ^ j) ∨ 3 ≤ ‖(m : ℂ) * rho + n‖ ^ 2 := by
  by_cases h : m ^ 2 + m * n + n ^ 2 ≤ 2
  · left
    rcases hex_int_cases m n h0 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩
    · exact ⟨2, by norm_num, by rw [rho_sq]; push_cast; ring⟩
    · exact ⟨3, by norm_num, by rw [rho_cube]; push_cast; ring⟩
    · exact ⟨4, by norm_num, by rw [rho_pow_four]; push_cast; ring⟩
    · exact ⟨5, by norm_num, by rw [rho_pow_five]; push_cast; ring⟩
  · right
    rw [norm_sq_hex]
    push Not at h
    have : (3 : ℤ) ≤ m ^ 2 + m * n + n ^ 2 := by omega
    exact_mod_cast this

/-- **Shells of `Λ_△`.** A nonzero lattice point is one of the six nearest neighbours `a ρ^j` or has
`‖z‖² ≥ 3 a²`. -/
theorem tri_shell {z : ℂ} (hz : z ∈ triangularLattice) (h0 : z ≠ 0) :
    (∃ j : ℕ, j < 6 ∧ z = (a : ℂ) * rho ^ j) ∨ 3 * a ^ 2 ≤ ‖z‖ ^ 2 := by
  obtain ⟨m, n, rfl⟩ := mem_triangularLattice_iff.1 hz
  have hmn : ¬ (m = 0 ∧ n = 0) := by
    rintro ⟨rfl, rfl⟩; apply h0; simp
  rcases hex_shell m n hmn with ⟨j, hj, he⟩ | h
  · exact Or.inl ⟨j, hj, by rw [he]⟩
  · right
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg a_pos.le, mul_pow]
    nlinarith [sq_nonneg a]

/-- The nonzero points of `Λ_△` have norm at least `a`. -/
theorem a_le_norm_of_mem_tri {z : ℂ} (hz : z ∈ triangularLattice) (h0 : z ≠ 0) : a ≤ ‖z‖ := by
  rcases tri_shell hz h0 with ⟨j, -, rfl⟩ | h
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg a_pos.le, norm_rho_pow, mul_one]
  · have : a ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg a]
    exact (sq_le_sq₀ a_pos.le (norm_nonneg _)).1 this

end Calibration

end SandierSerfaty

end
