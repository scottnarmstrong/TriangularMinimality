/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.HexCell

/-!
# The six sectors of the regular hexagon

Paper proof of `cal:energy-identity`: "Its regular Voronoi hexagon supplies six compatible sectors with `d = p` and
`α = β = π/6`." Here `triSites = periodicSites Λ_△ (fun _ : Fin 1 => 0)`.

* `mem_cell_rho_pow_mul_iff`: the cell is invariant under the rotations by `ρ^j`;
* `facetOrdinates_triSites`: the facet ordinates of `(0, a ρ^j)` are `[-x₀, x₀]`, `x₀ = p tan(π/6)`;
* `pairHalfDist_triSites`, `sectorAlpha_triSites`, `sectorBeta_triSites`: `d = p`, `α = β = π/6`;
* `exists_pow_of_isVoronoiNeighbor`: every Voronoi neighbour of `0` is one of the six `a ρ^j`
  (the next lattice shell lies outside the circumscribed disc of the cell).
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm

theorem rho_mul_mem_cell {x : ℂ} (hx : x ∈ voronoiCell triSites 0) :
    rho * x ∈ voronoiCell triSites 0 := by
  intro γ hγ
  have hγ' := mem_triSites_iff.1 hγ
  have hγ5 : rho ^ 5 * γ ∈ triangularLattice := rho_pow_mul_mem_tri hγ' 5
  have h := hx _ (mem_triSites_iff.2 hγ5)
  have e : rho * (rho ^ 5 * γ) = γ := by
    rw [← mul_assoc, ← pow_succ', rho_pow_six, one_mul]
  rw [sub_zero] at h ⊢
  have : rho * x - γ = rho * (x - rho ^ 5 * γ) := by rw [mul_sub, e]
  rw [this, norm_mul, norm_mul, norm_rho, one_mul, one_mul]
  exact h

theorem rho_pow_mul_mem_cell {x : ℂ} (hx : x ∈ voronoiCell triSites 0) (j : ℕ) :
    rho ^ j * x ∈ voronoiCell triSites 0 := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have := rho_mul_mem_cell ih
    rwa [← mul_assoc, ← pow_succ'] at this

theorem mem_cell_rho_pow_mul_iff (j : ℕ) {y : ℂ} :
    rho ^ j * y ∈ voronoiCell triSites 0 ↔ y ∈ voronoiCell triSites 0 := by
  refine ⟨fun h => ?_, fun h => rho_pow_mul_mem_cell h j⟩
  have := rho_pow_mul_mem_cell h (5 * j)
  have e : rho ^ (5 * j) * (rho ^ j * y) = y := by
    rw [← mul_assoc, ← pow_add, show 5 * j + j = 6 * j by ring, pow_mul, rho_pow_six, one_pow,
      one_mul]
  rwa [e] at this

theorem a_ne_zero_c : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'

theorem pairAxis_triSites (j : ℕ) : pairAxis 0 ((a : ℂ) * rho ^ j) = rho ^ j := by
  unfold pairAxis
  rw [sub_zero, norm_a_mul_rho_pow]
  exact mul_div_cancel_left₀ _ a_ne_zero_c

theorem pairHalfDist_triSites (j : ℕ) : pairHalfDist 0 ((a : ℂ) * rho ^ j) = p := by
  unfold pairHalfDist
  rw [sub_zero, norm_a_mul_rho_pow]
  rfl

theorem bisectorPoint_triSites (j : ℕ) (s : ℝ) :
    bisectorPoint 0 ((a : ℂ) * rho ^ j) s = rho ^ j * ((p : ℂ) + (s : ℂ) * Complex.I) := by
  unfold bisectorPoint
  rw [pairAxis_triSites, pairHalfDist_triSites, zero_add]

theorem x₀_mul_sqrt_three : x₀ * √3 = p := by
  unfold x₀ R₀
  have := sqrt_three_pos
  field_simp

theorem inHex_bisector (s : ℝ) :
    InHex ((p : ℂ) + (s : ℂ) * Complex.I) ↔ -x₀ ≤ s ∧ s ≤ x₀ := by
  have hp := p_pos
  have h3 := sqrt_three_pos
  have hx := x₀_mul_sqrt_three
  unfold InHex
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
    zero_add]
  constructor
  · rintro ⟨-, -, h1, -, -, h5⟩
    constructor
    · by_contra hlt
      push Not at hlt
      nlinarith
    · by_contra hlt
      push Not at hlt
      nlinarith
  · rintro ⟨h1, h2⟩
    have e1 : √3 * s ≤ p := by nlinarith
    have e2 : -p ≤ √3 * s := by nlinarith
    refine ⟨le_rfl, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **The facet ordinates of the six neighbours** are `[-x₀, x₀]`. -/
theorem facetOrdinates_triSites (j : ℕ) :
    facetOrdinates triSites 0 ((a : ℂ) * rho ^ j) = Icc (-x₀) x₀ := by
  ext s
  simp only [facetOrdinates, mem_ofPred_eq, bisectorPoint_triSites, mem_Icc]
  rw [mem_cell_rho_pow_mul_iff, mem_cell_iff, inHex_bisector]

theorem facetLo_triSites (j : ℕ) : facetLo triSites 0 ((a : ℂ) * rho ^ j) = -x₀ := by
  rw [facetLo, facetOrdinates_triSites]
  exact csInf_Icc (by linarith [x₀_pos])

theorem facetHi_triSites (j : ℕ) : facetHi triSites 0 ((a : ℂ) * rho ^ j) = x₀ := by
  rw [facetHi, facetOrdinates_triSites]
  exact csSup_Icc (by linarith [x₀_pos])

theorem x₀_div_p : x₀ / p = Real.tan (Real.pi / 6) := by
  rw [Real.tan_pi_div_six]
  have := p_pos
  have := sqrt_three_pos
  have hx := x₀_mul_sqrt_three
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linarith

theorem sectorAlpha_triSites (j : ℕ) : sectorAlpha triSites 0 ((a : ℂ) * rho ^ j) = Real.pi / 6 := by
  unfold sectorAlpha
  rw [facetLo_triSites, pairHalfDist_triSites, neg_neg, x₀_div_p,
    Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

theorem sectorBeta_triSites (j : ℕ) : sectorBeta triSites 0 ((a : ℂ) * rho ^ j) = Real.pi / 6 := by
  unfold sectorBeta
  rw [facetHi_triSites, pairHalfDist_triSites, x₀_div_p,
    Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

/-- Every Voronoi neighbour of `0` among the sites `Λ_△` is one of the six nearest neighbours `a ρ^j`. -/
theorem exists_pow_of_isVoronoiNeighbor {q : ℂ} (h : IsVoronoiNeighbor triSites 0 q) :
    ∃ j : ℕ, j < 6 ∧ q = (a : ℂ) * rho ^ j := by
  obtain ⟨-, hq, hne, hnt⟩ := h
  have hq' := mem_triSites_iff.1 hq
  rcases tri_shell hq' hne.symm with hj | hbig
  · exact hj
  · exfalso
    obtain ⟨s, hs⟩ := hnt.nonempty
    have hcell : bisectorPoint 0 q s ∈ voronoiCell triSites 0 := hs
    have hx := norm_sq_le_of_mem_cell hcell
    have heq := norm_bisectorPoint_sub_eq hne s
    rw [sub_zero] at heq
    have h1 : ‖q‖ ≤ 2 * ‖bisectorPoint 0 q s‖ := by
      calc ‖q‖ = ‖bisectorPoint 0 q s - (bisectorPoint 0 q s - q)‖ := by congr 1; ring
        _ ≤ ‖bisectorPoint 0 q s‖ + ‖bisectorPoint 0 q s - q‖ := norm_sub_le _ _
        _ = 2 * ‖bisectorPoint 0 q s‖ := by rw [← heq]; ring
    have h2 : ‖q‖ ^ 2 ≤ 4 * ‖bisectorPoint 0 q s‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      linarith
    have ha := a_eq_two_mul_p
    have hp := p_pos
    nlinarith

end Calibration

end SandierSerfaty

end
