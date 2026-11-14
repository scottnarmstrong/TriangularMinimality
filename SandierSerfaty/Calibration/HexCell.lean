/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.HexLattice
public import SandierSerfaty.Geometry.VoronoiPeriodic
public import SandierSerfaty.Geometry.VoronoiFacet

/-!
# The Voronoi cell of `Λ_△` is the regular hexagon

Paper proof of `cal:energy-identity`. Let `triSites = periodicSites Λ_△ (fun _ : Fin 1 => 0)` (the lattice `Λ_△`, as a set of sites).

* `InHex x`: the six half-plane conditions `⟨x, ρ^j⟩ ≤ p` (`p = a/2` the apothem), in coordinates;
* `mem_cell_iff`: `x ∈ voronoiCell triSites 0 ↔ InHex x` (the cell is the regular hexagon of apothem `p`);
* `norm_sq_le_of_inHex`: `‖x‖² ≤ 4 p²/3 = R₀²` on the hexagon (circumradius `R₀`);
* `facetOrdinates_triSites`: for `q = a ρ^j`, the facet ordinates are `[-x₀, x₀]` (`x₀ = p tan(π/6)`);
* `isVoronoiNeighbor_triSites`: the Voronoi neighbours of `0` are among the six vectors `a ρ^j`;
* `pairHalfDist_eq`, `sectorAlpha_eq`, `sectorBeta_eq`: for each, `d = p`, `α = β = π/6`.
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm

/-- The sites `Λ_△` (one charge at the origin on the triangular torus). -/
@[expose] noncomputable def triSites : Set ℂ :=
  periodicSites triangularLattice (fun _ : Fin 1 => (0 : ℂ))

theorem mem_triSites_iff {x : ℂ} : x ∈ triSites ↔ x ∈ triangularLattice := by
  rw [triSites, mem_periodicSites_iff]
  simp

theorem a_mem_tri : (a : ℂ) ∈ triangularLattice :=
  mem_triangularLattice_iff.2 ⟨0, 1, by simp⟩

theorem a_mul_rho_pow_mem_tri (j : ℕ) : (a : ℂ) * rho ^ j ∈ triangularLattice := by
  have := rho_pow_mul_mem_tri a_mem_tri j
  rwa [mul_comm] at this

theorem norm_a_mul_rho_pow (j : ℕ) : ‖(a : ℂ) * rho ^ j‖ = a := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg a_pos.le, norm_rho_pow, mul_one]

theorem sqrt_three_mul_self : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem rho_pow_re_im :
    (rho ^ 0).re = 1 ∧ (rho ^ 0).im = 0 ∧ (rho ^ 1).re = 1 / 2 ∧ (rho ^ 1).im = √3 / 2 ∧
      (rho ^ 2).re = -1 / 2 ∧ (rho ^ 2).im = √3 / 2 ∧ (rho ^ 3).re = -1 ∧ (rho ^ 3).im = 0 ∧
      (rho ^ 4).re = -1 / 2 ∧ (rho ^ 4).im = -(√3 / 2) ∧ (rho ^ 5).re = 1 / 2 ∧
      (rho ^ 5).im = -(√3 / 2) := by
  refine ⟨by simp, by simp, by simp [rho_re], by simp [rho_im], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rho_sq]; simp [rho_re]; norm_num
  · rw [rho_sq]; simp [rho_im]
  · rw [rho_cube]; simp
  · rw [rho_cube]; simp
  · rw [rho_pow_four]; simp [rho_re]; norm_num
  · rw [rho_pow_four]; simp [rho_im]
  · rw [rho_pow_five]; simp [rho_re]; norm_num
  · rw [rho_pow_five]; simp [rho_im]

/-- The regular hexagon of apothem `p`: the six half-planes `⟨x, ρ^j⟩ ≤ p`. -/
@[expose] def InHex (x : ℂ) : Prop :=
  x.re ≤ p ∧ -x.re ≤ p ∧ x.re + √3 * x.im ≤ 2 * p ∧ -x.re + √3 * x.im ≤ 2 * p ∧
    -x.re - √3 * x.im ≤ 2 * p ∧ x.re - √3 * x.im ≤ 2 * p

theorem norm_le_norm_sub_iff (x γ : ℂ) :
    ‖x‖ ≤ ‖x - γ‖ ↔ 2 * (x.re * γ.re + x.im * γ.im) ≤ ‖γ‖ ^ 2 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  have hγ : ‖γ‖ ^ 2 = γ.re * γ.re + γ.im * γ.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hγ]
  constructor <;> intro h <;> linarith

theorem inner_le_of_mem_cell {x : ℂ} (hx : x ∈ voronoiCell triSites 0) (j : ℕ) :
    x.re * (rho ^ j).re + x.im * (rho ^ j).im ≤ p := by
  have h := hx _ (mem_triSites_iff.2 (a_mul_rho_pow_mem_tri j))
  rw [sub_zero, norm_le_norm_sub_iff, norm_a_mul_rho_pow, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul] at h
  have hp : p = a / 2 := rfl
  have ha := a_pos
  rw [hp]
  by_contra hlt
  push Not at hlt
  linarith [mul_lt_mul_of_pos_left hlt ha]

theorem inHex_of_mem_cell {x : ℂ} (hx : x ∈ voronoiCell triSites 0) : InHex x := by
  obtain ⟨e00, e01, e10, e11, e20, e21, e30, e31, e40, e41, e50, e51⟩ := rho_pow_re_im
  have h0 := inner_le_of_mem_cell hx 0
  have h1 := inner_le_of_mem_cell hx 1
  have h2 := inner_le_of_mem_cell hx 2
  have h3 := inner_le_of_mem_cell hx 3
  have h4 := inner_le_of_mem_cell hx 4
  have h5 := inner_le_of_mem_cell hx 5
  rw [e00, e01] at h0
  rw [e10, e11] at h1
  rw [e20, e21] at h2
  rw [e30, e31] at h3
  rw [e40, e41] at h4
  rw [e50, e51] at h5
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sq_add_sq_le_aux {X Y : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (h0 : X ≤ p)
    (h1 : X + √3 * Y ≤ 2 * p) : X ^ 2 + Y ^ 2 ≤ 4 * p ^ 2 / 3 := by
  have hs := sqrt_three_mul_self
  have hs0 : 0 ≤ √3 := Real.sqrt_nonneg 3
  have hsY : 0 ≤ √3 * Y := mul_nonneg hs0 hY0
  have h2 : 3 * Y ^ 2 ≤ (2 * p - X) ^ 2 := by
    have : (√3 * Y) ^ 2 ≤ (2 * p - X) ^ 2 := by
      apply pow_le_pow_left₀ hsY; linarith
    have e : (√3 * Y) ^ 2 = 3 * Y ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
    linarith
  linarith [mul_nonneg hX0 (sub_nonneg.2 h0)]

/-- On the hexagon `‖x‖² ≤ R₀² = 4 p²/3`. -/
theorem norm_sq_le_of_inHex {x : ℂ} (h : InHex x) : ‖x‖ ^ 2 ≤ 4 * p ^ 2 / 3 := by
  obtain ⟨h0, h3, h1, h2, h4, h5⟩ := h
  rw [Complex.sq_norm, Complex.normSq_apply]
  have key : x.re ^ 2 + x.im ^ 2 ≤ 4 * p ^ 2 / 3 := by
    rcases le_total 0 x.re with hX | hX <;> rcases le_total 0 x.im with hY | hY
    · exact sq_add_sq_le_aux hX hY h0 h1
    · have := sq_add_sq_le_aux (X := x.re) (Y := -x.im) hX (by linarith) h0 (by linarith)
      linarith [this]
    · have := sq_add_sq_le_aux (X := -x.re) (Y := x.im) (by linarith) hY h3 (by linarith)
      linarith [this]
    · have := sq_add_sq_le_aux (X := -x.re) (Y := -x.im) (by linarith) (by linarith) h3 (by linarith)
      linarith [this]
  linarith [key]

theorem a_eq_two_mul_p : a = 2 * p := by unfold p; ring

theorem mem_cell_of_inHex {x : ℂ} (h : InHex x) : x ∈ voronoiCell triSites 0 := by
  intro γ hγ
  rw [sub_zero]
  have hγ' := mem_triSites_iff.1 hγ
  have hxn := norm_sq_le_of_inHex h
  have hp := p_pos
  have ha := a_eq_two_mul_p
  by_cases h0 : γ = 0
  · simp [h0]
  rcases tri_shell hγ' h0 with ⟨j, hj, rfl⟩ | hbig
  · rw [norm_le_norm_sub_iff, norm_a_mul_rho_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    obtain ⟨e00, e01, e10, e11, e20, e21, e30, e31, e40, e41, e50, e51⟩ := rho_pow_re_im
    obtain ⟨h0, h3, h1, h2, h4, h5⟩ := h
    have haa : 0 < a := a_pos
    have key : x.re * (rho ^ j).re + x.im * (rho ^ j).im ≤ p := by
      interval_cases j
      · rw [e00, e01]; linarith
      · rw [e10, e11]; linarith
      · rw [e20, e21]; linarith
      · rw [e30, e31]; linarith
      · rw [e40, e41]; linarith
      · rw [e50, e51]; linarith
    have k2 : a * (x.re * (rho ^ j).re + x.im * (rho ^ j).im) ≤ a * (a / 2) :=
      mul_le_mul_of_nonneg_left (key.trans_eq rfl) haa.le
    linarith
  · -- far lattice points: `‖γ‖ ≥ 2 ‖x‖`
    have h2 : 2 * ‖x‖ ≤ ‖γ‖ := by
      have h4 : (2 * ‖x‖) ^ 2 ≤ ‖γ‖ ^ 2 := by nlinarith
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h4
    have h5 : ‖γ‖ ≤ ‖x - γ‖ + ‖x‖ := by
      calc ‖γ‖ = ‖x - (x - γ)‖ := by congr 1; ring
        _ ≤ ‖x‖ + ‖x - γ‖ := norm_sub_le _ _
        _ = ‖x - γ‖ + ‖x‖ := add_comm _ _
    linarith

/-- **The Voronoi cell of `Λ_△` at `0` is the regular hexagon of apothem `p`**. -/
theorem mem_cell_iff {x : ℂ} : x ∈ voronoiCell triSites 0 ↔ InHex x :=
  ⟨inHex_of_mem_cell, mem_cell_of_inHex⟩

/-- The circumscribed disc: the cell lies in the closed disc of radius `R₀`. -/
theorem norm_sq_le_of_mem_cell {x : ℂ} (hx : x ∈ voronoiCell triSites 0) :
    ‖x‖ ^ 2 ≤ 4 * p ^ 2 / 3 :=
  norm_sq_le_of_inHex (inHex_of_mem_cell hx)

end Calibration

end SandierSerfaty

end
