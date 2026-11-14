/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectInvariance
public import SandierSerfaty.Statements.Torus.Theorems.TendstoTorusEnergy
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec

/-!
# The torus energy of the reflected configuration is four times the quadrant energy (Lemma 6.2(iii))

For `Z : Fin n̄ → ℂ` injective with `Z i ∈ b + (0, √n̄)²` and `h = torusPotential (squareLattice (4 n̄))
(reflectPts b Z)`:

* `Lower.integral_torusDomain_eq_four`: for a nonnegative measurable function periodic under the lattice
  and invariant under `reflX b.re`, `reflY b.im`, `∫_{torusDomain} F = 4 ∫_{b + (0, √n̄)²} F`;
* `Lower.tendsto_punctureTrunc_reflected`: the truncated puncture energies of `h` on the open square
  `b + (0, √n̄)²` with punctures `Z` converge to `torusEnergy / 4`.
-/

open MeasureTheory Filter Topology Set

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

open Torus

section Integral

theorem integral_torusDomain_eq_four {nb : ℕ} (hnb : 1 ≤ nb) (b : ℂ) {F : ℂ → ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hFm : Measurable F)
    (hper : ∀ γ ∈ squareLattice (4 * nb), ∀ x, F (x + γ) = F x)
    (hX : ∀ x, F (reflX b.re x) = F x) (hY : ∀ x, F (reflY b.im x) = F x) :
    ∫ x in torusDomain (squareLattice (4 * nb)), F x = 4 * ∫ x in openSq b (√nb), F x := by
  have : NeZero (4 * nb) := ⟨by omega⟩
  have hs : 0 < √(nb : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnb)
  have hfd := isAddFundamentalDomain_box (n := 4 * nb) (by omega) (b - ⟨√nb, √nb⟩)
  rw [(torusDomain_spec _).2 _ hfd F hper, sqrt_four_mul]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFm.aestronglyMeasurable,
    lintegral_box_eq_four b (√nb) hs (G := fun x => ENNReal.ofReal (F x)) (by simp [hX])
      (by simp [hY]), ENNReal.toReal_mul]
  simp

end Integral

section Coordinates

theorem coord_aux {s u x δ σ : ℝ} {p : ℤ} (hσ : σ = 1 ∨ σ = -1) (hδ : 0 < δ) (hu₁ : δ ≤ u)
    (hu₂ : u ≤ s - δ) (hx₁ : 0 < x) (hx₂ : x < s) (hd : |x - (σ * u + 2 * s * p)| < δ) :
    σ = 1 ∧ p = 0 := by
  have hs : 0 < s := by linarith
  rw [abs_lt] at hd
  rcases hσ with rfl | rfl
  · refine ⟨rfl, ?_⟩
    have h1 : p ≤ 0 := by
      by_contra hp
      push Not at hp
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    have h2 : 0 ≤ p := by
      by_contra hp
      push Not at hp
      have : (p : ℝ) ≤ -1 := by
        have : p ≤ -1 := by omega
        exact_mod_cast this
      nlinarith
    omega
  · exfalso
    have h1 : 1 ≤ p := by
      by_contra hp
      push Not at hp
      have : (p : ℝ) ≤ 0 := by
        have : p ≤ 0 := by omega
        exact_mod_cast this
      nlinarith
    have : (1 : ℝ) ≤ p := by exact_mod_cast h1
    nlinarith

/-- A point of the open quadrant lying in an `η`-ball about a reflected charge (`η ≤ δ`, with `δ` smaller than
the distances of the charges to the sides of the quadrant) lies in an `η`-ball about an original charge. -/
theorem exists_ball_of_mem_ballUnion {nb : ℕ} (_hnb : 1 ≤ nb) (b : ℂ) (Z : Fin nb → ℂ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : η ≤ δ)
    (hZδ : ∀ i, δ ≤ (Z i - b).re ∧ (Z i - b).re ≤ √nb - δ ∧ δ ≤ (Z i - b).im ∧
      (Z i - b).im ≤ √nb - δ)
    {x : ℂ} (hx : x ∈ openSq b (√nb))
    (hxb : x ∈ ballUnion (squareLattice (4 * nb)) (reflectPts b Z) η) :
    ∃ i, ‖x - Z i‖ < η := by
  rw [mem_ballUnion] at hxb
  obtain ⟨k, γ, hγ, hlt⟩ := hxb
  obtain ⟨e, i, hk⟩ := exists_reflectPts_eq b Z k
  rw [hk] at hlt
  obtain ⟨p, q, rfl⟩ := mem_squareLattice_iff.1 hγ
  rw [sqrt_four_mul] at hlt
  have hlt' : ‖x - (reflect4 b (Z i) e + ⟨p * (2 * √nb), q * (2 * √nb)⟩)‖ < δ := hlt.trans_le hη
  have hre : |(x - (reflect4 b (Z i) e + ⟨p * (2 * √nb), q * (2 * √nb)⟩)).re| < δ :=
    (Complex.abs_re_le_norm _).trans_lt hlt'
  have him : |(x - (reflect4 b (Z i) e + ⟨p * (2 * √nb), q * (2 * √nb)⟩)).im| < δ :=
    (Complex.abs_im_le_norm _).trans_lt hlt'
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, reflect4_re,
    reflect4_im] at hre him
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := hZδ i
  simp only [Complex.sub_re, Complex.sub_im] at hZ1 hZ2 hZ3 hZ4
  simp only [openSq, mem_ofPred_eq] at hx
  have hsr : sgnRe e = 1 ∨ sgnRe e = -1 := by fin_cases e <;> simp [sgnRe]
  have hsi : sgnIm e = 1 ∨ sgnIm e = -1 := by fin_cases e <;> simp [sgnIm]
  have h1 := coord_aux (s := √nb) (u := (Z i).re - b.re) (x := x.re - b.re) (δ := δ)
    (σ := sgnRe e) (p := p) hsr hδ hZ1 hZ2 (by linarith [hx.1]) (by linarith [hx.2.1])
    (by convert hre using 2; ring)
  have h2 := coord_aux (s := √nb) (u := (Z i).im - b.im) (x := x.im - b.im) (δ := δ)
    (σ := sgnIm e) (p := q) hsi hδ hZ3 hZ4 (by linarith [hx.2.2.1]) (by linarith [hx.2.2.2])
    (by convert him using 2; ring)
  have he : e = 0 := by
    obtain ⟨hr, rfl⟩ := h1
    obtain ⟨hi, rfl⟩ := h2
    fin_cases e
    · rfl
    · exfalso; norm_num [sgnRe] at hr
    · exfalso; norm_num [sgnIm] at hi
    · exfalso; norm_num [sgnRe] at hr
  subst he
  refine ⟨i, ?_⟩
  obtain ⟨-, rfl⟩ := h1
  obtain ⟨-, rfl⟩ := h2
  have z : (⟨0, 0⟩ : ℂ) = 0 := Complex.ext (by simp) (by simp)
  simpa [reflect4_zero, z] using hlt

end Coordinates

section Energy

variable {nb : ℕ}

theorem interior_sqAt (a₀ : ℂ) (t : ℝ) : interior (sqAt a₀ t) = openSq a₀ t := by
  have h1 : sqAt a₀ t = (Complex.re ⁻¹' Icc a₀.re (a₀.re + t)) ∩
      (Complex.im ⁻¹' Icc a₀.im (a₀.im + t)) := by
    ext x; simp [sqAt, and_assoc]
  rw [h1, interior_inter, Complex.interior_preimage_re, Complex.interior_preimage_im]
  ext x
  simp [openSq, and_assoc]

end Energy

end Lower

end Sphere

end SandierSerfaty

end
