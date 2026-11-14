/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.InversionChange

/-!
# Images of discs under the inversion `ι(x) = 1 / x̄`

For `0 < η < ‖p‖` the inversion maps the disc `B(p, η)` onto the disc with center
`c = (‖p‖² - η²)⁻¹ p` and radius `ρ = η / (‖p‖² - η²)` (`Sphere.invC_mem_ball_iff`):
for `z ≠ 0`,
`‖ι z - c‖² - ρ² = (‖z - p‖² - η²) / (‖z‖² (‖p‖² - η²))`.
The center differs from `ι p` by `δ = η² / (‖p‖ (‖p‖² - η²))`, so
`B(ι p, η / (‖p‖ (‖p‖ + η))) ⊆ ι(B(p, η)) ⊆ B(ι p, η / (‖p‖ (‖p‖ - η)))`
(`Sphere.ball_sandwich`). These are the only Taylor-type estimates needed for the inversion
case of the sphere note's Lemma 3.5.
-/

open MeasureTheory Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Sphere

theorem invC_eq_smul (z : ℂ) : invC z = ((‖z‖ ^ 2)⁻¹ : ℝ) • z := by
  rw [invC, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq,
    Complex.real_smul, mul_comm]

/-- The center of the image disc. -/
@[expose] noncomputable def invCenter (p : ℂ) (η : ℝ) : ℂ := ((‖p‖ ^ 2 - η ^ 2)⁻¹ : ℝ) • p

/-- The radius of the image disc. -/
@[expose] noncomputable def invRad (p : ℂ) (η : ℝ) : ℝ := η / (‖p‖ ^ 2 - η ^ 2)

theorem norm_sq_invC_sub (z p : ℂ) (hz : z ≠ 0) (η : ℝ) (hD : ‖p‖ ^ 2 - η ^ 2 ≠ 0) :
    ‖invC z - invCenter p η‖ ^ 2 - invRad p η ^ 2 =
      (‖z - p‖ ^ 2 - η ^ 2) / (‖z‖ ^ 2 * (‖p‖ ^ 2 - η ^ 2)) := by
  have hN : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  rw [invC_eq_smul, invCenter, invRad, norm_sub_sq_real, norm_sub_sq_real (x := z) (y := p),
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem invRad_pos {p : ℂ} {η : ℝ} (hη : 0 < η) (hηp : η < ‖p‖) : 0 < invRad p η := by
  unfold invRad
  have : 0 < ‖p‖ ^ 2 - η ^ 2 := by nlinarith
  positivity

/-- **Image of a disc under the inversion.** -/
theorem invC_mem_ball_iff {z p : ℂ} {η : ℝ} (hη : 0 < η) (hηp : η < ‖p‖) (hz : z ≠ 0) :
    invC z ∈ ball (invCenter p η) (invRad p η) ↔ z ∈ ball p η := by
  have hD : 0 < ‖p‖ ^ 2 - η ^ 2 := by nlinarith
  have hρ := invRad_pos hη hηp
  have hN : 0 < ‖z‖ ^ 2 := by have := norm_pos_iff.2 hz; positivity
  have key := norm_sq_invC_sub z p hz η hD.ne'
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm]
  have h1 : ‖invC z - invCenter p η‖ < invRad p η ↔ ‖invC z - invCenter p η‖ ^ 2 - invRad p η ^ 2 < 0 := by
    rw [sub_neg]
    exact (sq_lt_sq₀ (norm_nonneg _) hρ.le).symm
  have h2 : ‖z - p‖ < η ↔ ‖z - p‖ ^ 2 - η ^ 2 < 0 := by
    rw [sub_neg]
    exact (sq_lt_sq₀ (norm_nonneg _) hη.le).symm
  rw [h1, h2, key, div_neg_iff]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact absurd h' (not_lt.2 (by positivity))
    · exact h
  · intro h
    exact Or.inr ⟨h, by positivity⟩

theorem norm_invCenter_sub_invC {p : ℂ} {η : ℝ} (hp : p ≠ 0) (hη : 0 < η) (hηp : η < ‖p‖) :
    ‖invCenter p η - invC p‖ = η ^ 2 / (‖p‖ * (‖p‖ ^ 2 - η ^ 2)) := by
  have hP : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hD : 0 < ‖p‖ ^ 2 - η ^ 2 := by nlinarith
  have e : invCenter p η - invC p =
      ((η ^ 2 / (‖p‖ ^ 2 * (‖p‖ ^ 2 - η ^ 2)) : ℝ)) • p := by
    rw [invC_eq_smul, invCenter, ← sub_smul]
    congr 1
    field_simp
    ring
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

/-- The sandwich `B(ι p, ρ⁻) ⊆ B(c, ρ₀) ⊆ B(ι p, ρ⁺)` with `ρ^± = η / (‖p‖ (‖p‖ ∓ η))`. -/
theorem ball_sandwich {p : ℂ} {η : ℝ} (hp : p ≠ 0) (hη : 0 < η) (hηp : η < ‖p‖) :
    ball (invC p) (η / (‖p‖ * (‖p‖ + η))) ⊆ ball (invCenter p η) (invRad p η) ∧
      ball (invCenter p η) (invRad p η) ⊆ ball (invC p) (η / (‖p‖ * (‖p‖ - η))) := by
  have hP : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hD : 0 < ‖p‖ ^ 2 - η ^ 2 := by nlinarith
  have hδ := norm_invCenter_sub_invC hp hη hηp
  have hm : 0 < ‖p‖ - η := by linarith
  have hsum : η / (‖p‖ * (‖p‖ + η)) + η ^ 2 / (‖p‖ * (‖p‖ ^ 2 - η ^ 2)) = invRad p η := by
    unfold invRad
    have : ‖p‖ ^ 2 - η ^ 2 = (‖p‖ - η) * (‖p‖ + η) := by ring
    rw [this]
    field_simp
    ring
  have hsum' : invRad p η + η ^ 2 / (‖p‖ * (‖p‖ ^ 2 - η ^ 2)) = η / (‖p‖ * (‖p‖ - η)) := by
    unfold invRad
    have : ‖p‖ ^ 2 - η ^ 2 = (‖p‖ - η) * (‖p‖ + η) := by ring
    rw [this]
    field_simp
  constructor
  · intro x hx
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have := norm_sub_le_norm_sub_add_norm_sub x (invC p) (invCenter p η)
    rw [norm_sub_rev (invC p) (invCenter p η)] at this
    linarith
  · intro x hx
    rw [mem_ball, dist_eq_norm] at hx ⊢
    have := norm_sub_le_norm_sub_add_norm_sub x (invCenter p η) (invC p)
    linarith

end Sphere

end SandierSerfaty

end
