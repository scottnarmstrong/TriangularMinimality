/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiSectorTotals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals over sectors in polar coordinates

* `integral_comp_affine_image`: the integral over the image of a set under `ζ ↦ c + u ζ`
  (`‖u‖ = 1`) is the integral over the set of the composed integrand;
* `integral_inv_sq_arg_annulus`: `∫_{a < arg x < b, η' < ‖x‖ ≤ η} ‖x‖⁻² = (b - a) log (η/η')`
  (for `-π ≤ a ≤ b ≤ π`), the radial integral behind the renormalization of the sector integral
  `(dual:sector-ren)` (paper `dual:sector-ren`).
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty

theorem measurePreserving_mul_add {u : ℂ} (hu : ‖u‖ = 1) (c : ℂ) :
    MeasurePreserving (fun z : ℂ => c + u * z) volume volume := by
  obtain ⟨a, rfl⟩ : ∃ a : Circle, (a : ℂ) = u := ⟨⟨u, mem_sphere_zero_iff_norm.2 hu⟩, rfl⟩
  have h1 : MeasurePreserving (rotation a) volume volume := (rotation a).measurePreserving
  have h2 : MeasurePreserving (fun z : ℂ => c + z) volume volume :=
    measurePreserving_add_left volume c
  exact h2.comp h1

theorem measurableEmbedding_mul_add {u : ℂ} (hu : u ≠ 0) (c : ℂ) :
    MeasurableEmbedding (fun z : ℂ => c + u * z) :=
  ((Homeomorph.mulLeft₀ u hu).trans (Homeomorph.addLeft c)).measurableEmbedding

theorem integral_comp_affine_image {u : ℂ} (hu : ‖u‖ = 1) (c : ℂ) (S : Set ℂ) (F : ℂ → ℝ) :
    ∫ z in (fun ζ => c + u * ζ) '' S, F z = ∫ ζ in S, F (c + u * ζ) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  exact (measurePreserving_mul_add hu c).setIntegral_image_emb (measurableEmbedding_mul_add hu0 c) F S

/-- **The radial integral over an angular sector annulus.** -/
theorem integral_inv_sq_arg_annulus {a b η' η : ℝ} (hab : a ≤ b) (ha : -π ≤ a) (hb : b ≤ π)
    (h0 : 0 < η') (h1 : η' ≤ η) :
    ∫ x in {x : ℂ | x ≠ 0 ∧ a < Complex.arg x ∧ Complex.arg x < b ∧ η' < ‖x‖ ∧ ‖x‖ ≤ η},
      (‖x‖ ^ 2)⁻¹ = (b - a) * Real.log (η / η') := by
  set A : Set ℂ := {x : ℂ | x ≠ 0 ∧ a < Complex.arg x ∧ Complex.arg x < b ∧ η' < ‖x‖ ∧ ‖x‖ ≤ η}
    with hA
  have hAm : MeasurableSet A := by
    have : A = {x : ℂ | x ≠ 0} ∩ (Complex.arg ⁻¹' Ioo a b) ∩ (norm ⁻¹' Ioc η' η) := by
      ext x; simp [hA, and_assoc]
    rw [this]
    exact ((measurableSet_singleton 0).compl.inter (Complex.measurable_arg measurableSet_Ioo)).inter
      (measurable_norm measurableSet_Ioc)
  rw [← integral_indicator hAm, ← Complex.integral_comp_polarCoord_symm]
  have hcongr : ∀ z ∈ polarCoord.target,
      z.1 • A.indicator (fun x : ℂ => (‖x‖ ^ 2)⁻¹) (Complex.polarCoord.symm z) =
        (Ioc η' η ×ˢ Ioo a b).indicator (fun p : ℝ × ℝ => p.1⁻¹) z := by
    intro z hz
    rw [polarCoord_target] at hz
    have hr : 0 < z.1 := hz.1
    have hsymm : Complex.polarCoord.symm z =
        (z.1 : ℂ) * (Complex.cos z.2 + Complex.sin z.2 * Complex.I) := by
      rw [Complex.polarCoord_symm_apply]; push_cast; rfl
    have hn : ‖Complex.polarCoord.symm z‖ = z.1 := by
      rw [hsymm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_cos_add_sin_mul_I, mul_one]
    have harg : Complex.arg (Complex.polarCoord.symm z) = z.2 := by
      rw [hsymm]
      exact Complex.arg_mul_cos_add_sin_mul_I hr ⟨hz.2.1, hz.2.2.le⟩
    have hne : Complex.polarCoord.symm z ≠ 0 := by
      intro h; rw [h] at hn; simp at hn; linarith
    by_cases hmem : z ∈ Ioc η' η ×ˢ Ioo a b
    · have : Complex.polarCoord.symm z ∈ A :=
        ⟨hne, by rw [harg]; exact hmem.2.1, by rw [harg]; exact hmem.2.2, by rw [hn]; exact hmem.1.1,
          by rw [hn]; exact hmem.1.2⟩
      rw [indicator_of_mem this, indicator_of_mem hmem, hn]
      simp only [smul_eq_mul]
      field_simp
    · have : Complex.polarCoord.symm z ∉ A := by
        rintro ⟨-, h2, h3, h4, h5⟩
        rw [harg] at h2 h3
        rw [hn] at h4 h5
        exact hmem ⟨⟨h4, h5⟩, h2, h3⟩
      rw [indicator_of_notMem this, indicator_of_notMem hmem]
      simp
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr]
  rw [setIntegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  have hsub : polarCoord.target ∩ (Ioc η' η ×ˢ Ioo a b) = Ioc η' η ×ˢ Ioo a b := by
    rw [inter_eq_right]
    rw [polarCoord_target]
    refine prod_mono (fun r hr => lt_of_lt_of_le h0 hr.1.le) ?_
    intro θ hθ
    exact ⟨lt_of_le_of_lt ha hθ.1, lt_of_lt_of_le hθ.2 hb⟩
  rw [hsub]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  rw [hvol]
  have := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => r⁻¹) (fun _ : ℝ => (1 : ℝ)) (Ioc η' η) (Ioo a b)
  simp only [mul_one] at this
  rw [this]
  rw [← intervalIntegral.integral_of_le h1, integral_inv_of_pos h0 (lt_of_lt_of_le h0 h1)]
  rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul]
  ring

end SandierSerfaty

end
