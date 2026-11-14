/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GridStrips

/-!
# Fubini choice of the grid, real form (sphere note, Lemma 6.12)

`Lower.exists_good_offset`: for an integrable `G ≥ 0` on `ℂ` there is an offset `θ ∈ [0,R]²` such that for every finite
family `J` of grid cells and each of two bands `[aᵢ, bᵢ]`,
`R · ∑_{j ∈ J} ∫_{stripSq R θ aᵢ bᵢ j} G ≤ 12 (bᵢ - aᵢ) ∫ G`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem exists_good_offset {R a₁ b₁ a₂ b₂ : ℝ} (hR : 0 < R) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) {G : ℂ → ℝ}
    (hG : Integrable G) (hGm : Measurable G) (hG0 : ∀ z, 0 ≤ G z) :
    ∃ θ ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R, ∀ J : Finset (ℤ × ℤ),
      (∑ j ∈ J, ∫ z in stripSq R θ a₁ b₁ j, G z) * R ≤ 12 * (b₁ - a₁) * ∫ z, G z ∧
      (∑ j ∈ J, ∫ z in stripSq R θ a₂ b₂ j, G z) * R ≤ 12 * (b₂ - a₂) * ∫ z, G z := by
  have hint0 : 0 ≤ ∫ z, G z := integral_nonneg hG0
  have hmeas : Measurable fun z => ENNReal.ofReal (G z) := ENNReal.measurable_ofReal.comp hGm
  have hcongr : ∫⁻ z, ENNReal.ofReal (G z) = ENNReal.ofReal (∫ z, G z) :=
    (ofReal_integral_eq_lintegral_ofReal hG (Eventually.of_forall hG0)).symm
  have hfin : ∫⁻ z, ENNReal.ofReal (G z) ≠ ⊤ := by rw [hcongr]; exact ENNReal.ofReal_ne_top
  obtain ⟨θ, hθ, e1, e2⟩ := exists_offset_two_bands hR h₁ h₂ hmeas hfin
  have key : ∀ (a b : ℝ), (∫⁻ z in gridBand R θ a b, ENNReal.ofReal (G z)) * ENNReal.ofReal (R * R) ≤
      3 * (ENNReal.ofReal (4 * (b - a) * R) * ∫⁻ z, ENNReal.ofReal (G z)) → a ≤ b →
      ∀ J : Finset (ℤ × ℤ), (∑ j ∈ J, ∫ z in stripSq R θ a b j, G z) * R ≤ 12 * (b - a) * ∫ z, G z := by
    intro a b hk hab J
    have hGi : ∀ s : Set ℂ, ∫⁻ z in s, ENNReal.ofReal (G z) = ENNReal.ofReal (∫ z in s, G z) := fun s =>
      (ofReal_integral_eq_lintegral_ofReal hG.integrableOn (Eventually.of_forall hG0)).symm
    have hband : 0 ≤ ∫ z in gridBand R θ a b, G z := setIntegral_nonneg_of_ae_restrict
      (Eventually.of_forall hG0)
    have hstrip : ∀ j, 0 ≤ ∫ z in stripSq R θ a b j, G z := fun j =>
      setIntegral_nonneg_of_ae_restrict (Eventually.of_forall hG0)
    have h1 : ENNReal.ofReal (∑ j ∈ J, ∫ z in stripSq R θ a b j, G z) ≤
        ENNReal.ofReal (∫ z in gridBand R θ a b, G z) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hstrip j), ← hGi]
      simp only [← hGi]
      exact sum_lintegral_strip_le hR θ a b J _
    have h2 := hk
    rw [hGi, hcongr] at h2
    have hb0 : 0 ≤ b - a := by linarith
    have e3 : ENNReal.ofReal ((∫ z in gridBand R θ a b, G z) * (R * R)) =
        ENNReal.ofReal (∫ z in gridBand R θ a b, G z) * ENNReal.ofReal (R * R) := ENNReal.ofReal_mul hband
    have e4 : ENNReal.ofReal (3 * (4 * (b - a) * R * ∫ z, G z)) =
        3 * (ENNReal.ofReal (4 * (b - a) * R) * ENNReal.ofReal (∫ z, G z)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
    rw [← e3, ← e4] at h2
    have h2' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
    have h3 := (ENNReal.ofReal_le_ofReal_iff hband).1 h1
    have hsum0 : 0 ≤ ∑ j ∈ J, ∫ z in stripSq R θ a b j, G z := Finset.sum_nonneg fun j _ => hstrip j
    have hRR : 0 < R * R := mul_pos hR hR
    have h4 : (∫ z in gridBand R θ a b, G z) * R ≤ 12 * (b - a) * ∫ z, G z := by
      have h5 : (∫ z in gridBand R θ a b, G z) * R * R ≤ 12 * (b - a) * (∫ z, G z) * R := by nlinarith [h2']
      exact le_of_mul_le_mul_right h5 hR
    calc (∑ j ∈ J, ∫ z in stripSq R θ a b j, G z) * R ≤ (∫ z in gridBand R θ a b, G z) * R := by gcongr
      _ ≤ _ := h4
  exact ⟨θ, hθ, fun J => ⟨key _ _ e1 h₁ J, key _ _ e2 h₂ J⟩⟩

end Lower

end Sphere

end SandierSerfaty

end
