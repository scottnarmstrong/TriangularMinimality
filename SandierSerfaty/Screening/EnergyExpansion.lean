/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Mollify

/-!
# Expanding the square of a locally perturbed field

`lintegral_norm_sq_perturb`: if `H = G + h` a.e., `h` is bounded and supported in a set `B ⊆ D` of
finite measure, `H = G` off `B`, `G` is integrable on `B` and `∫_D |G|² < ∞`, then (as real numbers)
`∫_D |G|² = r` and `∫_D |H|² = r + 2 ∫ ⟪G, h⟫ + ∫ |h|²`, all quantities finite. The field `G` is only
assumed square-integrable on `D` in the sense of the lower Lebesgue integral and integrable on `B`
(no measurability on `D \ B` is needed).
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal

public section

namespace SandierSerfaty

namespace Screening

theorem integrableOn_norm_sq_of_lintegral {G : ℂ → ℂ} {B D : Set ℂ} (hBD : B ⊆ D)
    (hG : AEStronglyMeasurable G (volume.restrict B))
    (hL2 : ∫⁻ x in D, ENNReal.ofReal (‖G x‖ ^ 2) ≠ ⊤) :
    IntegrableOn (fun x => ‖G x‖ ^ 2) B volume :=
  ⟨hG.norm.pow 2, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).2
    ((lintegral_mono_set hBD).trans_lt hL2.lt_top)⟩

/-- **Expansion of `∫_D |G + h|²`** for a bounded perturbation `h` supported in `B ⊆ D`. -/
theorem lintegral_norm_sq_perturb {D B : Set ℂ} (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hBD : B ⊆ D) (hBfin : volume B ≠ ⊤) {G H h : ℂ → ℂ} (hG : IntegrableOn G B volume)
    (hL2 : ∫⁻ x in D, ENNReal.ofReal (‖G x‖ ^ 2) ≠ ⊤) (hhm : AEStronglyMeasurable h volume)
    {c : ℝ} (hhc : ∀ x, ‖h x‖ ≤ c) (hh0 : ∀ x ∉ B, h x = 0) (hHout : ∀ x ∉ B, H x = G x)
    (hHae : H =ᵐ[volume] fun x => G x + h x) :
    ∃ r : ℝ, 0 ≤ r ∧ 0 ≤ r + 2 * (∫ x, inner ℝ (G x) (h x)) + ∫ x, ‖h x‖ ^ 2 ∧
      ∫⁻ x in D, ENNReal.ofReal (‖G x‖ ^ 2) = ENNReal.ofReal r ∧
      ∫⁻ x in D, ENNReal.ofReal (‖H x‖ ^ 2) =
        ENNReal.ofReal (r + 2 * (∫ x, inner ℝ (G x) (h x)) + ∫ x, ‖h x‖ ^ 2) := by
  set P := ∫⁻ x in D \ B, ENNReal.ofReal (‖G x‖ ^ 2) with hP
  have hPfin : P ≠ ⊤ := ne_top_of_le_ne_top hL2 (lintegral_mono_set sdiff_subset)
  have hDB : D ∩ B = B := inter_eq_right.2 hBD
  have hHrest : ∫⁻ x in D \ B, ENNReal.ofReal (‖H x‖ ^ 2) = P :=
    setLIntegral_congr_fun (hD.diff hB) fun x hx => by rw [hHout x hx.2]
  -- integrability on `B`
  have hGsq : IntegrableOn (fun x => ‖G x‖ ^ 2) B volume :=
    integrableOn_norm_sq_of_lintegral hBD hG.aestronglyMeasurable hL2
  have hinner : Integrable (fun x => inner ℝ (G x) (h x)) volume :=
    integrable_inner_of_integrableOn hB hG hhm hhc hh0
  have hhsq : IntegrableOn (fun x => ‖h x‖ ^ 2) B volume :=
    Measure.integrableOn_of_bounded (M := c ^ 2) hBfin (hhm.norm.pow 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hhc x) 2)
  have hGsum : IntegrableOn (fun x => ‖G x‖ ^ 2 + 2 * inner ℝ (G x) (h x)) B volume :=
    hGsq.add (hinner.integrableOn.const_mul 2)
  have hexp : (fun x => ‖H x‖ ^ 2) =ᵐ[volume.restrict B]
      fun x => ‖G x‖ ^ 2 + 2 * inner ℝ (G x) (h x) + ‖h x‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae hHae] with x hx
    rw [hx, norm_add_sq_real]
  have hHsq : IntegrableOn (fun x => ‖H x‖ ^ 2) B volume :=
    (hGsum.add hhsq).congr_fun_ae hexp.symm
  have hcompl1 : ∫ x in B, inner ℝ (G x) (h x) = ∫ x, inner ℝ (G x) (h x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hh0 x hx, inner_zero_right]
  have hcompl2 : ∫ x in B, ‖h x‖ ^ 2 = ∫ x, ‖h x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hh0 x hx]; simp
  have hHB : ∫ x in B, ‖H x‖ ^ 2 = (∫ x in B, ‖G x‖ ^ 2) + 2 * (∫ x, inner ℝ (G x) (h x)) +
      ∫ x, ‖h x‖ ^ 2 := by
    rw [integral_congr_ae hexp, integral_add hGsum hhsq,
      integral_add hGsq (hinner.integrableOn.const_mul 2), integral_const_mul, hcompl1, hcompl2]
  have hofG : ∫⁻ x in B, ENNReal.ofReal (‖G x‖ ^ 2) = ENNReal.ofReal (∫ x in B, ‖G x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hGsq (Eventually.of_forall fun x => sq_nonneg _)).symm
  have hofH : ∫⁻ x in B, ENNReal.ofReal (‖H x‖ ^ 2) = ENNReal.ofReal (∫ x in B, ‖H x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hHsq (Eventually.of_forall fun x => sq_nonneg _)).symm
  have hG0 : 0 ≤ ∫ x in B, ‖G x‖ ^ 2 := setIntegral_nonneg hB fun x _ => sq_nonneg _
  have hH0 : 0 ≤ ∫ x in B, ‖H x‖ ^ 2 := setIntegral_nonneg hB fun x _ => sq_nonneg _
  refine ⟨(∫ x in B, ‖G x‖ ^ 2) + P.toReal, by positivity, ?_, ?_, ?_⟩
  · have : (∫ x in B, ‖G x‖ ^ 2) + P.toReal + 2 * (∫ x, inner ℝ (G x) (h x)) +
        ∫ x, ‖h x‖ ^ 2 = (∫ x in B, ‖H x‖ ^ 2) + P.toReal := by rw [hHB]; ring
    rw [this]; positivity
  · rw [← lintegral_inter_add_sdiff _ D hB, hDB, hofG, ENNReal.ofReal_add hG0 ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hPfin]
  · rw [← lintegral_inter_add_sdiff _ D hB, hDB, hofH, hHrest, show (∫ x in B, ‖G x‖ ^ 2) + P.toReal +
        2 * (∫ x, inner ℝ (G x) (h x)) + ∫ x, ‖h x‖ ^ 2 = (∫ x in B, ‖H x‖ ^ 2) + P.toReal by
      rw [hHB]; ring, ENNReal.ofReal_add hH0 ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hPfin]

end Screening

end SandierSerfaty

end
