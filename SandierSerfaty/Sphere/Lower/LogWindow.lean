/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# A one-dimensional logarithmic integral (for the sphere note's Lemma 6.9)

`logPlus t = max (log t) 0`. For `s > 0` and `ρ ∈ ℝ`, `∫_ℝ log₊ (1 / (2 s |ρ - r|)) dr = 1 / s`; consequently
`∫_A log₊ (1 / (2 s |ρ - r|)) dr ≤ 1 / s` for every set `A` (`lintegral_logPlus_le`).
-/

open MeasureTheory Set intervalIntegral
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- `log₊ t = max (log t) 0`. -/
@[expose] noncomputable def logPlus (t : ℝ) : ℝ := max (Real.log t) 0

theorem logPlus_nonneg (t : ℝ) : 0 ≤ logPlus t := le_max_right _ _

theorem negLog_integrable {s : ℝ} (hs : 0 < s) (δ : ℝ) :
    IntervalIntegrable (fun u : ℝ => -Real.log (2 * s * u)) volume 0 δ := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 2 * s * δ)).comp_mul_left (c := 2 * s)
  have hne : (2 * s) ≠ 0 := by positivity
  rw [zero_div, mul_div_cancel_left₀ _ hne] at h
  exact h.neg

theorem integral_negLog {s : ℝ} (hs : 0 < s) :
    ∫ u in (0:ℝ)..(1 / (2 * s)), -Real.log (2 * s * u) = 1 / (2 * s) := by
  have hne : (2 * s) ≠ 0 := by positivity
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_mul_left (fun x => Real.log x) hne, integral_log]
  have : 2 * s * (1 / (2 * s)) = 1 := by field_simp
  rw [this]
  simp

theorem negLogWindow {s : ℝ} (hs : 0 < s) (ρ : ℝ) :
    IntervalIntegrable (fun r => -Real.log (2 * s * |ρ - r|)) volume (ρ - 1 / (2 * s)) (ρ + 1 / (2 * s)) ∧
    ∫ r in (ρ - 1 / (2 * s))..(ρ + 1 / (2 * s)), -Real.log (2 * s * |ρ - r|) = 1 / s := by
  set δ := 1 / (2 * s) with hδ
  have hδ0 : 0 < δ := by positivity
  set f : ℝ → ℝ := fun u => -Real.log (2 * s * u) with hf
  have hint : IntervalIntegrable f volume 0 δ := negLog_integrable hs δ
  have hL : ∫ r in (ρ - δ)..ρ, -Real.log (2 * s * |ρ - r|) = δ := by
    have : ∫ r in (ρ - δ)..ρ, -Real.log (2 * s * |ρ - r|) = ∫ r in (ρ - δ)..ρ, f (ρ - r) := by
      refine intervalIntegral.integral_congr (fun r hr => ?_)
      rw [uIcc_of_le (by linarith)] at hr
      simp only [hf]
      rw [abs_of_nonneg (by linarith [hr.2])]
    rw [this, intervalIntegral.integral_comp_sub_left f ρ]
    simp only [sub_self, sub_sub_cancel]
    exact integral_negLog hs
  have hR : ∫ r in ρ..(ρ + δ), -Real.log (2 * s * |ρ - r|) = δ := by
    have : ∫ r in ρ..(ρ + δ), -Real.log (2 * s * |ρ - r|) = ∫ r in ρ..(ρ + δ), f (r - ρ) := by
      refine intervalIntegral.integral_congr (fun r hr => ?_)
      rw [uIcc_of_le (by linarith)] at hr
      simp only [hf]
      rw [abs_of_nonpos (by linarith [hr.1])]
      simp
    rw [this, intervalIntegral.integral_comp_sub_right f ρ]
    simp only [sub_self, add_sub_cancel_left]
    exact integral_negLog hs
  have iL : IntervalIntegrable (fun r => -Real.log (2 * s * |ρ - r|)) volume (ρ - δ) ρ := by
    have h1 := (hint.comp_sub_left ρ).symm
    simp only [sub_zero] at h1
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 h1
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 (h2.congr_fun ?_ measurableSet_Ioc)
    intro r hr
    simp only [hf]
    rw [abs_of_nonneg (by linarith [hr.2])]
  have iR : IntervalIntegrable (fun r => -Real.log (2 * s * |ρ - r|)) volume ρ (ρ + δ) := by
    have h1 := hint.comp_sub_right ρ
    rw [zero_add, add_comm δ ρ] at h1
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 h1
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2 (h2.congr_fun ?_ measurableSet_Ioc)
    intro r hr
    simp only [hf]
    rw [abs_of_nonpos (by linarith [hr.1])]
    simp
  refine ⟨iL.trans iR, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals iL iR, hL, hR]
  simp only [hδ]
  field_simp
  ring

theorem logPlus_eq {s u : ℝ} (hu : 0 ≤ u) : logPlus (1 / (2 * (s * u))) = max (-Real.log (2 * s * u)) 0 := by
  unfold logPlus
  rcases hu.eq_or_lt with rfl | hu
  · simp
  · rw [one_div, Real.log_inv]
    rw [← mul_assoc]

theorem lintegral_logPlus_le {s : ℝ} (hs : 0 < s) (ρ : ℝ) (A : Set ℝ) :
    ∫⁻ r in A, ENNReal.ofReal (logPlus (1 / (2 * (s * |ρ - r|)))) ≤ ENNReal.ofReal (1 / s) := by
  set δ := 1 / (2 * s) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨hint, hval⟩ := negLogWindow hs ρ
  set W : Set ℝ := Icc (ρ - δ) (ρ + δ) with hW
  set g : ℝ → ℝ := fun r => -Real.log (2 * s * |ρ - r|) with hg
  have hpt : ∀ r, ENNReal.ofReal (logPlus (1 / (2 * (s * |ρ - r|)))) ≤ W.indicator (fun r => ENNReal.ofReal (g r)) r := by
    intro r
    rw [logPlus_eq (abs_nonneg _)]
    by_cases hr : r ∈ W
    · rw [Set.indicator_of_mem hr]
      apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ g r := by
        simp only [hg, neg_nonneg]
        apply Real.log_nonpos (by positivity)
        have : |ρ - r| ≤ δ := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
        calc 2 * s * |ρ - r| ≤ 2 * s * δ := by gcongr
          _ = 1 := by rw [hδ]; field_simp
      exact max_le le_rfl this
    · rw [Set.indicator_of_notMem hr]
      have : |ρ - r| > δ := by
        by_contra hcon
        push Not at hcon
        rw [abs_le] at hcon
        exact hr ⟨by linarith [hcon.1, hcon.2], by linarith [hcon.1, hcon.2]⟩
      have h1 : 1 < 2 * s * |ρ - r| := by
        calc (1 : ℝ) = 2 * s * δ := by rw [hδ]; field_simp
          _ < 2 * s * |ρ - r| := by gcongr
      have : -Real.log (2 * s * |ρ - r|) ≤ 0 := by
        have := Real.log_pos h1
        linarith
      simp [max_eq_right this]
  calc ∫⁻ r in A, ENNReal.ofReal (logPlus (1 / (2 * (s * |ρ - r|))))
      ≤ ∫⁻ r, ENNReal.ofReal (logPlus (1 / (2 * (s * |ρ - r|)))) := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ r, W.indicator (fun r => ENNReal.ofReal (g r)) r := lintegral_mono hpt
    _ = ∫⁻ r in W, ENNReal.ofReal (g r) := lintegral_indicator measurableSet_Icc _
    _ = ENNReal.ofReal (∫ r in W, g r) := by
        refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
        · have h1 : IntegrableOn g (Ioc (ρ - δ) (ρ + δ)) :=
            (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 hint
          exact (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).2 h1
        · refine ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_)
          simp only [hg, Pi.zero_apply, neg_nonneg]
          apply Real.log_nonpos (by positivity)
          have : |ρ - r| ≤ δ := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
          calc 2 * s * |ρ - r| ≤ 2 * s * δ := by gcongr
            _ = 1 := by rw [hδ]; field_simp
    _ = ENNReal.ofReal (1 / s) := by
        rw [hW, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
        exact congrArg ENNReal.ofReal hval

end Lower

end Sphere

end SandierSerfaty

end
