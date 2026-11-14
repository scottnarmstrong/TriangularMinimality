/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.BlowupWeak
public import SandierSerfaty.Sphere.Lower.LipschitzWeak

/-!
# The truncated potential `H_η` (sphere note, Lemma 6.7, Proposition 6.13)

`Lower.truncPot X η = H - ∑ᵢ f_η(· - s xᵢ)` written without the junk values at the points:
`H_η(x) = ∑ᵢ (-log max(|x - s xᵢ|, η) + log s) + (n/2) V(x/s)`.  It agrees with `H - ∑ f_η(· - s xᵢ)` off the points
(`Lower.truncPot_eq`), is locally Lipschitz (`Lower.locallyLipschitz_truncPot`), and satisfies
`∫ H_η Δχ = -2π (∑ᵢ ⨍_{∂B(s xᵢ, η)} χ - ∫ m χ)` (`Lower.integral_truncPot_mul_lap`).
-/

open MeasureTheory Set Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- `log` is `1/η`-Lipschitz on `[η, ∞)`. -/
theorem abs_log_sub_log_le {η a b : ℝ} (hη : 0 < η) (ha : η ≤ a) (hb : η ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / η := by
  have key : ∀ a b : ℝ, η ≤ b → b ≤ a → Real.log a - Real.log b ≤ (a - b) / η := by
    intro a b hb hba
    have hb0 : 0 < b := hη.trans_le hb
    have ha0 : 0 < a := by linarith
    have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by linarith) hb0.ne'] at h1
    have h2 : a / b - 1 = (a - b) / b := by field_simp
    rw [h2] at h1
    refine h1.trans ?_
    exact div_le_div_of_nonneg_left (by linarith) hη hb
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith [Real.log_le_log (hη.trans_le hb) h]), abs_of_nonneg (by linarith)]
    exact key a b hb h
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (by linarith [Real.log_le_log (hη.trans_le ha) h]),
      abs_of_nonneg (by linarith)]
    exact key b a ha h

theorem lipschitz_logMax {η : ℝ} (hη : 0 < η) (p : ℂ) :
    LipschitzWith (Real.toNNReal (1 / η)) (fun x : ℂ => Real.log (max ‖x - p‖ η)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal (1 / η) (by positivity)]
  have h1 := abs_log_sub_log_le hη (le_max_right ‖x - p‖ η) (le_max_right ‖y - p‖ η)
  have h2 : |max ‖x - p‖ η - max ‖y - p‖ η| ≤ ‖x - y‖ := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have := abs_norm_sub_norm_le (x - p) (y - p)
    simpa using this
  calc |Real.log (max ‖x - p‖ η) - Real.log (max ‖y - p‖ η)| ≤ |max ‖x - p‖ η - max ‖y - p‖ η| / η := h1
    _ ≤ ‖x - y‖ / η := by gcongr
    _ = 1 / η * ‖x - y‖ := by ring

theorem locallyLipschitz_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℝ}
    (hf : ∀ i ∈ s, LocallyLipschitz (f i)) : LocallyLipschitz fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LipschitzWith.const (0 : ℝ)).locallyLipschitz
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The truncated potential `H_η = H - ∑ f_η(· - s xᵢ)`, junk-free form. -/
@[expose] noncomputable def truncPot {n : ℕ} (X : Fin n → ℂ) (η : ℝ) (x : ℂ) : ℝ :=
  ∑ i, (-Real.log (max ‖x - blowupScale n • X i‖ η) + Real.log (blowupScale n)) +
    (n : ℝ) / 2 * potV ((blowupScale n)⁻¹ • x)

theorem locallyLipschitz_truncPot {n : ℕ} (X : Fin n → ℂ) {η : ℝ} (hη : 0 < η) :
    LocallyLipschitz (truncPot X η) := by
  unfold truncPot
  refine (locallyLipschitz_finsetSum _ fun i _ => ?_).add ?_
  · exact ((lipschitz_logMax hη _).locallyLipschitz.neg.add (LipschitzWith.const _).locallyLipschitz :)
  · exact (((contDiff_potV.comp (contDiff_const_smul _)).const_smul ((n : ℝ) / 2)).of_le (by norm_cast)).locallyLipschitz

/-- Off the points, `H_η = H - ∑ f_η(· - s xᵢ)`. -/
theorem truncPot_eq {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {η : ℝ} (hη : 0 < η) {x : ℂ}
    (hx : ∀ i, x ≠ blowupScale n • X i) :
    truncPot X η x = blowupPot X x - ∑ i, truncLog η (x - blowupScale n • X i) := by
  have hs := blowupScale_pos hn
  unfold truncPot blowupPot chartPot gKer
  have hi : ∀ i, -Real.log (max ‖x - blowupScale n • X i‖ η) + Real.log (blowupScale n) =
      -Real.log ‖(blowupScale n)⁻¹ • x - X i‖ - truncLog η (x - blowupScale n • X i) := by
    intro i
    have e : (blowupScale n)⁻¹ • x - X i = (blowupScale n)⁻¹ • (x - blowupScale n • X i) := by
      rw [smul_sub, inv_smul_smul₀ hs.ne']
    have h0 : ‖x - blowupScale n • X i‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (hx i))
    have h0' : 0 < ‖x - blowupScale n • X i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le),
      Real.log_mul (inv_pos.2 hs).ne' h0, Real.log_inv]
    unfold truncLog
    rcases le_total ‖x - blowupScale n • X i‖ η with h | h
    · rw [max_eq_right h, max_eq_left (by
        have := Real.log_le_log h0' h
        linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by
        have := Real.log_le_log hη h
        linarith)]
      ring
  rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_sub_distrib]
  ring

theorem integrable_truncLog_mul_lap {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {η : ℝ} (hη : 0 < η) (p : ℂ) : Integrable fun x : ℂ => truncLog η (x - p) * Δ φ x := by
  have hlap := contDiff_lap hφ
  have hlc := hasCompactSupport_lap hc
  obtain ⟨C, hC⟩ := hlap.continuous.bounded_above_of_compact_support hlc
  have hint : Integrable (fun x : ℂ => truncLog η (x - p)) volume :=
    (Screening.integrable_truncLog hη).comp_sub_right p
  exact hint.mul_bdd hlap.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- **Distributional Laplacian of `H_η`**: `∫ H_η Δχ = -2π (∑ᵢ ⨍_{∂B(s xᵢ, η)} χ - ∫ m χ)`. -/
theorem integral_truncPot_mul_lap {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) :
    ∫ x, truncPot X η x * Δ φ x =
      -(2 * Real.pi * ((∑ i, Real.circleAverage φ (blowupScale n • X i) η) -
        ∫ x, blowupDens n x * φ x)) := by
  have hae : ∀ᵐ x : ℂ, truncPot X η x * Δ φ x =
      blowupPot X x * Δ φ x - ∑ i, truncLog η (x - blowupScale n • X i) * Δ φ x := by
    filter_upwards [(Set.countable_range fun i => blowupScale n • X i).ae_notMem (volume : Measure ℂ)]
      with x hx
    have hx' : ∀ i, x ≠ blowupScale n • X i := fun i h => hx ⟨i, h.symm⟩
    rw [truncPot_eq hn X hη hx', sub_mul, Finset.sum_mul]
  rw [integral_congr_ae hae, integral_sub (integrable_blowupPot_mul_lap hn X hφ hc)
    (integrable_finsetSum _ fun i _ => integrable_truncLog_mul_lap hφ hc hη _),
    integral_finsetSum _ fun i _ => integrable_truncLog_mul_lap hφ hc hη _]
  have h1 := integral_blowupPot_mul_lap hn X hφ hc
  simp only [integral_truncLog_mul_lap hφ hη]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  linarith

/-- **Integration by parts for `H_η`**: `∫ H_η Δχ = -∑_e ∫ ∂_e H_η ∂_e χ`. -/
theorem integral_truncPot_mul_lap_eq {n : ℕ} (X : Fin n → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) :
    ∫ x, truncPot X η x * Δ φ x =
      -(∫ x, fderiv ℝ (truncPot X η) x 1 * fderiv ℝ φ x 1) -
        ∫ x, fderiv ℝ (truncPot X η) x Complex.I * fderiv ℝ φ x Complex.I := by
  have hL := locallyLipschitz_truncPot X hη
  have h1 : ∀ x, Δ φ x = Weyl.pd 1 (Weyl.pd 1 φ) x + Weyl.pd Complex.I (Weyl.pd Complex.I φ) x :=
    fun x => Weyl.lap_eq_pd ((hφ.of_le (by norm_cast)).contDiffAt)
  have hpd : ∀ v : ℂ, ContDiff ℝ 1 (Weyl.pd v φ) := fun v =>
    Weyl.contDiff_pd (m := 1) hφ (by norm_cast) v
  have hpc : ∀ v : ℂ, HasCompactSupport (Weyl.pd v φ) := fun v => hc.fderiv_apply ℝ v
  have hI : ∀ v : ℂ, Integrable fun x => truncPot X η x * Weyl.pd v (Weyl.pd v φ) x := fun v => by
    refine ((hL.continuous).mul ((Weyl.contDiff_pd (m := 0) (hpd v) (by norm_cast) v).continuous)
      ).integrable_of_hasCompactSupport ((hpc v).fderiv_apply ℝ v).mul_left
  have e1 : ∀ v : ℂ, ∫ x, truncPot X η x * Weyl.pd v (Weyl.pd v φ) x =
      -∫ x, fderiv ℝ (truncPot X η) x v * fderiv ℝ φ x v := fun v =>
    integral_mul_fderiv_of_locallyLipschitz hL (hpd v) (hpc v) v
  simp only [h1, mul_add]
  rw [integral_add (hI 1) (hI Complex.I), e1 1, e1 Complex.I]
  ring

end Lower

end Sphere

end SandierSerfaty

end
