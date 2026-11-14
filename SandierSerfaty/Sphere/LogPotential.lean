/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Density
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog

/-!
# The logarithmic potential of `µ` (sphere note, Lemma 3.2)

With `g(z) = -log |z|`, `Sphere.potU x = ∫_ℂ g(x - y) µ(y) dy`.

* `Sphere.integral_polar`: polar coordinates for an integrable measurable function on `ℂ`;
* `Sphere.integral_log_norm_sub_circle`: the circle average `⨍ log |x - r e^{iθ}| dθ = log max(r, |x|)`;
* `Sphere.potU_eq`: `U = -V / 2`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

/-- The kernel `g(z) = -log |z|` of the planar Coulomb interaction. -/
@[expose] noncomputable def gKer (z : ℂ) : ℝ := -Real.log ‖z‖

/-- The logarithmic potential `U(x) = ∫ g(x - y) µ(y) dy` of the density `µ`. -/
@[expose] noncomputable def potU (x : ℂ) : ℝ := ∫ y : ℂ, gKer (x - y) * dens y

theorem integrableOn_polar {F : ℂ → ℝ} (hm : Measurable F) (hF : Integrable F) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hcont : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]; fun_prop
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p)) :=
    measurable_fst.smul (hm.comp hcont.measurable)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hT : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have h := Complex.lintegral_comp_polarCoord_symm (fun x => ‖F x‖ₑ)
  rw [polarCoord_target] at h
  unfold HasFiniteIntegral
  calc ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, ‖p.1 • F (Complex.polarCoord.symm p)‖ₑ
      = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 • ‖F (Complex.polarCoord.symm p)‖ₑ := by
        refine setLIntegral_congr_fun hT (fun p hp => ?_)
        rw [enorm_smul, Real.enorm_eq_ofReal (le_of_lt hp.1)]
        rfl
    _ = ∫⁻ x, ‖F x‖ₑ := h
    _ < ∞ := hF.2

/-- **Polar coordinates** for an integrable measurable function on `ℂ`. -/
theorem integral_polar {F : ℂ → ℝ} (hm : Measurable F) (hF : Integrable F) :
    ∫ x, F x = ∫ r in Ioi (0 : ℝ), r * ∫ θ in Ioo (-Real.pi) Real.pi, F (circleMap 0 r θ) := by
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  rw [hvol, setIntegral_prod _ (hvol ▸ integrableOn_polar hm hF)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  simp only [smul_eq_mul]
  rw [integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  have e : circleMap 0 r θ = (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
    rw [circleMap, zero_add, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [e, Complex.polarCoord_symm_apply]

theorem integral_Ioo_eq_circleAverage (φ : ℂ → ℝ) (R : ℝ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, φ (circleMap 0 R θ) = 2 * Real.pi * Real.circleAverage φ 0 R := by
  have hpi := Real.pi_pos
  have hper : Function.Periodic (fun θ : ℝ => φ (circleMap 0 R θ)) (2 * Real.pi) :=
    fun θ => by
      show φ (circleMap 0 R (θ + 2 * Real.pi)) = φ (circleMap 0 R θ)
      rw [periodic_circleMap 0 R θ]
  have hshift : ∫ θ in (-Real.pi)..Real.pi, φ (circleMap 0 R θ) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, φ (circleMap 0 R θ) := by
    have := hper.intervalIntegral_add_eq (-Real.pi) 0
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at this
    exact this
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), hshift,
    Real.circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The circle average of `log |x - ·|`: `⨍ log |x - r e^{iθ}| dθ = log max(r, |x|)`. -/
theorem integral_log_norm_sub_circle (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ θ in Ioo (-Real.pi) Real.pi, Real.log ‖x - circleMap 0 r θ‖ =
      2 * Real.pi * Real.log (max r ‖x‖) := by
  have h1 := integral_Ioo_eq_circleAverage (fun z : ℂ => Real.log ‖z - x‖) r
  simp only [norm_sub_rev x] at h1 ⊢
  rw [h1, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
  congr 1
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  rw [zero_sub, norm_neg]
  rcases le_total ‖x‖ r with h | h
  · have h2 : r⁻¹ * ‖x‖ ≤ 1 := by rw [inv_mul_le_iff₀ hr]; linarith
    rw [(Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (by positivity)]; exact h2),
      max_eq_left h, add_zero]
  · rcases eq_or_lt_of_le hx with h0 | h0
    · have : ‖x‖ = 0 := h0.symm
      simp [this, hr.le]
    · have h2 : 1 ≤ r⁻¹ * ‖x‖ := by rw [le_inv_mul_iff₀ hr]; linarith
      rw [Real.posLog_eq_log (by rw [abs_of_nonneg (by positivity)]; exact h2), max_eq_right h,
        Real.log_mul (by positivity) h0.ne', Real.log_inv]
      ring

/-- **Lemma 3.2.** `U = -V / 2`. -/
theorem potU_eq (x : ℂ) : potU x = -(potV x / 2) := by
  have hpi := Real.pi_pos
  have hm : Measurable fun y : ℂ => Real.log ‖x - y‖ * dens y := by
    have := measurable_dens
    fun_prop
  have hi := integrable_log_dens x
  have h1 : potU x = - ∫ y : ℂ, Real.log ‖x - y‖ * dens y := by
    unfold potU gKer
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp
  rw [h1, integral_polar hm hi]
  have h2 : ∀ r ∈ Ioi (0 : ℝ),
      r * ∫ θ in Ioo (-Real.pi) Real.pi, Real.log ‖x - circleMap 0 r θ‖ * dens (circleMap 0 r θ) =
        2 * Real.pi * (r * (densR r * Real.log (max r ‖x‖))) := by
    intro r hr
    have hr : 0 < r := hr
    have hd : ∀ θ : ℝ, dens (circleMap 0 r θ) = densR r := fun θ => by
      rw [dens_eq_densR, norm_circleMap_zero, abs_of_pos hr]
    simp only [hd]
    rw [integral_mul_const, integral_log_norm_sub_circle x hr]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h2, integral_const_mul,
    integral_log_max (norm_nonneg x)]
  unfold potV
  field_simp
  ring

end Sphere

end SandierSerfaty

end
