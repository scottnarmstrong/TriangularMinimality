/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.AngleBounds

/-!
# The radial integrals along the rays of the model sector

Paper, verification of `cal:angle-density`. For `φ ∈ (-α, β)` and `T = d sec φ`, the three radial integrals of
`cal:angle-density` (the polar integrand is `r F(r e^{iφ})`):

* `inner_source`: `∫₀ᵀ r H dr = S₁(T) + T² ∑ Dᵢ(T)/(kᵢ+2)`;
* `inner_sing`: `∫_η^T r B'(r)² dr = S₂(T) - S₂(η) + log T - log η` for `0 < η ≤ T`;
* `inner_rest`: `∫₀ᵀ r · restSq dr = ∑ (-2 Dᵢ + 2 kᵢ Dᵢ H_{kᵢ}) + ∑_{i,j} kᵢkⱼ/(kᵢ+kⱼ) Dᵢ Dⱼ +
  tan²φ ∑_{i,j} Qᵢ Qⱼ/(kᵢ+kⱼ)` (all at `T`), the series of `f₀(T)` and `2 e(T)`.
-/

open Set Filter Topology MeasureTheory Real intervalIntegral

public section

namespace SandierSerfaty

namespace Calibration

open SandierSerfaty.Dual

variable {d α β : ℝ}

/-- The angular remainder `∑ (-2Dᵢ + 2kᵢDᵢH) + ∑ kᵢkⱼ/(kᵢ+kⱼ) DᵢDⱼ + tan²φ ∑ QᵢQⱼ/(kᵢ+kⱼ)` at `T = d sec φ`. -/
@[expose] noncomputable def restDensity (d φ : ℝ) : ℝ :=
  (∑' i, (-2 * D i (Tφ d φ) + 2 * (k i : ℝ) * D i (Tφ d φ) * H (k i) (Tφ d φ))) +
    (∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) *
      D ij.1 (Tφ d φ) * D ij.2 (Tφ d φ)) +
    Real.tan φ ^ 2 * ∑' ij : ℕ × ℕ, Q ij.1 (Tφ d φ) * Q ij.2 (Tφ d φ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ))

/-- The source density `S₁(T) + T² ∑ Dᵢ(T)/(kᵢ+2)` at `T = d sec φ`. -/
@[expose] noncomputable def srcDensity (d φ : ℝ) : ℝ :=
  S₁ (Tφ d φ) + Tφ d φ ^ 2 * ∑' i, D i (Tφ d φ) / ((k i : ℝ) + 2)

/-- The singular density `S₂(T) + log T` at `T = d sec φ`. -/
@[expose] noncomputable def limDensity (d φ : ℝ) : ℝ := S₂ (Tφ d φ) + Real.log (Tφ d φ)

theorem inner_source (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {φ : ℝ} (hφ : φ ∈ Ioo (-α) β) :
    ∫ r in Ioo 0 (d / Real.cos φ), r * modelH radialData d (Complex.polarCoord.symm (r, φ)) =
      srcDensity d φ := by
  obtain ⟨M, hM⟩ := exists_bnd_model hd hα hβ
  have hts := tφ_mem_T₁ hd hα hβ hφ
  have htpos := Tφ_pos hd hα hβ hφ
  have hc := summable_abs_D' hM hd hts
  have hT : d / Real.cos φ = Tφ d φ := rfl
  rw [hT]
  have hpt : ∫ r in Ioo 0 (Tφ d φ), r * modelH radialData d (Complex.polarCoord.symm (r, φ)) =
      ∫ r in Ioo 0 (Tφ d φ), (B r * r + r * ser (fun i => D i (Tφ d φ)) (Tφ d φ) r) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    have hrt : r * Real.cos φ < d := (lt_Tφ_iff hα hβ hφ).2 hr.2
    rw [modelH_polar hd hα hβ hr.1 hφ hrt]
    ring
  rw [hpt, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le htpos.le,
    intervalIntegral.integral_add (nearZero_S₁.intervalIntegrable htpos)
      (intervalIntegrable_r_ser hc htpos)]
  have h2 : ∫ r in (0 : ℝ)..Tφ d φ, r * ser (fun i => D i (Tφ d φ)) (Tφ d φ) r =
      Tφ d φ ^ 2 * ∑' i, D i (Tφ d φ) / ((k i : ℝ) + 2) := integral_source_series htpos hc
  rw [h2]
  rfl

theorem inner_sing (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {φ η : ℝ} (hφ : φ ∈ Ioo (-α) β)
    (hη : 0 < η) (hηd : η ≤ d) :
    ∫ r in Ioo η (d / Real.cos φ), r * (deriv B ‖(Complex.polarCoord.symm (r, φ) : ℂ)‖) ^ 2 =
      (S₂ (Tφ d φ) - S₂ η) + (Real.log (Tφ d φ) - Real.log η) := by
  have htd : d ≤ Tφ d φ := (Tφ_mem hd hα hβ hφ).1
  have hT : d / Real.cos φ = Tφ d φ := rfl
  rw [hT]
  have hpt : ∫ r in Ioo η (Tφ d φ), r * (deriv B ‖(Complex.polarCoord.symm (r, φ) : ℂ)‖) ^ 2 =
      ∫ r in Ioo η (Tφ d φ), r * (deriv B r) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    rw [polarCoord_symm_norm (x := (r, φ)) (hη.trans hr.1)]
  rw [hpt, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (hηd.trans htd)]
  exact integral_radial_sq hη (hηd.trans htd)

theorem inner_rest (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {φ : ℝ} (hφ : φ ∈ Ioo (-α) β) :
    ∫ r in Ioo 0 (d / Real.cos φ), r * restSq d (Complex.polarCoord.symm (r, φ)) = restDensity d φ := by
  obtain ⟨M, hM⟩ := exists_bnd_model hd hα hβ
  have hts := tφ_mem_T₁ hd hα hβ hφ
  have htpos := Tφ_pos hd hα hβ hφ
  have hT : d / Real.cos φ = Tφ d φ := rfl
  rw [hT]
  have hpt : ∫ r in Ioo 0 (Tφ d φ), r * restSq d (Complex.polarCoord.symm (r, φ)) =
      ∫ r in Ioo 0 (Tφ d φ),
        (2 * deriv B r * ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r +
          ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r ^ 2 / r +
          Real.tan φ ^ 2 * (ser (fun i => Q i (Tφ d φ)) (Tφ d φ) r ^ 2 / r)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
    have hrt : r * Real.cos φ < d := (lt_Tφ_iff hα hβ hφ).2 hr.2
    exact rest_polar hd hα hβ hr.1 hφ hrt
  rw [hpt, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le htpos.le]
  exact integral_rest_inner htpos (summable_abs_kD hM hd hts) (summable_abs_Q htpos) _

end Calibration

end SandierSerfaty

end
