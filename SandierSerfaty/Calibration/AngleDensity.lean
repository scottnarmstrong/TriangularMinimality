/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.AngleInner
public import SandierSerfaty.Calibration.SectorPrimitive
public import SandierSerfaty.Dual.SectorToEnergy

/-!
# `cal:angle-density`: the sector functional as an integral of the angle density

For the model sector `S(d, α, β)` (`d > 0`, `|α|, |β| < π/2`, `α + β > 0`) and the
calibration data `radialData`,

`J(S(d, α, β)) = -2π ∫_S H - ½ ∫^ren_S |∇H|² = ∫_{-α}^β (f₀(d sec φ) - tan²φ e(d sec φ)) dφ`
(`modelSectorJ_eq`).

Proof: polar integration (`SectorPolar.lean`) with the radial integrals of `AngleInner.lean`:
`∫_S H` has density `srcDensity`; `|∇H|² = B'(‖w‖)² + restSq` where `restSq` is bounded (`bound_rest`), so
`∫_{S ∩ {‖w‖ > η}} |∇H|² + (α + β) log η = ∫ limDensity - (α+β) S₂(η) + ∫_{S ∩ {‖w‖ > η}} restSq`
(`B'²` integrates to `S₂(T) - S₂(η) + log T - log η` on each ray), whose limit as `η ↓ 0` is
`∫ limDensity + ∫_S restSq` (dominated convergence; `S₂(η) → 0`).
-/

open Set Filter Topology MeasureTheory Real intervalIntegral

public section

namespace SandierSerfaty

namespace Calibration

open SandierSerfaty.Dual

variable {d α β : ℝ}

theorem polar_integral_eq (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {η : ℝ} (hη : 0 ≤ η)
    {F : ℂ → ℝ}
    (hmeas : AEStronglyMeasurable (fun x : ℝ × ℝ => x.1 * F (Complex.polarCoord.symm x))
      (volume.restrict (polarRegion d α β η))) {C : ℝ}
    (hbd : ∀ w ∈ modelSector d α β ∩ {w : ℂ | η < ‖w‖}, ‖w‖ * |F w| ≤ C) (G : ℝ → ℝ)
    (hG : ∀ φ ∈ Ioo (-α) β, ∫ r in Ioo η (d / Real.cos φ), r * F (Complex.polarCoord.symm (r, φ)) = G φ) :
    IntegrableOn G (Ioo (-α) β) ∧
      ∫ w in modelSector d α β ∩ {w : ℂ | η < ‖w‖}, F w = ∫ φ in Ioo (-α) β, G φ := by
  obtain ⟨h1, h2⟩ := integral_modelSector_inter_polar hd hα hβ hη F
    (integrableOn_polarRegion hd hα hβ hη hmeas hbd)
  exact ⟨h1.congr_fun (fun φ hφ => hG φ hφ) measurableSet_Ioo,
    h2.trans (setIntegral_congr_fun measurableSet_Ioo hG)⟩

theorem inter_norm_pos_eq (d α β : ℝ) :
    modelSector d α β ∩ {w : ℂ | (0 : ℝ) < ‖w‖} = modelSector d α β :=
  inter_eq_left.2 fun _ hw => norm_pos_iff.2 (ne_zero_of_mem_modelSector hw)

theorem continuousOn_modelH (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    ContinuousOn (modelH radialData d) (modelSector d α β) := by
  obtain ⟨M, hM⟩ := exists_bnd_model hd hα hβ
  exact fun w hw => (hasFDerivAt_modelH hd hα hβ hM (by linarith) hw).continuousAt.continuousWithinAt

theorem norm_le_secRadius (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {w : ℂ}
    (hw : w ∈ modelSector d α β) : ‖w‖ ≤ secRadius d α β := by
  obtain ⟨r, φ, hr, hφ, hrt, rfl⟩ := exists_polar_rep hα hβ hw
  rw [polarCoord_symm_norm (x := (r, φ)) hr]
  exact r_le_secRadius hd hα hβ hφ hrt

theorem volume_modelSector_lt_top (hd : 0 < d) : volume (modelSector d α β) < ⊤ := by
  rw [volume_modelSector hd.le]; exact ENNReal.ofReal_lt_top

theorem measurable_restSq (d : ℝ) : Measurable (restSq d) := by
  unfold restSq
  exact (Torus.measurable_gradSq _).sub (((measurable_deriv B).comp measurable_norm).pow_const 2)

theorem measurable_deriv_B_sq : Measurable fun w : ℂ => (deriv B ‖w‖) ^ 2 :=
  ((measurable_deriv B).comp measurable_norm).pow_const 2

/-! ### The three polar integrals -/

theorem integral_modelH (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    IntegrableOn (srcDensity d) (Ioo (-α) β) ∧
      ∫ w in modelSector d α β, modelH radialData d w = ∫ φ in Ioo (-α) β, srcDensity d φ := by
  obtain ⟨C, hC⟩ := bound_H hd hα hβ
  have := polar_integral_eq hd hα hβ (η := 0) le_rfl
    (aestronglyMeasurable_polar_of_continuousOn hα hβ le_rfl (continuousOn_modelH hd hα hβ))
    (fun w hw => hC w hw.1) (srcDensity d) (fun φ hφ => inner_source hd hα hβ hφ)
  rwa [inter_norm_pos_eq] at this

theorem integral_restSq (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    IntegrableOn (restDensity d) (Ioo (-α) β) ∧
      ∫ w in modelSector d α β, restSq d w = ∫ φ in Ioo (-α) β, restDensity d φ := by
  obtain ⟨C, hC⟩ := bound_rest hd hα hβ
  have := polar_integral_eq hd hα hβ (η := 0) le_rfl
    (aestronglyMeasurable_polar_of_measurable (measurable_restSq d))
    (C := secRadius d α β * |C|)
    (fun w hw => mul_le_mul (norm_le_secRadius hd hα hβ hw.1) ((hC w hw.1).trans (le_abs_self C))
      (abs_nonneg _) (secRadius_pos hd hα hβ).le)
    (restDensity d) (fun φ hφ => inner_rest hd hα hβ hφ)
  rwa [inter_norm_pos_eq] at this

theorem integral_radial_sq_polar (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {η : ℝ}
    (hη : 0 < η) (hηd : η ≤ d) :
    IntegrableOn (fun φ => limDensity d φ - (S₂ η + Real.log η)) (Ioo (-α) β) ∧
      ∫ w in modelSector d α β ∩ {w : ℂ | η < ‖w‖}, (deriv B ‖w‖) ^ 2 =
        ∫ φ in Ioo (-α) β, (limDensity d φ - (S₂ η + Real.log η)) := by
  obtain ⟨C, hC⟩ := bound_radial_sq hd hα hβ hη
  refine polar_integral_eq hd hα hβ hη.le (aestronglyMeasurable_polar_of_measurable measurable_deriv_B_sq)
    (C := secRadius d α β * |C|)
    (fun w hw => ?_) _ (fun φ hφ => ?_)
  · rw [abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (norm_le_secRadius hd hα hβ hw.1) ((hC w hw.1 hw.2).trans (le_abs_self C))
      (sq_nonneg _) (secRadius_pos hd hα hβ).le
  · rw [inner_sing hd hα hβ hφ hη hηd]
    unfold limDensity
    ring

/-! ### The renormalized Dirichlet integral -/

theorem tendsto_S₂_zero : Tendsto S₂ (𝓝[>] 0) (𝓝 0) := by
  have hint : IntervalIntegrable (fun r => -2 * B₁ r + r * B₁ r ^ 2) volume 0 1 :=
    nearZero_S₂.intervalIntegrable one_pos
  have hc : ContinuousOn S₂ (uIcc (0 : ℝ) 1) :=
    intervalIntegral.continuousOn_primitive_interval' hint (by simp)
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := by simp
  have := (hc.continuousWithinAt h0).tendsto
  have e : S₂ 0 = 0 := by simp [S₂]
  rw [e] at this
  refine this.mono_left (nhdsWithin_le_of_mem ?_)
  exact mem_of_superset (Ioo_mem_nhdsGT one_pos) (fun x hx => by
    rw [uIcc_of_le zero_le_one]; exact ⟨hx.1.le, hx.2.le⟩)

theorem integrableOn_restSq (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    IntegrableOn (restSq d) (modelSector d α β) := by
  obtain ⟨C, hC⟩ := bound_rest hd hα hβ
  refine Measure.integrableOn_of_bounded (M := C) (volume_modelSector_lt_top hd).ne
    (measurable_restSq d).aestronglyMeasurable ?_
  exact (ae_restrict_iff' (measurableSet_modelSector d α β)).2
    (Filter.Eventually.of_forall fun w hw => by simpa using hC w hw)

theorem tendsto_gradSq_ren (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hαβ : 0 < α + β) :
    Tendsto (fun η : ℝ =>
      (∫ w in modelSector d α β ∩ {w : ℂ | η < ‖w‖}, Analysis.gradSq (modelH radialData d) w) +
        (α + β) * Real.log η) (𝓝[>] 0)
      (𝓝 ((∫ φ in Ioo (-α) β, limDensity d φ) + ∫ w in modelSector d α β, restSq d w)) := by
  have hrestInt := integrableOn_restSq hd hα hβ
  have hS0 : (0 : ℂ) ∉ modelSector d α β := fun h => by have := h.1; simp at this
  have hlim := Dual.tendsto_setIntegral_inter_norm_gt (measurableSet_modelSector d α β) hrestInt 0 hS0
  simp only [sub_zero] at hlim
  have hmain := (tendsto_const_nhds (x := ∫ φ in Ioo (-α) β, limDensity d φ)).sub
    ((tendsto_const_nhds (x := α + β)).mul tendsto_S₂_zero) |>.add hlim
  simp only [mul_zero, sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hd] with η hη
  set A := modelSector d α β ∩ {w : ℂ | η < ‖w‖} with hA
  have hAm : MeasurableSet A := (measurableSet_modelSector d α β).inter
    (measurableSet_lt measurable_const measurable_norm)
  have hAfin : volume A ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (volume_modelSector_lt_top (α := α) (β := β) hd)).ne
  obtain ⟨hlimInt, hsing⟩ := integral_radial_sq_polar hd hα hβ hη.1 hη.2.le
  obtain ⟨C, hC⟩ := bound_radial_sq hd hα hβ hη.1
  have hB : IntegrableOn (fun w : ℂ => (deriv B ‖w‖) ^ 2) A := by
    refine Measure.integrableOn_of_bounded (M := C) hAfin measurable_deriv_B_sq.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hAm).2 (Filter.Eventually.of_forall fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hC w hw.1 hw.2
  have hR : IntegrableOn (restSq d) A := hrestInt.mono_set inter_subset_left
  have hsplit : ∫ w in A, Analysis.gradSq (modelH radialData d) w =
      (∫ w in A, (deriv B ‖w‖) ^ 2) + ∫ w in A, restSq d w := by
    rw [← integral_add hB hR]
    refine setIntegral_congr_fun hAm fun w _ => ?_
    simp only [restSq]; ring
  rw [hsplit, hsing]
  have hvol : (volume.real (Ioo (-α) β)) = α + β := by
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hfin : volume (Ioo (-α) β) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hlimD : IntegrableOn (limDensity d) (Ioo (-α) β) :=
    (hlimInt.add (integrableOn_const hfin (C := S₂ η + Real.log η))).congr_fun
      (fun φ _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioo
  rw [integral_sub hlimD (integrableOn_const hfin), setIntegral_const, hvol]
  simp only [smul_eq_mul]
  ring

theorem integrableOn_limDensity (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    IntegrableOn (limDensity d) (Ioo (-α) β) := by
  have hfin : volume (Ioo (-α) β) ≠ ⊤ := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  obtain ⟨hlimInt, -⟩ := integral_radial_sq_polar hd hα hβ hd le_rfl
  exact (hlimInt.add (integrableOn_const hfin (C := S₂ d + Real.log d))).congr_fun
    (fun φ _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioo

/-- The renormalized Dirichlet integral of the trial potential on the model sector. -/
theorem modelSectorRen_eq (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hαβ : 0 < α + β) :
    modelSectorRen radialData d α β =
      (∫ φ in Ioo (-α) β, limDensity d φ) + ∫ w in modelSector d α β, restSq d w :=
  (tendsto_gradSq_ren hd hα hβ hαβ).limUnder_eq

theorem angleDensity_eq (d φ : ℝ) :
    angleDensity d φ = -(2 * π) * srcDensity d φ - 1 / 2 * (limDensity d φ + restDensity d φ) := by
  unfold angleDensity srcDensity limDensity restDensity f₀ e Tφ
  ring

/-- **`cal:angle-density`**: the sector functional is the integral of the angle density,
`J(S(d, α, β)) = ∫_{-α}^β (f₀(d sec φ) - tan²φ e(d sec φ)) dφ`. -/
theorem modelSectorJ_eq (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hαβ : 0 < α + β) :
    modelSectorJ radialData d α β = ∫ φ in (-α)..β, angleDensity d φ := by
  obtain ⟨hsrc, hH⟩ := integral_modelH hd hα hβ
  obtain ⟨hrest, hR⟩ := integral_restSq hd hα hβ
  have hlim := integrableOn_limDensity hd hα hβ
  unfold modelSectorJ
  rw [modelSectorRen_eq hd hα hβ hαβ, hH, hR,
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun φ _ => angleDensity_eq d φ)]
  symm
  rw [integral_sub (f := fun φ => -(2 * π) * srcDensity d φ)
    (g := fun φ => 1 / 2 * (limDensity d φ + restDensity d φ)) (hsrc.const_mul _)
    ((hlim.add hrest).const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_add hlim hrest]

/-- **`cal:sector-primitive`**: `J - λ A - μ θ = g_d(d tan α) + g_d(d tan β)`, for signed
endpoint angles. -/
theorem modelSectorJ_sub_eq (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hαβ : 0 < α + β) :
    modelSectorJ radialData d α β - lam * Dual.sectorArea d α β - mu * (α + β) =
      g d (d * Real.tan α) + g d (d * Real.tan β) := by
  rw [modelSectorJ_eq hd hα hβ hαβ]
  exact integral_angleDensity_sub hd hα hβ

/-- **The sector input from the primitive bound** (conditional helper; the scalar bound on `g` is the
certified estimate of `cal:scalar-bounds`, supplied elsewhere): if `K ≤ g_d(d tan α) + g_d(d tan β)` for all
`d ≥ d₀` and all signed endpoint angles, then `SectorBound radialData d₀ K λ μ` (`dual:sector-input`). -/
theorem sectorBound_of_primitive_bound {d₀ K : ℝ} (hd₀ : 0 < d₀)
    (h : ∀ d : ℝ, d₀ ≤ d → ∀ α β : ℝ, |α| < π / 2 → |β| < π / 2 → 0 < α + β →
      K ≤ g d (d * Real.tan α) + g d (d * Real.tan β)) :
    Dual.SectorBound radialData d₀ K lam mu := by
  intro d hd α β hα hβ hαβ
  have h1 := modelSectorJ_sub_eq (lt_of_lt_of_le hd₀ hd) hα hβ hαβ
  have h2 := h d hd α β hα hβ hαβ
  linarith

end Calibration

end SandierSerfaty

end
