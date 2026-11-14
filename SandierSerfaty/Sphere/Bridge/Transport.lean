/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Defs
public import SandierSerfaty.Screening.TruncLogCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Transport of charge fields by a similarity of the plane

For `σ > 0`, a linear isometry `L` of `ℂ` and `c ∈ ℂ`, the similarity `A y = L (σ y) + c`
(`Bridge.simMap`) and the transported field `E_A(x) = σ⁻¹ L E(A⁻¹ x)` (`Bridge.simField`):

* `Bridge.map_simMap`: `A_* (Lebesgue) = σ⁻² · Lebesgue`, hence the change of variables
  `Bridge.integral_comp_simMap`, `Bridge.lintegral_comp_simMap`;
* `Bridge.gradient_comp_simMap`: `∇(φ ∘ A)(y) = σ L⁻¹ ∇φ(A y)` (at every point);
* `Bridge.isNeumannChargeField_simField`: a Neumann charge field on `Q` with density `σ² m'` and
  charges `Y` is carried to a Neumann charge field on `A Q` with density `m'` and charges `A Y`;
* `Bridge.truncField_simField`: off the charges, `(E_A)_{σρ∘A⁻¹}(A y) = σ⁻¹ L E_ρ(y)`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal NNReal ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

/-- The similarity `y ↦ L (σ y) + c`. -/
@[expose] noncomputable def simMap (σ : ℝ) (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) (y : ℂ) : ℂ := L (σ • y) + c

/-- The inverse similarity `x ↦ σ⁻¹ L⁻¹ (x - c)`. -/
@[expose] noncomputable def simInv (σ : ℝ) (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) (x : ℂ) : ℂ := σ⁻¹ • L.symm (x - c)

/-- The transported field `E_A(x) = σ⁻¹ L E(A⁻¹ x)`. -/
@[expose] noncomputable def simField (σ : ℝ) (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) (E : ℂ → ℂ) (x : ℂ) : ℂ :=
  σ⁻¹ • L (E (simInv σ L c x))

variable {σ : ℝ} {L : ℂ ≃ₗᵢ[ℝ] ℂ} {c : ℂ}

theorem simInv_simMap (hσ : σ ≠ 0) (y : ℂ) : simInv σ L c (simMap σ L c y) = y := by
  simp only [simInv, simMap, add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply,
    inv_smul_smul₀ hσ]

theorem simMap_simInv (hσ : σ ≠ 0) (x : ℂ) : simMap σ L c (simInv σ L c x) = x := by
  simp only [simMap, simInv, smul_inv_smul₀ hσ, LinearIsometryEquiv.apply_symm_apply, sub_add_cancel]

theorem simMap_sub (y z : ℂ) : simMap σ L c y - simMap σ L c z = L (σ • (y - z)) := by
  simp [simMap, smul_sub]

theorem norm_simMap_sub (hσ : 0 < σ) (y z : ℂ) :
    ‖simMap σ L c y - simMap σ L c z‖ = σ * ‖y - z‖ := by
  rw [simMap_sub, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]

theorem simMap_injective (hσ : σ ≠ 0) : Function.Injective (simMap σ L c) := fun y z h => by
  rw [← simInv_simMap (L := L) (c := c) hσ y, h, simInv_simMap hσ]

theorem continuous_simMap : Continuous (simMap σ L c) :=
  (L.continuous.comp (continuous_const_smul σ)).add continuous_const

theorem continuous_simInv : Continuous (simInv σ L c) := by
  unfold simInv
  exact (L.symm.continuous.comp (continuous_id.sub continuous_const)).const_smul (σ⁻¹ : ℝ)

theorem contDiff_simMap : ContDiff ℝ ∞ (simMap σ L c) := by
  unfold simMap
  exact ((L.toContinuousLinearEquiv : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_const_smul σ)).add
    contDiff_const

/-- The similarity as a homeomorphism. -/
@[expose] noncomputable def simHomeomorph (hσ : σ ≠ 0) (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c : ℂ) : ℂ ≃ₜ ℂ where
  toFun := simMap σ L c
  invFun := simInv σ L c
  left_inv := simInv_simMap hσ
  right_inv := simMap_simInv hσ
  continuous_toFun := continuous_simMap
  continuous_invFun := continuous_simInv

theorem measurableEmbedding_simMap (hσ : σ ≠ 0) : MeasurableEmbedding (simMap σ L c) :=
  (simHomeomorph hσ L c).measurableEmbedding

theorem mem_image_simMap_iff (hσ : σ ≠ 0) {S : Set ℂ} {y : ℂ} :
    simMap σ L c y ∈ simMap σ L c '' S ↔ y ∈ S :=
  (simMap_injective hσ).mem_set_image

theorem measurableSet_image_simMap (hσ : σ ≠ 0) {S : Set ℂ} (hS : MeasurableSet S) :
    MeasurableSet (simMap σ L c '' S) :=
  (measurableEmbedding_simMap hσ).measurableSet_image' hS

theorem indicator_image_simMap (hσ : σ ≠ 0) {β : Type*} [Zero β] (S : Set ℂ) (f : ℂ → β) (y : ℂ) :
    (simMap σ L c '' S).indicator f (simMap σ L c y) = S.indicator (fun y => f (simMap σ L c y)) y := by
  by_cases hy : y ∈ S
  · rw [indicator_of_mem ((mem_image_simMap_iff hσ).2 hy), indicator_of_mem hy]
  · rw [indicator_of_notMem (fun h => hy ((mem_image_simMap_iff hσ).1 h)), indicator_of_notMem hy]

/-! ### Change of variables -/

theorem map_simMap (hσ : 0 < σ) :
    Measure.map (simMap σ L c) volume = ENNReal.ofReal (σ ^ 2)⁻¹ • volume := by
  have e : simMap σ L c = (fun x => L x + c) ∘ (fun y : ℂ => σ • y) := rfl
  have hLm : Measurable (fun x => L x + c) := (L.continuous.add continuous_const).measurable
  rw [e, ← Measure.map_map hLm (measurable_const_smul σ),
    Measure.map_addHaar_smul volume hσ.ne', Complex.finrank_real_complex,
    Measure.map_smul _ hLm.aemeasurable]
  have hmp : MeasurePreserving (fun x => L x + c) volume volume :=
    (measurePreserving_add_right volume c).comp L.measurePreserving
  rw [hmp.map_eq, abs_of_pos (inv_pos.2 (by positivity))]

theorem integral_comp_simMap (hσ : 0 < σ) (f : ℂ → ℝ) :
    ∫ y, f (simMap σ L c y) = (σ ^ 2)⁻¹ * ∫ x, f x := by
  rw [← (measurableEmbedding_simMap hσ.ne').integral_map, map_simMap hσ, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem lintegral_comp_simMap (hσ : 0 < σ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ y, f (simMap σ L c y) = ENNReal.ofReal (σ ^ 2)⁻¹ * ∫⁻ x, f x := by
  rw [← (measurableEmbedding_simMap hσ.ne').lintegral_map, map_simMap hσ, lintegral_smul_measure,
    smul_eq_mul]

theorem integrable_comp_simMap_iff (hσ : 0 < σ) {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    Integrable (fun y => f (simMap σ L c y)) ↔ Integrable f := by
  rw [← Function.comp_def, ← (measurableEmbedding_simMap hσ.ne').integrable_map_iff, map_simMap hσ,
    integrable_smul_measure (by simp; positivity) ENNReal.ofReal_ne_top]

theorem setIntegral_image_simMap (hσ : 0 < σ) {S : Set ℂ} (hS : MeasurableSet S) (f : ℂ → ℝ) :
    ∫ x in simMap σ L c '' S, f x = σ ^ 2 * ∫ y in S, f (simMap σ L c y) := by
  rw [← integral_indicator (measurableSet_image_simMap hσ.ne' hS), ← integral_indicator hS]
  have h := integral_comp_simMap (L := L) (c := c) hσ ((simMap σ L c '' S).indicator f)
  simp only [indicator_image_simMap hσ.ne'] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem setLIntegral_image_simMap (hσ : 0 < σ) {S : Set ℂ} (hS : MeasurableSet S) (f : ℂ → ℝ≥0∞) :
    ∫⁻ x in simMap σ L c '' S, f x = ENNReal.ofReal (σ ^ 2) * ∫⁻ y in S, f (simMap σ L c y) := by
  rw [← lintegral_indicator (measurableSet_image_simMap hσ.ne' hS), ← lintegral_indicator hS]
  have h := lintegral_comp_simMap (L := L) (c := c) hσ ((simMap σ L c '' S).indicator f)
  simp only [indicator_image_simMap hσ.ne'] at h
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

theorem integrableOn_image_simMap_iff (hσ : 0 < σ) {S : Set ℂ} (hS : MeasurableSet S)
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    IntegrableOn f (simMap σ L c '' S) ↔ IntegrableOn (fun y => f (simMap σ L c y)) S := by
  rw [← integrable_indicator_iff (measurableSet_image_simMap hσ.ne' hS),
    ← integrable_indicator_iff hS, ← integrable_comp_simMap_iff (L := L) (c := c) hσ]
  simp only [indicator_image_simMap hσ.ne']

/-! ### Gradients -/

/-- The linear part `σ L` as a continuous linear equivalence. -/
@[expose] noncomputable def simLin (hσ : σ ≠ 0) (L : ℂ ≃ₗᵢ[ℝ] ℂ) : ℂ ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.smulLeft (Units.mk0 σ hσ)).trans L.toContinuousLinearEquiv

theorem fderiv_comp_simMap (hσ : σ ≠ 0) (φ : ℂ → ℝ) (y v : ℂ) :
    fderiv ℝ (fun y => φ (simMap σ L c y)) y v = fderiv ℝ φ (simMap σ L c y) (L (σ • v)) := by
  have e : (fun y => φ (simMap σ L c y)) = (fun z => φ (z + c)) ∘ simLin hσ L := rfl
  rw [e, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    fderiv_comp_add_right]
  rfl

/-- `∇(φ ∘ A)(y) = σ L⁻¹ ∇φ(A y)`, at every point. -/
theorem gradient_comp_simMap (hσ : σ ≠ 0) (φ : ℂ → ℝ) (y : ℂ) :
    gradient (fun y => φ (simMap σ L c y)) y = σ • L.symm (gradient φ (simMap σ L c y)) := by
  refine ext_inner_right ℝ fun v => ?_
  rw [Screening.inner_gradient_left, fderiv_comp_simMap hσ, real_inner_smul_left,
    ← LinearIsometryEquiv.inner_map_map L, L.apply_symm_apply, Screening.inner_gradient_left,
    map_smul, ContinuousLinearMap.map_smul, smul_eq_mul]

theorem inner_simField_gradient (hσ : 0 < σ) (E : ℂ → ℂ) (φ : ℂ → ℝ) (y : ℂ) :
    inner ℝ (simField σ L c E (simMap σ L c y)) (gradient φ (simMap σ L c y)) =
      (σ ^ 2)⁻¹ * inner ℝ (E y) (gradient (fun y => φ (simMap σ L c y)) y) := by
  rw [gradient_comp_simMap hσ.ne', simField, simInv_simMap hσ.ne', real_inner_smul_left,
    real_inner_smul_right, ← LinearIsometryEquiv.inner_map_map L (E y), L.apply_symm_apply]
  field_simp

/-! ### Neumann charge fields -/

/-- **Transport of Neumann charge fields**: density `σ² m'` on `Q` with charges `Y` becomes density
`m'` on `A Q` with charges `A Y`. -/
theorem isNeumannChargeField_simField (hσ : 0 < σ) {Q : Set ℂ} (hQ : MeasurableSet Q) {m' : ℝ}
    {Y : Finset ℂ} {E : ℂ → ℂ} (hE : IsNeumannChargeField Q (σ ^ 2 * m') Y E) :
    IsNeumannChargeField (simMap σ L c '' Q) m' (Y.image (simMap σ L c)) (simField σ L c E) := by
  classical
  refine ⟨?_, fun φ hφ hc => ?_⟩
  · rw [integrableOn_image_simMap_iff hσ hQ]
    have : (fun y => simField σ L c E (simMap σ L c y)) = fun y => σ⁻¹ • L (E y) := by
      ext y; simp [simField, simInv_simMap hσ.ne']
    rw [this]
    exact (L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hE.1).smul σ⁻¹
  · have hψ : ContDiff ℝ ∞ (fun y => φ (simMap σ L c y)) := hφ.comp contDiff_simMap
    have hψc : HasCompactSupport (fun y => φ (simMap σ L c y)) :=
      hc.comp_homeomorph (simHomeomorph hσ.ne' L c)
    have h := hE.2 _ hψ hψc
    rw [setIntegral_image_simMap hσ hQ, setIntegral_image_simMap hσ hQ]
    simp only [inner_simField_gradient hσ]
    rw [integral_const_mul, h, Finset.sum_image fun y _ z _ h => simMap_injective hσ.ne' h]
    field_simp

/-! ### Truncated fields -/

theorem truncLog_simLin (hσ : 0 < σ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) :
    truncLog (σ * r) (L (σ • z)) = truncLog r z := by
  unfold truncLog
  rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hσ,
    Real.log_mul hσ.ne' (norm_ne_zero_iff.2 hz), Real.log_mul hσ.ne' hr.ne']
  ring_nf

/-- Off the centre, `∇f_{σr}(σ L z) = σ⁻¹ L ∇f_r(z)`. -/
theorem gradient_truncLog_simLin (hσ : 0 < σ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) :
    gradient (truncLog (σ * r)) (L (σ • z)) = σ⁻¹ • L (gradient (truncLog r) z) := by
  have h := gradient_comp_simMap (L := L) (c := 0) hσ.ne' (truncLog (σ * r)) z
  have hev : (fun y => truncLog (σ * r) (simMap σ L 0 y)) =ᶠ[𝓝 z] truncLog r := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    simp only [simMap, add_zero]
    exact truncLog_simLin hσ hr hy
  rw [Screening.gradient_congr_nhds hev] at h
  have hs : simMap σ L 0 z = L (σ • z) := add_zero _
  rw [hs] at h
  rw [h, L.map_smul σ (L.symm (gradient (truncLog (σ * r)) (L (σ • z)))), L.apply_symm_apply,
    smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]

/-- **Transport of truncated fields**: off the charges,
`(E_A)_{σ ρ ∘ A⁻¹}(A y) = σ⁻¹ L E_ρ(y)`. -/
theorem truncField_simField (hσ : 0 < σ) (C : Finset ℂ) {ρ : ℂ → ℝ} (hρ : ∀ p ∈ C, 0 < ρ p)
    (E : ℂ → ℂ) {y : ℂ} (hy : y ∉ C) :
    truncField (↑(C.image (simMap σ L c))) (fun x => σ * ρ (simInv σ L c x)) (simField σ L c E)
        (simMap σ L c y) =
      σ⁻¹ • L (truncField (↑C) ρ E y) := by
  classical
  unfold truncField
  rw [finsum_mem_coe_finset, finsum_mem_coe_finset,
    Finset.sum_image fun y _ z _ h => simMap_injective hσ.ne' h, simField, simInv_simMap hσ.ne',
    map_sub, smul_sub, map_sum, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  beta_reduce
  rw [simInv_simMap hσ.ne', simMap_sub]
  have hyp : y - p ≠ 0 := sub_ne_zero.2 fun h => hy (h ▸ hp)
  exact gradient_truncLog_simLin hσ (hρ p hp) hyp

theorem norm_truncField_simField (hσ : 0 < σ) (C : Finset ℂ) {ρ : ℂ → ℝ} (hρ : ∀ p ∈ C, 0 < ρ p)
    (E : ℂ → ℂ) {y : ℂ} (hy : y ∉ C) :
    ‖truncField (↑(C.image (simMap σ L c))) (fun x => σ * ρ (simInv σ L c x)) (simField σ L c E)
        (simMap σ L c y)‖ ^ 2 =
      (σ ^ 2)⁻¹ * ‖truncField (↑C) ρ E y‖ ^ 2 := by
  rw [truncField_simField hσ C hρ E hy, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hσ)]
  ring

end Bridge

end Sphere

end SandierSerfaty

end
