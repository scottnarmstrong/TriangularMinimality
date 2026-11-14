/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.ChartPotential
public import SandierSerfaty.Torus.PotentialLocal
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.RingTheory.Complex
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Conformal invariance of the Dirichlet integral under the inversion `ι(x) = 1 / x̄`

(Input A7 of the sphere note: conformal change of variables for the Dirichlet integral, in the case needed
for the two-chart decomposition.)

* `Sphere.hasFDerivAt_invC`: `Dι(z) h = -(z̄²)⁻¹ h̄`;
* `Sphere.abs_det_invDeriv`: `|det Dι(z)| = ‖z‖⁻⁴`;
* `Sphere.norm_comp_invDeriv`: `‖L ∘ Dι(z)‖ = ‖z‖⁻² ‖L‖`;
* `Sphere.integral_gradSq_image_invC`: `∫_{ι(S)} |∇f|² = ∫_S |∇(f ∘ ι)|²` for measurable `S ⊆ ℂ ∖ {0}`.
-/

open MeasureTheory Set Filter Topology Laplacian Metric

public section

namespace SandierSerfaty

namespace Sphere

theorem norm_invC (x : ℂ) : ‖invC x‖ = ‖x‖⁻¹ := by simp [invC]

theorem injOn_invC (S : Set ℂ) : InjOn invC S := fun x _ y _ h => by
  have := congrArg invC h
  rwa [invC_invC, invC_invC] at this

/-- The derivative of the inversion. -/
@[expose] noncomputable def invDeriv (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (-((starRingEnd ℂ z) ^ 2)⁻¹) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem invDeriv_apply (z h : ℂ) :
    invDeriv z h = -((starRingEnd ℂ z) ^ 2)⁻¹ * starRingEnd ℂ h := by
  simp [invDeriv]

theorem hasFDerivAt_invC {z : ℂ} (hz : z ≠ 0) : HasFDerivAt invC (invDeriv z) z := by
  have hz' : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h1 := (hasDerivAt_inv hz').hasFDerivAt.restrictScalars ℝ
  have h2 := h1.comp z (Complex.conjCLE.hasFDerivAt (x := z))
  have e : invC = (fun y : ℂ => y⁻¹) ∘ (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    funext x; simp [invC]
  have e2 : invDeriv z = (ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ (-((starRingEnd ℂ) z ^ 2)⁻¹))).comp
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
    ContinuousLinearMap.ext fun h => by simp [invDeriv_apply, mul_comm]
  rw [e, e2]
  exact h2

theorem norm_invDeriv_apply (z h : ℂ) : ‖invDeriv z h‖ = (‖z‖ ^ 2)⁻¹ * ‖h‖ := by
  rw [invDeriv_apply]
  simp [norm_neg, norm_inv, norm_pow]

theorem surjective_invDeriv {z : ℂ} (hz : z ≠ 0) : Function.Surjective (invDeriv z) := by
  intro y
  have hz' : starRingEnd ℂ z ≠ 0 := by simpa using hz
  refine ⟨starRingEnd ℂ (y / (-((starRingEnd ℂ z) ^ 2)⁻¹)), ?_⟩
  rw [invDeriv_apply, Complex.conj_conj]
  field_simp

theorem abs_det_invDeriv {z : ℂ} : |(invDeriv z).det| = ((‖z‖ ^ 2)⁻¹) ^ 2 := by
  set w : ℂ := -((starRingEnd ℂ z) ^ 2)⁻¹ with hw
  have hlin : (invDeriv z : ℂ →ₗ[ℝ] ℂ) =
      (Algebra.lmul ℝ ℂ w).comp (Complex.conjAe.toLinearMap) := by
    ext h
    simp [invDeriv_apply, hw]
  have : (invDeriv z).det = - Complex.normSq w := by
    rw [ContinuousLinearMap.det, hlin, LinearMap.det_comp]
    have h1 : LinearMap.det (Algebra.lmul ℝ ℂ w) = Complex.normSq w := by
      rw [← Algebra.norm_apply, Algebra.norm_complex_apply]
    rw [h1, Complex.det_conjAe]
    ring
  rw [this, abs_neg, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, hw]
  simp [norm_neg, norm_inv, norm_pow]

theorem norm_comp_invDeriv {z : ℂ} (hz : z ≠ 0) (L : ℂ →L[ℝ] ℝ) :
    ‖L.comp (invDeriv z)‖ = (‖z‖ ^ 2)⁻¹ * ‖L‖ := by
  have hk : 0 < (‖z‖ ^ 2)⁻¹ := by
    have : 0 < ‖z‖ := norm_pos_iff.2 hz
    positivity
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    simp only [ContinuousLinearMap.comp_apply]
    calc ‖L (invDeriv z h)‖ ≤ ‖L‖ * ‖invDeriv z h‖ := L.le_opNorm _
      _ = (‖z‖ ^ 2)⁻¹ * ‖L‖ * ‖h‖ := by rw [norm_invDeriv_apply]; ring
  · have : ‖L‖ ≤ ‖L.comp (invDeriv z)‖ / (‖z‖ ^ 2)⁻¹ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      obtain ⟨h, rfl⟩ := surjective_invDeriv hz v
      have h1 : ‖L.comp (invDeriv z) h‖ ≤ ‖L.comp (invDeriv z)‖ * ‖h‖ := (L.comp (invDeriv z)).le_opNorm h
      have h2 : ‖invDeriv z h‖ = (‖z‖ ^ 2)⁻¹ * ‖h‖ := norm_invDeriv_apply z h
      rw [h2, div_mul_eq_mul_div, le_div_iff₀ hk]
      simp only [ContinuousLinearMap.comp_apply] at h1
      nlinarith
    rw [le_div_iff₀ hk] at this
    linarith

/-- **Conformal invariance of the Dirichlet integral under the inversion.** -/
theorem integral_gradSq_image_invC {S : Set ℂ} (hS : MeasurableSet S) (h0 : (0 : ℂ) ∉ S)
    (f : ℂ → ℝ) (hf : ∀ z ∈ S, DifferentiableAt ℝ f (invC z)) :
    ∫ y in invC '' S, ‖gradient f y‖ ^ 2 = ∫ z in S, ‖gradient (f ∘ invC) z‖ ^ 2 := by
  have hne : ∀ z ∈ S, z ≠ 0 := fun z hz h => h0 (h ▸ hz)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hS
    (fun z hz => (hasFDerivAt_invC (hne z hz)).hasFDerivWithinAt) (injOn_invC S)
    (fun y => ‖gradient f y‖ ^ 2)]
  refine setIntegral_congr_fun hS fun z hz => ?_
  have hd : HasFDerivAt (f ∘ invC) ((fderiv ℝ f (invC z)).comp (invDeriv z)) z :=
    (hf z hz).hasFDerivAt.comp z (hasFDerivAt_invC (hne z hz))
  simp only [smul_eq_mul]
  rw [Torus.norm_gradient_eq, Torus.norm_gradient_eq, hd.fderiv, norm_comp_invDeriv (hne z hz),
    abs_det_invDeriv]
  ring

end Sphere

end SandierSerfaty

end
