/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.Kernel
public import SandierSerfaty.Analysis.Weyl
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Regularity of admissible fields

**Theorem** (`IsAdmissibleField.exists_local_form`; the comparison note's Lemma `lem:regularity`, paper Lemma
`red:local`). Let `E ∈ 𝒜₁` (`IsAdmissibleField Λ E`) and `R : ℝ`, and let `S` be the finite set
`Λ ∩ B̄(0, R)`. Then there is `F`, smooth on `B(0, R)`, with
`E(x) = ∑_{p ∈ S} κ(x - p) + F(x)` for almost every `x ∈ B(0, R)`, where `κ(y) = y / ‖y‖²`.

## Proof

The field `E⁰ = ∑_{p ∈ S} κ(· - p) - π x` satisfies `div E⁰ = 2π(∑_{p ∈ S} δ_p - 1)` and `curl E⁰ = 0`
weakly (`Whole.Kernel`), and the charges of `Λ` outside `B̄(0, R)` do not see test functions supported in
`B(0, R)`. So `V = E - E⁰` is weakly divergence- and curl-free in `B(0, R)`; then
`Re V` and `Im V` are weakly harmonic there (`Δ = ∂₁ div - ∂₂ curl`, resp. `∂₂ div + ∂₁ curl`), and Weyl's
lemma makes them smooth.
-/

open MeasureTheory Filter Topology Metric InnerProductSpace Set Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Whole

/-- The singular part of a field with charges `S` and neutralizing background `1`:
`E⁰(x) = ∑_{p ∈ S} κ(x - p) - π x` (paper sign: `div E⁰ = 2π(∑ δ_p - 1)`). -/
@[expose] noncomputable def singularField (S : Finset ℂ) (x : ℂ) : ℂ :=
  ∑ p ∈ S, kernel (x - p) - Real.pi • x

theorem locallyIntegrable_singularField (S : Finset ℂ) :
    LocallyIntegrable (singularField S) volume := by
  have h1 : LocallyIntegrable (fun x => ∑ p ∈ S, kernel (x - p)) volume :=
    locallyIntegrable_finsetSum S fun p _ => locallyIntegrable_kernel_sub p
  have h2 : LocallyIntegrable (fun x : ℂ => Real.pi • x) volume :=
    (by fun_prop : Continuous fun x : ℂ => Real.pi • x).locallyIntegrable
  exact h1.sub h2

theorem integral_inner_singularField_gradient (S : Finset ℂ) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ∫ x, inner ℝ (singularField S x) (gradient φ x) =
      -(2 * Real.pi * ((∑ p ∈ S, φ p) - ∫ x, φ x)) := by
  have hG := Torus.continuous_gradient hφ
  have hGc := Torus.hasCompactSupport_gradient hc
  have hk : ∀ p, Integrable fun x => inner ℝ (kernel (x - p)) (gradient φ x) := fun p =>
    integrable_inner_of_locallyIntegrable (locallyIntegrable_kernel_sub p) hG hGc
  have hl : Integrable fun x : ℂ => inner ℝ (x - 0) (gradient φ x) :=
    integrable_inner_of_locallyIntegrable (continuous_id.sub continuous_const).locallyIntegrable hG hGc
  have hpt : ∀ x, inner ℝ (singularField S x) (gradient φ x) =
      ∑ p ∈ S, inner ℝ (kernel (x - p)) (gradient φ x) -
        Real.pi * inner ℝ (x - 0) (gradient φ x) := by
    intro x
    rw [singularField, inner_sub_left, sum_inner, real_inner_smul_left, sub_zero]
  simp_rw [hpt]
  rw [integral_sub (integrable_finsetSum S fun p _ => hk p) (hl.const_mul _),
    integral_finsetSum S fun p _ => hk p, integral_const_mul,
    integral_inner_sub_gradient hφ hc 0,
    Finset.sum_congr rfl fun p _ => integral_inner_kernel_gradient hφ hc p,
    Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

theorem integral_inner_singularField_I_gradient (S : Finset ℂ) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    ∫ x, inner ℝ (singularField S x) (Complex.I * gradient φ x) = 0 := by
  have hG := continuous_I_mul_gradient hφ
  have hGc := hasCompactSupport_I_mul_gradient hc
  have hk : ∀ p, Integrable fun x => inner ℝ (kernel (x - p)) (Complex.I * gradient φ x) := fun p =>
    integrable_inner_of_locallyIntegrable (locallyIntegrable_kernel_sub p) hG hGc
  have hl : Integrable fun x : ℂ => inner ℝ (x - 0) (Complex.I * gradient φ x) :=
    integrable_inner_of_locallyIntegrable (continuous_id.sub continuous_const).locallyIntegrable hG hGc
  have hpt : ∀ x, inner ℝ (singularField S x) (Complex.I * gradient φ x) =
      ∑ p ∈ S, inner ℝ (kernel (x - p)) (Complex.I * gradient φ x) -
        Real.pi * inner ℝ (x - 0) (Complex.I * gradient φ x) := by
    intro x
    rw [singularField, inner_sub_left, sum_inner, real_inner_smul_left, sub_zero]
  simp_rw [hpt]
  rw [integral_sub (integrable_finsetSum S fun p _ => hk p) (hl.const_mul _),
    integral_finsetSum S fun p _ => hk p, integral_const_mul,
    integral_inner_sub_I_gradient hφ hc 0,
    Finset.sum_congr rfl fun p _ => integral_inner_kernel_I_gradient hφ hc p]
  simp

/-! ### Divergence- and curl-free fields have harmonic components -/

theorem pd_pd_comm {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (x : ℂ) :
    Weyl.pd Complex.I (Weyl.pd 1 ψ) x = Weyl.pd 1 (Weyl.pd Complex.I ψ) x := by
  have h2 : ContDiffAt ℝ 2 ψ x := (hψ.of_le (by norm_cast)).contDiffAt
  have hs := ContDiffAt.isSymmSndFDerivAt h2 (by simp)
  show fderiv ℝ (fun y => fderiv ℝ ψ y 1) x Complex.I =
    fderiv ℝ (fun y => fderiv ℝ ψ y Complex.I) x 1
  rw [Analysis.fderiv_fderiv_apply h2, Analysis.fderiv_fderiv_apply h2]
  exact hs Complex.I 1

theorem gradient_re_eq_pd (g : ℂ → ℝ) (x : ℂ) : (gradient g x).re = Weyl.pd 1 g x :=
  Analysis.gradient_re g x

theorem gradient_im_eq_pd (g : ℂ → ℝ) (x : ℂ) : (gradient g x).im = Weyl.pd Complex.I g x :=
  Analysis.gradient_im g x

theorem inner_eq_re_im (V w : ℂ) : inner ℝ V w = V.re * w.re + V.im * w.im := by
  simp [Complex.inner, Complex.mul_re]
  ring

theorem inner_I_mul_eq_re_im (V w : ℂ) :
    inner ℝ V (Complex.I * w) = -(V.re * w.im) + V.im * w.re := by
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

theorem contDiff_pd_infty {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (v : ℂ) :
    ContDiff ℝ ∞ (Weyl.pd v ψ) :=
  Weyl.contDiff_pd hψ (by exact_mod_cast le_rfl) v

theorem tsupport_pd_subset (ψ : ℂ → ℝ) (v : ℂ) : tsupport (Weyl.pd v ψ) ⊆ tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ v

theorem hasCompactSupport_pd {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) (v : ℂ) :
    HasCompactSupport (Weyl.pd v ψ) :=
  hc.fderiv_apply (𝕜 := ℝ) v

/-- A locally integrable field that is weakly divergence- and curl-free in `U` has weakly harmonic real and
imaginary parts in `U`. -/
theorem isWeaklyHarmonicOn_re_im {U : Set ℂ} {V : ℂ → ℂ} (hV : LocallyIntegrable V volume)
    (hdiv : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, inner ℝ (V x) (gradient φ x) = 0)
    (hcurl : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, inner ℝ (V x) (Complex.I * gradient φ x) = 0) :
    Weyl.IsWeaklyHarmonicOn U (fun x => (V x).re) ∧ Weyl.IsWeaklyHarmonicOn U (fun x => (V x).im) := by
  have hint : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      Integrable (fun x => inner ℝ (V x) (gradient g x)) ∧
        Integrable (fun x => inner ℝ (V x) (Complex.I * gradient g x)) := fun g hg hgc =>
    ⟨integrable_inner_of_locallyIntegrable hV (Torus.continuous_gradient (hg.of_le (by simp)))
        (Torus.hasCompactSupport_gradient hgc),
      integrable_inner_of_locallyIntegrable hV (continuous_I_mul_gradient (hg.of_le (by simp)))
        (hasCompactSupport_I_mul_gradient hgc)⟩
  have hlap : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → ∀ x,
      Δ ψ x = Weyl.pd 1 (Weyl.pd 1 ψ) x + Weyl.pd Complex.I (Weyl.pd Complex.I ψ) x :=
    fun ψ hψ x => Weyl.lap_eq_pd (hψ.of_le (by norm_cast)).contDiffAt
  constructor
  · intro ψ hψ hc hs
    rw [Weyl.setIntegral_mul_lap_eq_integral _ hs]
    have h1 := hint _ (contDiff_pd_infty hψ 1) (hasCompactSupport_pd hc 1)
    have h2 := hint _ (contDiff_pd_infty hψ Complex.I) (hasCompactSupport_pd hc Complex.I)
    have hpt : ∀ x, (V x).re * Δ ψ x = inner ℝ (V x) (gradient (Weyl.pd 1 ψ) x) -
        inner ℝ (V x) (Complex.I * gradient (Weyl.pd Complex.I ψ) x) := by
      intro x
      rw [inner_eq_re_im, inner_I_mul_eq_re_im, gradient_re_eq_pd, gradient_im_eq_pd,
        gradient_re_eq_pd, gradient_im_eq_pd, hlap ψ hψ x, pd_pd_comm hψ x]
      ring
    simp_rw [hpt]
    rw [integral_sub h1.1 h2.2,
      hdiv _ (contDiff_pd_infty hψ 1) (hasCompactSupport_pd hc 1) ((tsupport_pd_subset ψ 1).trans hs),
      hcurl _ (contDiff_pd_infty hψ Complex.I) (hasCompactSupport_pd hc Complex.I)
        ((tsupport_pd_subset ψ Complex.I).trans hs), sub_zero]
  · intro ψ hψ hc hs
    rw [Weyl.setIntegral_mul_lap_eq_integral _ hs]
    have h1 := hint _ (contDiff_pd_infty hψ 1) (hasCompactSupport_pd hc 1)
    have h2 := hint _ (contDiff_pd_infty hψ Complex.I) (hasCompactSupport_pd hc Complex.I)
    have hpt : ∀ x, (V x).im * Δ ψ x = inner ℝ (V x) (gradient (Weyl.pd Complex.I ψ) x) +
        inner ℝ (V x) (Complex.I * gradient (Weyl.pd 1 ψ) x) := by
      intro x
      rw [inner_eq_re_im, inner_I_mul_eq_re_im, gradient_re_eq_pd, gradient_im_eq_pd,
        gradient_re_eq_pd, gradient_im_eq_pd, hlap ψ hψ x, pd_pd_comm hψ x]
      ring
    simp_rw [hpt]
    rw [integral_add h2.1 h1.2,
      hdiv _ (contDiff_pd_infty hψ Complex.I) (hasCompactSupport_pd hc Complex.I)
        ((tsupport_pd_subset ψ Complex.I).trans hs),
      hcurl _ (contDiff_pd_infty hψ 1) (hasCompactSupport_pd hc 1) ((tsupport_pd_subset ψ 1).trans hs),
      add_zero]

/-! ### The local form -/

/-- A finite sum over `Λ` of a function vanishing off `B(0, R)` is the sum over `Λ ∩ B̄(0, R)`. -/
theorem finsum_mem_eq_sum_toFinset {Λ : Set ℂ} {R : ℝ} (h : (Λ ∩ closedBall 0 R).Finite)
    {g : ℂ → ℝ} (hg : ∀ p, R < ‖p‖ → g p = 0) :
    ∑ᶠ p ∈ Λ, g p = ∑ p ∈ h.toFinset, g p := by
  rw [← finsum_mem_coe_finset]
  apply finsum_mem_inter_support_eq
  ext p
  simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe, Set.Finite.mem_toFinset,
    mem_closedBall_zero_iff]
  constructor
  · rintro ⟨hpΛ, hp⟩
    exact ⟨⟨hpΛ, not_lt.1 fun h' => hp (hg p h')⟩, hp⟩
  · rintro ⟨⟨hpΛ, _⟩, hp⟩
    exact ⟨hpΛ, hp⟩

theorem eq_zero_of_tsupport_subset_ball {φ : ℂ → ℝ} {R : ℝ} (hs : tsupport φ ⊆ ball 0 R) {p : ℂ}
    (hp : R < ‖p‖) : φ p = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => by
    have := hs h
    rw [mem_ball_zero_iff] at this
    linarith

/-- **Regularity of admissible fields** (comparison note, Lemma `lem:regularity`): on `B(0, R)`, `E` is a.e. the sum of
the kernels of the charges in `B̄(0, R)` and a smooth field. -/
theorem IsAdmissibleField.exists_local_form {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E)
    (R : ℝ) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ ∞ F (ball 0 R) ∧
      ∀ᵐ x ∂(volume.restrict (ball 0 R)), E x = ∑ p ∈ (hE.1 R).toFinset, kernel (x - p) + F x := by
  have hEloc := hE.2.1
  have hEdiv := hE.2.2.1
  have hEcurl := hE.2.2.2.1
  set S := (hE.1 R).toFinset with hS
  set V : ℂ → ℂ := fun x => E x - singularField S x with hV
  have hVloc : LocallyIntegrable V volume := hEloc.sub (locallyIntegrable_singularField S)
  have hdiv : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      ∫ x, inner ℝ (V x) (gradient φ x) = 0 := by
    intro φ hφ hc hs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hG := Torus.continuous_gradient hφ1
    have hGc := Torus.hasCompactSupport_gradient hc
    have h1 := integrable_inner_of_locallyIntegrable hEloc hG hGc
    have h2 := integrable_inner_of_locallyIntegrable (locallyIntegrable_singularField S) hG hGc
    simp_rw [hV, inner_sub_left]
    rw [integral_sub h1 h2, hEdiv φ hφ hc, integral_inner_singularField_gradient S hφ1 hc,
      finsum_mem_eq_sum_toFinset (hE.1 R) fun p hp => eq_zero_of_tsupport_subset_ball hs hp]
    ring
  have hcurl : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      ∫ x, inner ℝ (V x) (Complex.I * gradient φ x) = 0 := by
    intro φ hφ hc _
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hG := continuous_I_mul_gradient hφ1
    have hGc := hasCompactSupport_I_mul_gradient hc
    have h1 := integrable_inner_of_locallyIntegrable hEloc hG hGc
    have h2 := integrable_inner_of_locallyIntegrable (locallyIntegrable_singularField S) hG hGc
    simp_rw [hV, inner_sub_left]
    rw [integral_sub h1 h2, hEcurl φ hφ hc, integral_inner_singularField_I_gradient S hφ1 hc, sub_zero]
  obtain ⟨hre, him⟩ := isWeaklyHarmonicOn_re_im hVloc hdiv hcurl
  have hre_loc : LocallyIntegrableOn (fun x => (V x).re) (ball 0 R) volume := by
    refine LocallyIntegrable.locallyIntegrableOn (fun x => ?_) _
    obtain ⟨s, hs, hint⟩ := hVloc x
    exact ⟨s, hs, hint.re⟩
  have him_loc : LocallyIntegrableOn (fun x => (V x).im) (ball 0 R) volume := by
    refine LocallyIntegrable.locallyIntegrableOn (fun x => ?_) _
    obtain ⟨s, hs, hint⟩ := hVloc x
    exact ⟨s, hs, hint.im⟩
  obtain ⟨v₁, hv₁, hv₁ae, -⟩ := Weyl.weyl_lemma isOpen_ball hre_loc hre
  obtain ⟨v₂, hv₂, hv₂ae, -⟩ := Weyl.weyl_lemma isOpen_ball him_loc him
  refine ⟨fun x => (v₁ x : ℂ) + (v₂ x : ℂ) * Complex.I - Real.pi • x, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun x => (v₁ x : ℂ)) (ball 0 R) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hv₁
    have h2 : ContDiffOn ℝ ∞ (fun x => (v₂ x : ℂ)) (ball 0 R) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hv₂
    exact (h1.add (h2.mul contDiffOn_const)).sub (contDiff_id.const_smul Real.pi).contDiffOn
  · filter_upwards [hv₁ae, hv₂ae] with x h1 h2
    have hEV : E x = singularField S x + V x := by simp [hV]
    rw [hEV, singularField]
    apply Complex.ext <;> simp [h1, h2] <;> ring

end Whole

end SandierSerfaty

end
