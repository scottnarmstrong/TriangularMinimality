/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TriangularCell
public import SandierSerfaty.Analysis.PolarMean
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Real-valued cell computations for the one-point torus potential

With `η = ¼`, `ann ε = {ε ≤ ‖y‖ < η}` and `V ρ = ∫_{B(0,ρ)} ‖∇v‖²`:

* `exists_bound_gradient_far`: `‖∇h‖` is bounded on `{x | ∀ γ ∈ Γ, ε ≤ ‖x - γ‖}`;
* `integral_gradient_ann`: `∫_{ann ε} ‖∇h‖² = V η - V ε - 2π²(η² - ε²) + 2π log (η/ε)`
  (polar coordinates, `‖∇h‖² = ‖∇v‖² - 2‖x‖⁻² ∂v[x] + ‖x‖⁻²` and the mean value property);
* `volumeBound_V`: `0 ≤ V ρ ≤ C ρ²`.
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Torus

section Bounds

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ]

/-- The gradient of a torus potential of the charge at `0` is bounded away from the lattice. -/
theorem exists_bound_gradient_far {h : ℂ → ℝ} (hP : IsTorusPotential Γ zeroCharge h) {F : Set ℂ}
    (hFb : Bornology.IsBounded F) (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ x ∈ farSet Γ ε, ‖gradient h x‖ ≤ M := by
  have hK : IsCompact (closure F ∩ farSet Γ ε) :=
    hFb.isCompact_closure.inter_right (isClosed_farSet Γ ε)
  have hopen := isOpen_notMem_chargeSet Γ zeroCharge
  have hcont : ContinuousOn (gradient h) {x : ℂ | ∀ i, x - zeroCharge i ∉ Γ} :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn
      (hP.2.1.continuousOn_fderiv_of_isOpen hopen (by simp))
  have hsub : closure F ∩ farSet Γ ε ⊆ {x : ℂ | ∀ i, x - zeroCharge i ∉ Γ} := by
    intro y hy i hyΓ
    have := hy.2 (y - zeroCharge i) hyΓ
    simp [zeroCharge] at this
    linarith
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨M, fun x hx => ?_⟩
  obtain ⟨γ, hγ, hxF⟩ := hcov x
  have hy : x - γ ∈ closure F ∩ farSet Γ ε := by
    refine ⟨subset_closure hxF, ?_⟩
    exact (farSet_add_periodic (ε := ε) (x := x - γ) hγ).1 (by rwa [sub_add_cancel])
  have e : gradient h x = gradient h (x - γ) := by
    have := gradient_add_periodic hP.1 hγ (x - γ)
    rwa [sub_add_cancel] at this
  rw [e]
  exact hM _ hy

end Bounds

section Annulus

/-- `V ρ = ∫_{B(0,ρ)} ‖∇v‖²`. -/
@[expose] noncomputable def Vint (v : ℂ → ℝ) (ρ : ℝ) : ℝ := ∫ y in ball (0 : ℂ) ρ, ‖gradient v y‖ ^ 2

theorem continuousOn_gradient {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v (ball 0 1)) :
    ContinuousOn (gradient v) (ball 0 1) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn
    (hv.continuousOn_fderiv_of_isOpen isOpen_ball (by simp))

theorem closedBall_quarter_subset : closedBall (0 : ℂ) (1 / 4) ⊆ ball 0 1 :=
  closedBall_subset_ball (by norm_num)

theorem integrableOn_ann {g : ℂ → ℝ} {ε : ℝ}
    (hg : ContinuousOn g (closedBall 0 (1 / 4) \ ball 0 ε)) :
    IntegrableOn g {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4} := by
  have hK : IsCompact (closedBall (0 : ℂ) (1 / 4) \ ball 0 ε) :=
    (isCompact_closedBall _ _).diff isOpen_ball
  refine (hg.integrableOn_compact hK).mono_set ?_
  intro y hy
  exact ⟨mem_closedBall_zero_iff.2 hy.2.le, fun hh => by
    have := mem_ball_zero_iff.1 hh; linarith [hy.1]⟩

theorem ann_eq_sdiff (ε : ℝ) :
    {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4} = ball (0 : ℂ) (1 / 4) \ ball 0 ε := by
  ext y
  simp only [mem_ofPred_eq, Set.mem_sdiff, mem_ball_zero_iff, not_lt]
  tauto

theorem measurableSet_ann (ε : ℝ) : MeasurableSet {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4} :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- **The annulus integral of `‖∇h‖²`.** -/
theorem integral_gradient_ann {h v : ℂ → ℝ} (hv : IsLocalPart h v) {ε : ℝ} (hε : 0 < ε)
    (hεη : ε < 1 / 4) :
    (IntegrableOn (fun y => ‖gradient h y‖ ^ 2) {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4}) ∧
    ∫ y in {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4}, ‖gradient h y‖ ^ 2 =
      Vint v (1 / 4) - Vint v ε - 2 * (Real.pi ^ 2 * ((1 / 4) ^ 2 - ε ^ 2)) +
        2 * Real.pi * Real.log ((1 / 4) / ε) := by
  set A : Set ℂ := {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4} with hA
  have hAm : MeasurableSet A := measurableSet_ann ε
  have hKball : closedBall (0 : ℂ) (1 / 4) \ ball 0 ε ⊆ ball 0 1 :=
    sdiff_subset.trans closedBall_quarter_subset
  have hKne : ∀ y ∈ closedBall (0 : ℂ) (1 / 4) \ ball 0 ε, y ≠ 0 := by
    intro y hy hy0
    apply hy.2
    rw [hy0]; exact mem_ball_self hε
  have hKn : ∀ y ∈ closedBall (0 : ℂ) (1 / 4) \ ball 0 ε, ‖y‖ ^ 2 ≠ 0 := fun y hy =>
    pow_ne_zero 2 (norm_ne_zero_iff.2 (hKne y hy))
  have hAball : ∀ y ∈ A, y ∈ ball (0 : ℂ) 1 := fun y hy => by
    rw [mem_ball_zero_iff]; linarith [hy.2]
  have hAne : ∀ y ∈ A, y ≠ 0 := fun y hy hy0 => by
    have := hy.1
    rw [hy0, norm_zero] at this; linarith
  have c1 : ContinuousOn (fun y : ℂ => ‖gradient v y‖ ^ 2)
      (closedBall 0 (1 / 4) \ ball 0 ε) :=
    ((continuousOn_gradient hv.1).mono hKball).norm.pow 2
  have hcontfd : ContinuousOn (fun x => fderiv ℝ v x) (ball 0 1) :=
    hv.1.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have c3 : ContinuousOn (fun y : ℂ => (‖y‖ ^ 2)⁻¹) (closedBall 0 (1 / 4) \ ball 0 ε) :=
    (continuous_norm.pow 2).continuousOn.inv₀ hKn
  have c2 : ContinuousOn (fun y : ℂ => (‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y)
      (closedBall 0 (1 / 4) \ ball 0 ε) :=
    c3.mul ((hcontfd.mono hKball).clm_apply continuousOn_id)
  have i1 := integrableOn_ann c1
  have i2 := integrableOn_ann c2
  have i3 := integrableOn_ann c3
  have hcongr : ∀ y ∈ A, ‖gradient h y‖ ^ 2 =
      ‖gradient v y‖ ^ 2 - 2 * ((‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y) + (‖y‖ ^ 2)⁻¹ := fun y hy =>
    norm_sq_gradient_eq hv.1 hv.2.2 (hAball y hy) (hAne y hy)
  have i2' : IntegrableOn (fun y : ℂ => 2 * ((‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y)) A := i2.const_mul 2
  have i12 : IntegrableOn (fun y : ℂ => ‖gradient v y‖ ^ 2 - 2 * ((‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y)) A :=
    i1.sub i2'
  have hint : IntegrableOn (fun y : ℂ => ‖gradient v y‖ ^ 2 - 2 * ((‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y) +
      (‖y‖ ^ 2)⁻¹) A := i12.add i3
  refine ⟨hint.congr_fun (fun y hy => (hcongr y hy).symm) hAm, ?_⟩
  rw [setIntegral_congr_fun hAm hcongr, integral_add i12 i3,
    integral_sub i1 i2', integral_const_mul, hA,
    integral_fderiv_div_sq_annulus_eq hv.1 hv.2.1 hε hεη (by norm_num : (1 / 4 : ℝ) < 1),
    integral_inv_sq_annulus hε hεη, ann_eq_sdiff,
    setIntegral_sdiff measurableSet_ball ?_ (ball_subset_ball hεη.le)]
  · simp only [Vint]
  · exact (((continuousOn_gradient hv.1).mono closedBall_quarter_subset).norm.pow 2
      |>.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall

theorem volume_real_ball_zero {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real (ball (0 : ℂ) ρ) = Real.pi * ρ ^ 2 := by
  rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hρ]
  simp [mul_comm]

theorem Vint_nonneg (v : ℂ → ℝ) (ρ : ℝ) : 0 ≤ Vint v ρ :=
  setIntegral_nonneg measurableSet_ball (fun _ _ => by positivity)

theorem exists_Vint_le {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v (ball 0 1)) :
    ∃ C : ℝ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 → Vint v ρ ≤ C * ρ ^ 2 := by
  have c1 : ContinuousOn (fun y : ℂ => ‖gradient v y‖ ^ 2) (closedBall 0 (1 / 4)) :=
    ((continuousOn_gradient hv).mono closedBall_quarter_subset).norm.pow 2
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 4)).exists_bound_of_continuousOn c1
  refine ⟨M * Real.pi, fun ρ hρ hρ4 => ?_⟩
  have hsub : ball (0 : ℂ) ρ ⊆ closedBall 0 (1 / 4) :=
    (ball_subset_closedBall).trans (closedBall_subset_closedBall hρ4)
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := ball (0 : ℂ) ρ)
    (f := fun y : ℂ => ‖gradient v y‖ ^ 2) (C := M) measure_ball_lt_top
    (fun y hy => hM y (hsub hy))
  rw [volume_real_ball_zero hρ.le] at this
  calc Vint v ρ ≤ ‖Vint v ρ‖ := le_abs_self _
    _ ≤ M * (Real.pi * ρ ^ 2) := this
    _ = M * Real.pi * ρ ^ 2 := by ring

/-- **The far part of the cell integral is finite.** -/
theorem lintegral_far_ne_top {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {h : ℂ → ℝ}
    (hP : IsTorusPotential Γ zeroCharge h) {F : Set ℂ} (hFb : Bornology.IsBounded F)
    (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x in F, (farSet Γ ε).indicator (cellGradSq h) x ≠ ⊤ := by
  obtain ⟨M, hM⟩ := exists_bound_gradient_far hP hFb hcov hε
  have hle : ∀ x, (farSet Γ ε).indicator (cellGradSq h) x ≤ ENNReal.ofReal (M ^ 2) := by
    intro x
    by_cases hx : x ∈ farSet Γ ε
    · rw [indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have h0 := norm_nonneg (gradient h x)
      have h1 := hM x hx
      nlinarith
    · rw [indicator_of_notMem hx]; exact bot_le
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFb.measure_lt_top.ne

/-- The annulus integral of `‖∇h‖²`, as a lower integral. -/
theorem lintegral_gradSq_ann {h v : ℂ → ℝ} (hv : IsLocalPart h v) {ε : ℝ} (hε : 0 < ε)
    (hεη : ε < 1 / 4) :
    ∫⁻ y in {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 1 / 4}, cellGradSq h y =
      ENNReal.ofReal (Vint v (1 / 4) - Vint v ε - 2 * (Real.pi ^ 2 * ((1 / 4) ^ 2 - ε ^ 2)) +
        2 * Real.pi * Real.log ((1 / 4) / ε)) := by
  obtain ⟨hint, hval⟩ := integral_gradient_ann hv hε hεη
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => by positivity)]
  rfl

end Annulus

end Torus

end SandierSerfaty

end
