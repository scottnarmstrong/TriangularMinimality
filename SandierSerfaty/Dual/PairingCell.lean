/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.LipschitzIBP
public import SandierSerfaty.Torus.GreenRepr
public import SandierSerfaty.Analysis.PeriodicGreen

/-!
# Green's identity on the cell with a Lipschitz test function

Let `u = greenSum Γ a` (the torus potential off the charges, `Δu = 2π` there), `w` a Lipschitz
`Γ`-periodic function, and `φ = 1 - B` a `C¹` periodic cut-off vanishing near the charges. Then
```
∫_D φ ⟨∇w, ∇u⟩ + ∫_D w ⟨∇φ, ∇u⟩ + 2π ∫_D φ w = 0
```
(`cell_pairing_cutoff`): the divergence theorem for the periodic Lipschitz field `w φ ∇u`, with no
boundary term (`integral_torusDomain_fderiv_lipschitz`). This is the cell part of the dual
identity's Green computation (paper proof of `dual:identity`), with the piecewise-`C¹` function `h - H` in place of
a smooth test function.
-/

open MeasureTheory Filter Topology Set Metric Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis Torus

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ}

/-- The test cut-off: `C¹`, periodic, and `≡ 1` near every charge. -/
structure CutOff (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (B : ℂ → ℝ) : Prop where
  contDiff : ContDiff ℝ 1 B
  periodic : ∀ γ ∈ Γ, ∀ x, B (x + γ) = B x
  eq_one : ∀ x ∈ chargeSet Γ a, B =ᶠ[𝓝 x] fun _ => 1

variable {B : ℂ → ℝ}

theorem CutOff.contDiff_field (hB : CutOff Γ a B) (v : ℂ) :
    ContDiff ℝ 1 (fun x => (1 - B x) * fderiv ℝ (greenSum Γ a) x v) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ chargeSet Γ a
  · have : (fun y => (1 - B y) * fderiv ℝ (greenSum Γ a) y v) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hB.eq_one x hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have h2 : ContDiffAt ℝ (1 + 1 : ℕ) (greenSum Γ a) x :=
      (contDiffAt_greenSum hx).of_le (by norm_cast)
    exact (contDiffAt_const.sub hB.contDiff.contDiffAt).mul (contDiffAt_pd (n := 1) h2 v)

theorem CutOff.periodic_field (hB : CutOff Γ a B) (v : ℂ) :
    ∀ γ ∈ Γ, ∀ x, (1 - B (x + γ)) * fderiv ℝ (greenSum Γ a) (x + γ) v =
      (1 - B x) * fderiv ℝ (greenSum Γ a) x v := by
  intro γ hγ x
  rw [hB.periodic γ hγ, fderiv_periodic Γ (fun δ hδ y => greenSum_add_period hδ y) hγ]

/-- The pointwise divergence of the field `w φ ∇u` where `w` is differentiable. -/
theorem fderiv_field_add (hΓ : ZLattice.covolume Γ = N) (hB : CutOff Γ a B) {w : ℂ → ℝ} {x : ℂ}
    (hw : DifferentiableAt ℝ w x) :
    fderiv ℝ (fun y => w y * ((1 - B y) * fderiv ℝ (greenSum Γ a) y 1)) x 1 +
      fderiv ℝ (fun y => w y * ((1 - B y) * fderiv ℝ (greenSum Γ a) y Complex.I)) x Complex.I =
    (1 - B x) * gradDot w (greenSum Γ a) x +
      w x * gradDot (fun y => 1 - B y) (greenSum Γ a) x + 2 * Real.pi * ((1 - B x) * w x) := by
  by_cases hx : x ∈ chargeSet Γ a
  · have h0 : (fun y => 1 - B y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hB.eq_one x hx] with y hy; simp [hy]
    have hY : ∀ v : ℂ, (fun y => w y * ((1 - B y) * fderiv ℝ (greenSum Γ a) y v)) =ᶠ[𝓝 x]
        fun _ => 0 := fun v => by
      filter_upwards [h0] with y hy; simp [hy]
    have hBx : B x = 1 := (hB.eq_one x hx).self_of_nhds
    have hpd : ∀ v : ℂ, fderiv ℝ (fun y => 1 - B y) x v = 0 := fun v => by
      rw [h0.fderiv_eq]; simp
    rw [(hY 1).fderiv_eq, (hY Complex.I).fderiv_eq]
    simp [gradDot, pd₁, pd₂, hpd, hBx]
  · have h2 : ContDiffAt ℝ 2 (greenSum Γ a) x := (contDiffAt_greenSum hx).of_le (by norm_cast)
    have hφ : DifferentiableAt ℝ (fun y => 1 - B y) x :=
      (contDiffAt_const.sub hB.contDiff.contDiffAt).differentiableAt one_ne_zero
    have hd : ∀ v : ℂ, DifferentiableAt ℝ (fun y => fderiv ℝ (greenSum Γ a) y v) x :=
      fun v => differentiableAt_pd h2 v
    have hG : ∀ v : ℂ, DifferentiableAt ℝ (fun y => (1 - B y) * fderiv ℝ (greenSum Γ a) y v) x :=
      fun v => hφ.mul (hd v)
    have hΔ : Δ (greenSum Γ a) x = 2 * Real.pi := laplacian_greenSum hΓ hx
    rw [laplacian_eq_pd h2] at hΔ
    have e1 : pd₁ (greenSum Γ a) = fun y => fderiv ℝ (greenSum Γ a) y 1 := rfl
    have e2 : pd₂ (greenSum Γ a) = fun y => fderiv ℝ (greenSum Γ a) y Complex.I := rfl
    rw [e1, e2] at hΔ
    have prod : ∀ v e : ℂ, fderiv ℝ (fun y => w y * ((1 - B y) * fderiv ℝ (greenSum Γ a) y v)) x e =
        fderiv ℝ w x e * ((1 - B x) * fderiv ℝ (greenSum Γ a) x v) +
          w x * ((1 - B x) * fderiv ℝ (fun y => fderiv ℝ (greenSum Γ a) y v) x e +
            fderiv ℝ (greenSum Γ a) x v * fderiv ℝ (fun y => 1 - B y) x e) := by
      intro v e
      rw [fderiv_fun_mul hw (hG v), fderiv_fun_mul hφ (hd v)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    rw [prod, prod]
    simp only [gradDot, pd₁, pd₂] at hΔ ⊢
    linear_combination (w x * (1 - B x)) * hΔ

theorem exists_lipschitzWith_of_contDiff_periodic {G : ℂ → ℝ} (hG : ContDiff ℝ 1 G)
    (hper : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x) : ∃ K, LipschitzWith K G :=
  lipschitzWith_of_locallyLipschitz_periodic (Γ := Γ)
    (fun x => (hG.contDiffAt (x := x)).exists_lipschitzOnWith) hper

/-- **Green's identity on the cell for a Lipschitz test function.** -/
theorem cell_pairing_cutoff (hΓ : ZLattice.covolume Γ = N) (hB : CutOff Γ a B) {w : ℂ → ℝ}
    {K : NNReal} (hw : LipschitzWith K w) (hwper : ∀ γ ∈ Γ, ∀ x, w (x + γ) = w x) :
    IntegrableOn (fun x => (1 - B x) * gradDot w (greenSum Γ a) x +
      w x * gradDot (fun y => 1 - B y) (greenSum Γ a) x + 2 * Real.pi * ((1 - B x) * w x))
      (torusDomain Γ) ∧
    ∫ x in torusDomain Γ, ((1 - B x) * gradDot w (greenSum Γ a) x +
      w x * gradDot (fun y => 1 - B y) (greenSum Γ a) x + 2 * Real.pi * ((1 - B x) * w x)) = 0 := by
  set u := greenSum Γ a with hu
  set G₁ : ℂ → ℝ := fun x => (1 - B x) * fderiv ℝ u x 1 with hG₁
  set G₂ : ℂ → ℝ := fun x => (1 - B x) * fderiv ℝ u x Complex.I with hG₂
  have hc₁ : ContDiff ℝ 1 G₁ := hB.contDiff_field 1
  have hc₂ : ContDiff ℝ 1 G₂ := hB.contDiff_field Complex.I
  have hp₁ := hB.periodic_field 1
  have hp₂ := hB.periodic_field Complex.I
  obtain ⟨K₁, hK₁⟩ := exists_lipschitzWith_of_contDiff_periodic (Γ := Γ) hc₁ hp₁
  obtain ⟨K₂, hK₂⟩ := exists_lipschitzWith_of_contDiff_periodic (Γ := Γ) hc₂ hp₂
  obtain ⟨Mw, hMw⟩ := Torus.exists_bound_of_periodic Γ hw.continuous hwper
  obtain ⟨M₁, hM₁⟩ := Torus.exists_bound_of_periodic Γ hK₁.continuous hp₁
  obtain ⟨M₂, hM₂⟩ := Torus.exists_bound_of_periodic Γ hK₂.continuous hp₂
  have hY₁ := LipschitzWith_mul_of_bounded hw hK₁ hMw hM₁
  have hY₂ := LipschitzWith_mul_of_bounded hw hK₂ hMw hM₂
  have hYp₁ : ∀ γ ∈ Γ, ∀ x, w (x + γ) * G₁ (x + γ) = w x * G₁ x := fun γ hγ x => by
    rw [hwper γ hγ]; exact congrArg (fun t => w x * t) (hp₁ γ hγ x)
  have hYp₂ : ∀ γ ∈ Γ, ∀ x, w (x + γ) * G₂ (x + γ) = w x * G₂ x := fun γ hγ x => by
    rw [hwper γ hγ]; exact congrArg (fun t => w x * t) (hp₂ γ hγ x)
  have i₁ := integral_torusDomain_fderiv_lipschitz Γ hY₁ hYp₁ 1
  have i₂ := integral_torusDomain_fderiv_lipschitz Γ hY₂ hYp₂ Complex.I
  have hfin : IsFiniteMeasure (volume.restrict (torusDomain Γ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (Torus.volume_torusDomain_ne_top Γ)⟩
  have hint : ∀ (Y : ℂ → ℝ) (KY : NNReal), LipschitzWith KY Y → ∀ e : ℂ,
      IntegrableOn (fun x => fderiv ℝ Y x e) (torusDomain Γ) := by
    intro Y KY hY e
    refine Measure.integrableOn_of_bounded (Torus.volume_torusDomain_ne_top Γ)
      (measurable_fderiv_apply_const ℝ Y e).aestronglyMeasurable (M := KY * ‖e‖) ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    have h1 := (fderiv ℝ Y x).le_opNorm e
    have h2 := norm_fderiv_le_of_lipschitz ℝ hY (x₀ := x)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  have hae : ∀ᵐ x ∂(volume.restrict (torusDomain Γ)), DifferentiableAt ℝ w x :=
    ae_restrict_of_ae hw.ae_differentiableAt
  have hae' : (fun x => (1 - B x) * gradDot w u x +
      w x * gradDot (fun y => 1 - B y) u x + 2 * Real.pi * ((1 - B x) * w x)) =ᵐ[volume.restrict (torusDomain Γ)]
      fun x => fderiv ℝ (fun y => w y * G₁ y) x 1 + fderiv ℝ (fun y => w y * G₂ y) x Complex.I := by
    filter_upwards [hae] with x hx
    exact (fderiv_field_add hΓ hB hx).symm
  refine ⟨((hint _ _ hY₁ 1).add (hint _ _ hY₂ Complex.I)).congr hae'.symm, ?_⟩
  have hsum : ∫ x in torusDomain Γ, ((1 - B x) * gradDot w u x +
      w x * gradDot (fun y => 1 - B y) u x + 2 * Real.pi * ((1 - B x) * w x)) =
      ∫ x in torusDomain Γ, (fderiv ℝ (fun y => w y * G₁ y) x 1 +
        fderiv ℝ (fun y => w y * G₂ y) x Complex.I) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    exact (fderiv_field_add hΓ hB hx).symm
  rw [hsum, integral_add (hint _ _ hY₁ 1) (hint _ _ hY₂ Complex.I), i₁, i₂, add_zero]

end Dual

end SandierSerfaty

end
