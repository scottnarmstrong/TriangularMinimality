/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Analysis.RemovableSingularity
public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Complex.Harmonic.MeanValue
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Polar-coordinate integrals over annuli

Integrals in the plane computed in polar coordinates `x = r e^{iθ}` (`SandierSerfaty.Torus.dir θ`):

* `integral_polar_radial`: `∫_{‖x‖ ∈ R} f = ∫_{-π}^{π} ∫_R r f(r e^{iθ}) dr dθ`;
* `integral_inv_sq_annulus`: `∫_{ε ≤ ‖x‖ < ρ} ‖x‖⁻² = 2π log (ρ/ε)`;
* `integral_fderiv_div_sq_annulus`: `∫_{ε ≤ ‖x‖ < ρ} ‖x‖⁻² ∂v(x)[x] = ∫_{-π}^{π} (v(ρ e^{iθ}) - v(ε e^{iθ})) dθ`;
* `integral_circle_eq`: if `Δ v = 2π` then `∫_{-π}^{π} v(ρ e^{iθ}) dθ = 2π (v 0 + π ρ² / 2)`
  (mean value property for `v - π‖·‖²/2`);
* `integral_truncLog`: `∫ f_η = π η² / 2`.
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

theorem norm_ofReal_mul_dir (r θ : ℝ) : ‖(r : ℂ) * dir θ‖ = |r| := by
  rw [norm_mul, norm_dir, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_dir : Continuous dir := by unfold dir; fun_prop

/-- **Integration in polar coordinates over a radial set.** -/
theorem integral_polar_radial {f : ℂ → ℝ} {R : Set ℝ} (hR : MeasurableSet R) (hR0 : R ⊆ Ioi 0)
    (hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * f ((p.1 : ℂ) * dir p.2))
      (R ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ x in {x : ℂ | ‖x‖ ∈ R}, f x =
      ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in R, r * f ((r : ℂ) * dir θ) := by
  set S : Set ℂ := {x | ‖x‖ ∈ R} with hS
  have hSm : MeasurableSet S := measurable_norm hR
  set H : ℝ × ℝ → ℝ := fun p => p.1 * f ((p.1 : ℂ) * dir p.2) with hH
  rw [← integral_indicator hSm, ← Complex.integral_comp_polarCoord_symm]
  have h2 : ∫ z in polarCoord.target, z.1 • S.indicator f (Complex.polarCoord.symm z) =
      ∫ z in R ×ˢ Ioo (-Real.pi) Real.pi, H z := by
    rw [polarCoord_target]
    have hcongr : ∀ z ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        z.1 • S.indicator f (Complex.polarCoord.symm z) =
          (R ×ˢ Ioo (-Real.pi) Real.pi).indicator H z := by
      intro z hz
      have hr : 0 < z.1 := hz.1
      have hsymm : Complex.polarCoord.symm z = (z.1 : ℂ) * dir z.2 := by
        rw [Complex.polarCoord_symm_apply]; rfl
      have hn : ‖(z.1 : ℂ) * dir z.2‖ = z.1 := by
        rw [norm_ofReal_mul_dir, abs_of_pos hr]
      have hiff : (z.1 : ℂ) * dir z.2 ∈ S ↔ z ∈ R ×ˢ Ioo (-Real.pi) Real.pi := by
        simp only [hS, mem_ofPred_eq, hn, mem_prod]
        exact ⟨fun h => ⟨h, hz.2⟩, fun h => h.1⟩
      by_cases hmem : z ∈ R ×ˢ Ioo (-Real.pi) Real.pi
      · rw [indicator_of_mem hmem, hsymm, indicator_of_mem (hiff.2 hmem)]
        simp [hH]
      · rw [indicator_of_notMem hmem, hsymm, indicator_of_notMem (fun h => hmem (hiff.1 h))]
        simp
    rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcongr,
      setIntegral_indicator (hR.prod measurableSet_Ioo),
      inter_eq_right.2 (prod_mono hR0 subset_rfl)]
  rw [h2]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  have hsw : ∫ z in R ×ˢ Ioo (-Real.pi) Real.pi, H z =
      ∫ z in Ioo (-Real.pi) Real.pi ×ˢ R, H z.swap := by
    rw [hvol]
    exact (setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      R (Ioo (-Real.pi) Real.pi) H).symm
  have hint' : IntegrableOn (fun z : ℝ × ℝ => H z.swap) (Ioo (-Real.pi) Real.pi ×ˢ R)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := hint.swap
  rw [hsw, hvol, setIntegral_prod _ hint']
  rfl

/-- The inner integral over `Ico a b` as an interval integral. -/
theorem setIntegral_Ico_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    ∫ r in Ico a b, g r = ∫ r in a..b, g r := by
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab]

theorem integral_const_Ioo_pi (c : ℝ) :
    ∫ _θ in Ioo (-Real.pi) Real.pi, c = 2 * Real.pi * c := by
  rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
    smul_eq_mul]
  ring

/-- `∫_{ε ≤ ‖x‖ < ρ} ‖x‖⁻² = 2π log (ρ/ε)`. -/
theorem integral_inv_sq_annulus {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) :
    ∫ x in {x : ℂ | ε ≤ ‖x‖ ∧ ‖x‖ < ρ}, (‖x‖ ^ 2)⁻¹ = 2 * Real.pi * Real.log (ρ / ε) := by
  have hkey : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 * (‖(p.1 : ℂ) * dir p.2‖ ^ 2)⁻¹ = p.1⁻¹ := by
    intro p hp
    rw [norm_ofReal_mul_dir, abs_of_pos hp]
    field_simp
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.1 * (‖(p.1 : ℂ) * dir p.2‖ ^ 2)⁻¹)
      (Icc ε ρ ×ˢ Icc (-Real.pi) Real.pi) := by
    have : ContinuousOn (fun p : ℝ × ℝ => p.1⁻¹) (Icc ε ρ ×ˢ Icc (-Real.pi) Real.pi) :=
      (continuous_fst.continuousOn).inv₀ (fun p hp => (lt_of_lt_of_le hε hp.1.1).ne')
    refine this.congr fun p hp => hkey p (lt_of_lt_of_le hε hp.1.1)
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖(p.1 : ℂ) * dir p.2‖ ^ 2)⁻¹)
      (Ico ε ρ ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
  have := integral_polar_radial (f := fun x : ℂ => (‖x‖ ^ 2)⁻¹) measurableSet_Ico
    (fun r hr => lt_of_lt_of_le hε hr.1) hint
  have hin : ∀ θ : ℝ, ∫ r in Ico ε ρ, r * (‖(r : ℂ) * dir θ‖ ^ 2)⁻¹ = Real.log (ρ / ε) := by
    intro θ
    rw [setIntegral_congr_fun measurableSet_Ico (fun r hr => hkey (r, θ) (lt_of_lt_of_le hε hr.1)),
      setIntegral_Ico_eq_intervalIntegral hερ.le, integral_inv_of_pos hε (hε.trans hερ)]
  exact this.trans ((setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hin θ)).trans
    (integral_const_Ioo_pi _))

/-- The radial derivative along the ray `s ↦ s e^{iθ}`. -/
theorem hasDerivAt_ray_of_differentiableAt {v : ℂ → ℝ} {x : ℂ} {θ r : ℝ}
    (hx : (r : ℂ) * dir θ = x) (hv : DifferentiableAt ℝ v x) :
    HasDerivAt (fun s : ℝ => v ((s : ℂ) * dir θ)) (fderiv ℝ v x (dir θ)) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * dir θ) (dir θ) r := by
    have := (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (dir θ)
    simpa using this
  have h2 : HasFDerivAt v (fderiv ℝ v x) ((r : ℂ) * dir θ) := hx ▸ hv.hasFDerivAt
  exact h2.comp_hasDerivAt r h1

/-- `∫_{ε ≤ ‖x‖ < ρ} ‖x‖⁻² ∂v(x)[x] = ∫_{-π}^{π} (v(ρ e^{iθ}) - v(ε e^{iθ})) dθ`. -/
theorem integral_fderiv_div_sq_annulus {v : ℂ → ℝ} {R ε ρ : ℝ} (hv : ContDiffOn ℝ 1 v (ball 0 R))
    (hε : 0 < ε) (hερ : ε < ρ) (hρR : ρ < R) :
    ∫ x in {x : ℂ | ε ≤ ‖x‖ ∧ ‖x‖ < ρ}, (‖x‖ ^ 2)⁻¹ * fderiv ℝ v x x =
      ∫ θ in Ioo (-Real.pi) Real.pi, (v ((ρ : ℂ) * dir θ) - v ((ε : ℂ) * dir θ)) := by
  set D : ℝ × ℝ → ℝ := fun p => fderiv ℝ v ((p.1 : ℂ) * dir p.2) (dir p.2) with hD
  have hkey : ∀ p : ℝ × ℝ, 0 < p.1 →
      p.1 * ((‖(p.1 : ℂ) * dir p.2‖ ^ 2)⁻¹ * fderiv ℝ v ((p.1 : ℂ) * dir p.2) ((p.1 : ℂ) * dir p.2)) =
        D p := by
    intro p hp
    have hlin : fderiv ℝ v ((p.1 : ℂ) * dir p.2) ((p.1 : ℂ) * dir p.2) =
        p.1 * fderiv ℝ v ((p.1 : ℂ) * dir p.2) (dir p.2) := by
      have : (p.1 : ℂ) * dir p.2 = p.1 • dir p.2 := (Complex.real_smul).symm
      rw [this, map_smul, smul_eq_mul]
    rw [norm_ofReal_mul_dir, abs_of_pos hp, hlin, hD]
    field_simp
  have hmaps : MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * dir p.2) (Icc ε ρ ×ˢ Icc (-Real.pi) Real.pi)
      (ball 0 R) := by
    intro p hp
    rw [mem_ball_zero_iff, norm_ofReal_mul_dir, abs_of_pos (lt_of_lt_of_le hε hp.1.1)]
    exact lt_of_le_of_lt hp.1.2 hρR
  have hcontfd : ContinuousOn (fun x => fderiv ℝ v x) (ball 0 R) :=
    hv.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have hcontmap : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * dir p.2 :=
    (Complex.continuous_ofReal.comp continuous_fst).mul (continuous_dir.comp continuous_snd)
  have hDc : ContinuousOn D (Icc ε ρ ×ˢ Icc (-Real.pi) Real.pi) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ v ((p.1 : ℂ) * dir p.2))
        (Icc ε ρ ×ˢ Icc (-Real.pi) Real.pi) :=
      hcontfd.comp hcontmap.continuousOn hmaps
    exact h1.clm_apply (continuous_dir.comp continuous_snd).continuousOn
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * ((‖(p.1 : ℂ) * dir p.2‖ ^ 2)⁻¹ *
        fderiv ℝ v ((p.1 : ℂ) * dir p.2) ((p.1 : ℂ) * dir p.2)))
      (Ico ε ρ ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have : IntegrableOn D (Ico ε ρ ×ˢ Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      (hDc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
    refine this.congr_fun (fun p hp => (hkey p (lt_of_lt_of_le hε hp.1.1)).symm)
      (measurableSet_Ico.prod measurableSet_Ioo)
  have := integral_polar_radial (f := fun x : ℂ => (‖x‖ ^ 2)⁻¹ * fderiv ℝ v x x) measurableSet_Ico
    (fun r hr => lt_of_lt_of_le hε hr.1) hint
  refine this.trans (setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_))
  show ∫ r in Ico ε ρ, r * ((‖(r : ℂ) * dir θ‖ ^ 2)⁻¹ * fderiv ℝ v ((r : ℂ) * dir θ) ((r : ℂ) * dir θ)) =
    v ((ρ : ℂ) * dir θ) - v ((ε : ℂ) * dir θ)
  rw [setIntegral_congr_fun measurableSet_Ico
      (fun r hr => hkey (r, θ) (lt_of_lt_of_le hε hr.1)),
    setIntegral_Ico_eq_intervalIntegral hερ.le]
  have hder : ∀ s ∈ uIcc ε ρ, HasDerivAt (fun s : ℝ => v ((s : ℂ) * dir θ)) (D (s, θ)) s := by
    intro s hs
    rw [uIcc_of_le hερ.le] at hs
    have hsb : ((s : ℂ) * dir θ) ∈ ball 0 R := by
      rw [mem_ball_zero_iff, norm_ofReal_mul_dir, abs_of_pos (lt_of_lt_of_le hε hs.1)]
      exact lt_of_le_of_lt hs.2 hρR
    exact hasDerivAt_ray_of_differentiableAt rfl
      ((hv.contDiffAt (isOpen_ball.mem_nhds hsb)).differentiableAt (by simp))
  have hDθ : ContinuousOn (fun r : ℝ => D (r, θ)) (uIcc ε ρ) := by
    rw [uIcc_of_le hερ.le]
    exact hDc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, Ioo_subset_Icc_self hθ⟩)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder hDθ.intervalIntegrable

end Torus

end SandierSerfaty

end
