/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The divergence theorem on the exterior of a disc, in polar coordinates

Mathlib has no divergence theorem on a plane domain with a circular hole. For a vector field
`Y = (Y₁, Y₂)` of class `C¹` away from a point `p` and vanishing outside a ball, the exterior
divergence integral is a pure boundary term on the circle:
`SandierSerfaty.Analysis.integral_exterior_div`
```
∫ x in {x | η ≤ ‖x - p‖}, (∂₁ Y₁ + ∂₂ Y₂) = - ∫ θ in -π..π, η (Y₁ cos θ + Y₂ sin θ)(p + η e^{iθ}).
```
The proof is the polar-coordinate chain rule `r · div Y = ∂_r (r Y_r) + ∂_θ Y_θ`, the polar change of
variables `Complex.integral_comp_polarCoord_symm`, Fubini on the compact box `[η, R] × [-π, π]`, and
the fundamental theorem of calculus in each variable (periodicity in `θ`, compact support in `r`).

Here `∂₁ f x = fderiv ℝ f x 1` and `∂₂ f x = fderiv ℝ f x I`.
-/

open MeasureTheory Filter Topology Set

public section

namespace SandierSerfaty

namespace Analysis

/-- The point of polar coordinates `(r, θ)`. -/
@[expose] noncomputable def polarPt (r θ : ℝ) : ℂ :=
  (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)

theorem norm_polarPt {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖polarPt r θ‖ = r := by
  have := Complex.norm_polarCoord_symm (r, θ)
  simp only [Complex.polarCoord_symm_apply] at this
  simp [polarPt, abs_of_nonneg hr] at this ⊢

theorem continuous_polarPt : Continuous fun q : ℝ × ℝ => polarPt q.1 q.2 := by
  unfold polarPt; fun_prop

theorem polarPt_pi (r : ℝ) : polarPt r Real.pi = polarPt r (-Real.pi) := by
  simp [polarPt]

theorem polarPt_ne_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : polarPt r θ ≠ 0 := by
  intro h
  have := norm_polarPt hr.le θ
  rw [h, norm_zero] at this
  exact hr.ne this

theorem hasDerivAt_polarPt_r (r θ : ℝ) :
    HasDerivAt (fun r : ℝ => polarPt r θ) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) r := by
  unfold polarPt
  simpa using ((hasDerivAt_id r).ofReal_comp).mul_const
    ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)

theorem hasDerivAt_polarPt_θ (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => polarPt r θ)
      ((r : ℂ) * (-(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * Complex.I)) θ := by
  unfold polarPt
  have h1 : HasDerivAt (fun θ : ℝ => (Real.cos θ : ℂ)) (-(Real.sin θ : ℂ)) θ := by
    simpa using (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 : HasDerivAt (fun θ : ℝ => (Real.sin θ : ℂ)) (Real.cos θ : ℂ) θ :=
    (Real.hasDerivAt_sin θ).ofReal_comp
  have := (h1.add (h2.mul_const Complex.I)).const_mul (r : ℂ)
  simpa using this

/-- The directional derivative along `cos θ + i sin θ` is `cos θ ∂₁ + sin θ ∂₂`. -/
theorem fderiv_polar_dir (Y : ℂ → ℝ) (x : ℂ) (θ : ℝ) :
    fderiv ℝ Y x ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
      Real.cos θ * fderiv ℝ Y x 1 + Real.sin θ * fderiv ℝ Y x Complex.I := by
  have : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
      Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    simp [Complex.real_smul]
  rw [this, map_add, map_smul, map_smul]
  simp

theorem fderiv_polar_dir' (Y : ℂ → ℝ) (x : ℂ) (r θ : ℝ) :
    fderiv ℝ Y x ((r : ℂ) * (-(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * Complex.I)) =
      r * (-Real.sin θ * fderiv ℝ Y x 1 + Real.cos θ * fderiv ℝ Y x Complex.I) := by
  have : ((r : ℂ) * (-(Real.sin θ : ℂ) + (Real.cos θ : ℂ) * Complex.I)) =
      (-(r * Real.sin θ)) • (1 : ℂ) + (r * Real.cos θ) • Complex.I := by
    simp [Complex.real_smul]; ring
  rw [this, map_add, map_smul, map_smul]
  simp
  ring

theorem hasDerivAt_comp_polarPt_r {Y : ℂ → ℝ} {r θ : ℝ} (hY : DifferentiableAt ℝ Y (polarPt r θ)) :
    HasDerivAt (fun r : ℝ => Y (polarPt r θ))
      (Real.cos θ * fderiv ℝ Y (polarPt r θ) 1 + Real.sin θ * fderiv ℝ Y (polarPt r θ) Complex.I) r := by
  rw [← fderiv_polar_dir]
  exact hY.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_polarPt_r r θ)

theorem hasDerivAt_comp_polarPt_θ {Y : ℂ → ℝ} {r θ : ℝ} (hY : DifferentiableAt ℝ Y (polarPt r θ)) :
    HasDerivAt (fun θ : ℝ => Y (polarPt r θ))
      (r * (-Real.sin θ * fderiv ℝ Y (polarPt r θ) 1 + Real.cos θ * fderiv ℝ Y (polarPt r θ) Complex.I))
      θ := by
  rw [← fderiv_polar_dir']
  exact hY.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_polarPt_θ r θ)


section Core

variable (Y₁ Y₂ : ℂ → ℝ)

/-- The radial component `Y · e_r` in polar coordinates. -/
@[expose] noncomputable def radialComp (r θ : ℝ) : ℝ :=
  Y₁ (polarPt r θ) * Real.cos θ + Y₂ (polarPt r θ) * Real.sin θ

/-- The angular component `Y · e_θ` in polar coordinates. -/
@[expose] noncomputable def angularComp (r θ : ℝ) : ℝ :=
  -(Y₁ (polarPt r θ)) * Real.sin θ + Y₂ (polarPt r θ) * Real.cos θ

/-- `∂_r (r Y_r)`. -/
@[expose] noncomputable def radialDeriv (r θ : ℝ) : ℝ :=
  radialComp Y₁ Y₂ r θ +
    r * (Real.cos θ * (Real.cos θ * fderiv ℝ Y₁ (polarPt r θ) 1 +
          Real.sin θ * fderiv ℝ Y₁ (polarPt r θ) Complex.I) +
      Real.sin θ * (Real.cos θ * fderiv ℝ Y₂ (polarPt r θ) 1 +
          Real.sin θ * fderiv ℝ Y₂ (polarPt r θ) Complex.I))

/-- `∂_θ Y_θ`. -/
@[expose] noncomputable def angularDeriv (r θ : ℝ) : ℝ :=
  -radialComp Y₁ Y₂ r θ +
    r * (-Real.sin θ * (-Real.sin θ * fderiv ℝ Y₁ (polarPt r θ) 1 +
          Real.cos θ * fderiv ℝ Y₁ (polarPt r θ) Complex.I) +
      Real.cos θ * (-Real.sin θ * fderiv ℝ Y₂ (polarPt r θ) 1 +
          Real.cos θ * fderiv ℝ Y₂ (polarPt r θ) Complex.I))

theorem radialDeriv_add_angularDeriv (r θ : ℝ) :
    radialDeriv Y₁ Y₂ r θ + angularDeriv Y₁ Y₂ r θ =
      r * (fderiv ℝ Y₁ (polarPt r θ) 1 + fderiv ℝ Y₂ (polarPt r θ) Complex.I) := by
  unfold radialDeriv angularDeriv
  have h := Real.sin_sq_add_cos_sq θ
  generalize fderiv ℝ Y₁ (polarPt r θ) 1 = a1
  generalize fderiv ℝ Y₁ (polarPt r θ) Complex.I = a2
  generalize fderiv ℝ Y₂ (polarPt r θ) 1 = b1
  generalize fderiv ℝ Y₂ (polarPt r θ) Complex.I = b2
  generalize Real.sin θ = s at h ⊢
  generalize Real.cos θ = c at h ⊢
  linear_combination r * (a1 + b2) * h

variable {Y₁ Y₂}

theorem hasDerivAt_radial {r θ : ℝ} (hY₁ : DifferentiableAt ℝ Y₁ (polarPt r θ))
    (hY₂ : DifferentiableAt ℝ Y₂ (polarPt r θ)) :
    HasDerivAt (fun r : ℝ => r * radialComp Y₁ Y₂ r θ) (radialDeriv Y₁ Y₂ r θ) r := by
  have h1 := hasDerivAt_comp_polarPt_r hY₁
  have h2 := hasDerivAt_comp_polarPt_r hY₂
  have h3 := ((h1.mul_const (Real.cos θ)).add (h2.mul_const (Real.sin θ)))
  have h4 := (hasDerivAt_id r).mul h3
  have e : (fun r : ℝ => r * radialComp Y₁ Y₂ r θ) = id * ((fun y => Y₁ (polarPt y θ) * Real.cos θ) +
      fun y => Y₂ (polarPt y θ) * Real.sin θ) := by
    funext y; simp [radialComp]
  rw [e]
  refine h4.congr_deriv ?_
  simp only [radialDeriv, radialComp, Pi.add_apply, id]
  ring

theorem hasDerivAt_angular {r θ : ℝ} (hY₁ : DifferentiableAt ℝ Y₁ (polarPt r θ))
    (hY₂ : DifferentiableAt ℝ Y₂ (polarPt r θ)) :
    HasDerivAt (fun θ : ℝ => angularComp Y₁ Y₂ r θ) (angularDeriv Y₁ Y₂ r θ) θ := by
  have h1 := hasDerivAt_comp_polarPt_θ hY₁
  have h2 := hasDerivAt_comp_polarPt_θ hY₂
  have h3 := (((h1.neg).mul (Real.hasDerivAt_sin θ)).add (h2.mul (Real.hasDerivAt_cos θ)))
  have e : (fun θ : ℝ => angularComp Y₁ Y₂ r θ) = (-fun θ => Y₁ (polarPt r θ)) * Real.sin +
      (fun θ => Y₂ (polarPt r θ)) * Real.cos := by
    funext y; simp [angularComp]
  rw [e]
  refine h3.congr_deriv ?_
  simp only [angularDeriv, radialComp, Pi.neg_apply]
  ring


theorem continuousAt_fderiv_apply {Y : ℂ → ℝ} {x : ℂ} (h : ContDiffAt ℝ 1 Y x) (v : ℂ) :
    ContinuousAt (fun y => fderiv ℝ Y y v) x := by
  have : ContDiffAt ℝ 0 (fderiv ℝ Y) x := h.fderiv_right (by norm_num)
  exact this.continuousAt.clm_apply continuousAt_const

section Continuity

variable (h₁ : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 Y₁ x) (h₂ : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 Y₂ x)
include h₁ h₂

theorem continuousAt_polar_pieces {q : ℝ × ℝ} (hq : 0 < q.1) :
    ContinuousAt (fun q : ℝ × ℝ => Y₁ (polarPt q.1 q.2)) q ∧
    ContinuousAt (fun q : ℝ × ℝ => Y₂ (polarPt q.1 q.2)) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₁ (polarPt q.1 q.2) 1) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₁ (polarPt q.1 q.2) Complex.I) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₂ (polarPt q.1 q.2) 1) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₂ (polarPt q.1 q.2) Complex.I) q := by
  have hne : polarPt q.1 q.2 ≠ 0 := polarPt_ne_zero hq q.2
  have hp : ContinuousAt (fun q : ℝ × ℝ => polarPt q.1 q.2) q := continuous_polarPt.continuousAt
  have e1 := h₁ _ hne
  have e2 := h₂ _ hne
  exact ⟨ContinuousAt.comp_of_eq e1.continuousAt hp rfl, ContinuousAt.comp_of_eq e2.continuousAt hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e1 1) hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e1 Complex.I) hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e2 1) hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e2 Complex.I) hp rfl⟩

theorem continuousOn_radialDeriv :
    ContinuousOn (fun q : ℝ × ℝ => radialDeriv Y₁ Y₂ q.1 q.2) {q | 0 < q.1} := by
  intro q hq
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := continuousAt_polar_pieces h₁ h₂ hq
  refine ContinuousAt.continuousWithinAt ?_
  have hr : ContinuousAt (fun q : ℝ × ℝ => q.1) q := continuousAt_fst
  have hc : ContinuousAt (fun q : ℝ × ℝ => Real.cos q.2) q :=
    (Real.continuous_cos.comp continuous_snd).continuousAt
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sin q.2) q :=
    (Real.continuous_sin.comp continuous_snd).continuousAt
  unfold radialDeriv radialComp
  apply_rules [ContinuousAt.add, ContinuousAt.mul, ContinuousAt.neg]

theorem continuousOn_angularDeriv :
    ContinuousOn (fun q : ℝ × ℝ => angularDeriv Y₁ Y₂ q.1 q.2) {q | 0 < q.1} := by
  intro q hq
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := continuousAt_polar_pieces h₁ h₂ hq
  refine ContinuousAt.continuousWithinAt ?_
  have hr : ContinuousAt (fun q : ℝ × ℝ => q.1) q := continuousAt_fst
  have hc : ContinuousAt (fun q : ℝ × ℝ => Real.cos q.2) q :=
    (Real.continuous_cos.comp continuous_snd).continuousAt
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sin q.2) q :=
    (Real.continuous_sin.comp continuous_snd).continuousAt
  unfold angularDeriv radialComp
  apply_rules [ContinuousAt.add, ContinuousAt.mul, ContinuousAt.neg]

end Continuity

end Core


/-- Fubini with the order of integration reversed, on a product of sets. -/
theorem setIntegral_prod_symm' {s t : Set ℝ} {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (s ×ˢ t) (volume.prod volume)) :
    ∫ z in s ×ˢ t, f z ∂(volume.prod volume) = ∫ y in t, ∫ x in s, f (x, y) := by
  rw [← setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) s t f]
  refine setIntegral_prod (f ∘ Prod.swap) ?_
  simp only [IntegrableOn, ← Measure.prod_restrict] at hf ⊢
  exact hf.swap

section Main

variable {Y₁ Y₂ : ℂ → ℝ}

/-- **Divergence theorem on the exterior of a disc** (centre `0`). -/
theorem integral_exterior_div_zero {η R : ℝ} (hη : 0 < η) (hηR : η ≤ R)
    (h₁ : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 Y₁ x) (h₂ : ∀ x, x ≠ 0 → ContDiffAt ℝ 1 Y₂ x)
    (hR : ∀ x : ℂ, R ≤ ‖x‖ → Y₁ x = 0 ∧ Y₂ x = 0) :
    ∫ x in {x : ℂ | η ≤ ‖x‖}, (fderiv ℝ Y₁ x 1 + fderiv ℝ Y₂ x Complex.I) =
      -∫ θ in (-Real.pi)..Real.pi, η * radialComp Y₁ Y₂ η θ := by
  set g : ℂ → ℝ := fun x => fderiv ℝ Y₁ x 1 + fderiv ℝ Y₂ x Complex.I with hg
  have hclosed : MeasurableSet {x : ℂ | η ≤ ‖x‖} := (isClosed_le continuous_const continuous_norm).measurableSet
  -- vanishing of the integrand outside the ball
  have hgR : ∀ x : ℂ, R < ‖x‖ → g x = 0 := by
    intro x hx
    have hev : Y₁ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
      exact (hR y hy.le).1
    have hev2 : Y₂ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
      exact (hR y hy.le).2
    simp [hg, hev.fderiv_eq, hev2.fderiv_eq]
  -- polar coordinates
  have hpolar := Complex.integral_comp_polarCoord_symm (E := ℝ) (Set.indicator {x : ℂ | η ≤ ‖x‖} g)
  rw [integral_indicator hclosed] at hpolar
  rw [← hpolar]
  set box : Set (ℝ × ℝ) := Icc η R ×ˢ Ioo (-Real.pi) Real.pi with hbox
  have hboxsub : box ⊆ polarCoord.target := by
    intro q hq
    rw [polarCoord_target]
    exact ⟨lt_of_lt_of_le hη hq.1.1, hq.2⟩
  have hpt : ∀ q : ℝ × ℝ, Complex.polarCoord.symm q = polarPt q.1 q.2 := fun q => by
    simp [polarPt]
  have hΦ : ∀ q ∈ box, q.1 • Set.indicator {x : ℂ | η ≤ ‖x‖} g (Complex.polarCoord.symm q) =
      radialDeriv Y₁ Y₂ q.1 q.2 + angularDeriv Y₁ Y₂ q.1 q.2 := by
    intro q hq
    rw [hpt, radialDeriv_add_angularDeriv]
    have hmem : polarPt q.1 q.2 ∈ {x : ℂ | η ≤ ‖x‖} := by
      show η ≤ ‖polarPt q.1 q.2‖
      rw [norm_polarPt (lt_of_lt_of_le hη hq.1.1).le]; exact hq.1.1
    rw [Set.indicator_of_mem hmem]
    simp [hg, smul_eq_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero polarCoord.open_target.measurableSet
    hboxsub ?_]
  swap
  · intro q hq
    obtain ⟨hqt, hqb⟩ := hq
    rw [polarCoord_target] at hqt
    have hnb : ¬ (q.1 ∈ Icc η R) := fun h => hqb ⟨h, hqt.2⟩
    rw [hpt]
    have hqn : ‖polarPt q.1 q.2‖ = q.1 := norm_polarPt hqt.1.le q.2
    by_cases hlt : q.1 < η
    · have : polarPt q.1 q.2 ∉ {x : ℂ | η ≤ ‖x‖} := by
        show ¬ η ≤ ‖polarPt q.1 q.2‖
        rw [hqn]; exact not_le.2 hlt
      rw [Set.indicator_of_notMem this]; simp
    · have hR' : R < q.1 := by
        by_contra hcon
        exact hnb ⟨not_lt.1 hlt, not_lt.1 hcon⟩
      have : g (polarPt q.1 q.2) = 0 := hgR _ (by rw [hqn]; exact hR')
      simp [Set.indicator, this]
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ioo) hΦ]
  -- the compact box and integrability
  have hdiff₁ : ∀ r θ : ℝ, 0 < r → DifferentiableAt ℝ Y₁ (polarPt r θ) := fun r θ hr =>
    (h₁ _ (polarPt_ne_zero hr θ)).differentiableAt one_ne_zero
  have hdiff₂ : ∀ r θ : ℝ, 0 < r → DifferentiableAt ℝ Y₂ (polarPt r θ) := fun r θ hr =>
    (h₂ _ (polarPt_ne_zero hr θ)).differentiableAt one_ne_zero
  set K : Set (ℝ × ℝ) := Icc η R ×ˢ Icc (-Real.pi) Real.pi with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKpos : K ⊆ {q : ℝ × ℝ | 0 < q.1} := fun q hq => lt_of_lt_of_le hη hq.1.1
  have hint₁ : IntegrableOn (fun q : ℝ × ℝ => radialDeriv Y₁ Y₂ q.1 q.2) box volume := by
    refine IntegrableOn.mono_set ?_ (Set.prod_mono subset_rfl Ioo_subset_Icc_self)
    exact (continuousOn_radialDeriv h₁ h₂).mono hKpos |>.integrableOn_compact hKc
  have hint₂ : IntegrableOn (fun q : ℝ × ℝ => angularDeriv Y₁ Y₂ q.1 q.2) box volume := by
    refine IntegrableOn.mono_set ?_ (Set.prod_mono subset_rfl Ioo_subset_Icc_self)
    exact (continuousOn_angularDeriv h₁ h₂).mono hKpos |>.integrableOn_compact hKc
  have hadd := integral_add hint₁ hint₂
  change ∫ q in box, _ = _
  rw [hadd]
  -- the angular part integrates to zero
  have hang : ∫ q in box, angularDeriv Y₁ Y₂ q.1 q.2 = 0 := by
    rw [hbox, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      setIntegral_prod _ (hbox ▸ hint₂)]
    have hz : ∀ r ∈ Icc η R, ∫ y in Ioo (-Real.pi) Real.pi, angularDeriv Y₁ Y₂ r y = 0 := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le hη hr.1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => angularComp Y₁ Y₂ r θ)]
      · simp [angularComp, polarPt_pi]
      · intro θ _
        exact hasDerivAt_angular (hdiff₁ r θ hr0) (hdiff₂ r θ hr0)
      · refine ContinuousOn.intervalIntegrable ?_
        have := (continuousOn_angularDeriv h₁ h₂).comp (f := fun θ : ℝ => (r, θ))
          (by fun_prop : Continuous fun θ : ℝ => (r, θ)).continuousOn
          (s := uIcc (-Real.pi) Real.pi) (fun θ _ => hr0)
        exact this
    rw [setIntegral_congr_fun measurableSet_Icc hz]
    simp
  -- the radial part
  have hrad : ∫ q in box, radialDeriv Y₁ Y₂ q.1 q.2 =
      ∫ θ in Ioo (-Real.pi) Real.pi, -(η * radialComp Y₁ Y₂ η θ) := by
    rw [hbox, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      setIntegral_prod_symm' (hbox ▸ hint₁)]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    simp only
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hηR]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => r * radialComp Y₁ Y₂ r θ)]
    · have hRz : radialComp Y₁ Y₂ R θ = 0 := by
        have hn : R ≤ ‖polarPt R θ‖ := by
          rw [norm_polarPt (hη.le.trans hηR)]
        simp [radialComp, (hR _ hn).1, (hR _ hn).2]
      rw [hRz]; ring
    · intro r hr
      rw [uIcc_of_le hηR] at hr
      have hr0 : 0 < r := lt_of_lt_of_le hη hr.1
      exact hasDerivAt_radial (hdiff₁ r θ hr0) (hdiff₂ r θ hr0)
    · refine ContinuousOn.intervalIntegrable ?_
      have := (continuousOn_radialDeriv h₁ h₂).comp (f := fun r : ℝ => (r, θ))
        (by fun_prop : Continuous fun r : ℝ => (r, θ)).continuousOn
        (s := uIcc η R) (fun r hr => by
          rw [uIcc_of_le hηR] at hr
          exact lt_of_lt_of_le hη hr.1)
      exact this
  rw [hang, hrad, add_zero, integral_neg,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]


/-- **Divergence theorem on the exterior of a disc.** For `C¹` fields away from `p` that vanish
outside a ball, the divergence integral over `{η ≤ ‖x - p‖}` is a boundary term on the circle
`‖x - p‖ = η` (outward normal of the exterior region `-(x - p)/‖x - p‖`). -/
theorem integral_exterior_div {p : ℂ} {η R : ℝ} (hη : 0 < η) (hηR : η ≤ R)
    (h₁ : ∀ x, x ≠ p → ContDiffAt ℝ 1 Y₁ x) (h₂ : ∀ x, x ≠ p → ContDiffAt ℝ 1 Y₂ x)
    (hR : ∀ x : ℂ, R ≤ ‖x - p‖ → Y₁ x = 0 ∧ Y₂ x = 0) :
    ∫ x in {x : ℂ | η ≤ ‖x - p‖}, (fderiv ℝ Y₁ x 1 + fderiv ℝ Y₂ x Complex.I) =
      -∫ θ in (-Real.pi)..Real.pi,
        η * (Y₁ (p + polarPt η θ) * Real.cos θ + Y₂ (p + polarPt η θ) * Real.sin θ) := by
  have key := integral_exterior_div_zero (Y₁ := fun y => Y₁ (p + y)) (Y₂ := fun y => Y₂ (p + y))
    hη hηR
    (fun x hx => ContDiffAt.comp (f := fun y : ℂ => p + y) x
      (h₁ (p + x) (fun h => hx (by simpa using h))) (contDiffAt_const.add contDiffAt_id))
    (fun x hx => ContDiffAt.comp (f := fun y : ℂ => p + y) x
      (h₂ (p + x) (fun h => hx (by simpa using h))) (contDiffAt_const.add contDiffAt_id))
    (fun x hx => hR (p + x) (by simpa using hx))
  have hfd : ∀ (Y : ℂ → ℝ) (y : ℂ), fderiv ℝ (fun y => Y (p + y)) y = fderiv ℝ Y (p + y) :=
    fun Y y => fderiv_comp_add_left p
  simp only [hfd] at key
  have hmp := (measurePreserving_add_left (volume : Measure ℂ) p).setIntegral_preimage_emb
    (measurableEmbedding_addLeft p) (fun x => fderiv ℝ Y₁ x 1 + fderiv ℝ Y₂ x Complex.I)
    {x : ℂ | η ≤ ‖x - p‖}
  have hpre : (fun y : ℂ => p + y) ⁻¹' {x : ℂ | η ≤ ‖x - p‖} = {x : ℂ | η ≤ ‖x‖} := by
    ext y; simp
  rw [hpre] at hmp
  rw [← hmp, key]
  simp [radialComp]

end Main

end Analysis

end SandierSerfaty

end
