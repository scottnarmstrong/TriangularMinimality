/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.PotentialLocal
public import SandierSerfaty.Torus.PotentialExists
public import SandierSerfaty.Torus.Lattice
public import SandierSerfaty.Geometry.VoronoiPeriodic
public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.TriangularField
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The gradient of a torus potential is an electric field

**Theorem** (`SandierSerfaty.gradient_torusPotential_mem_elec`). For a lattice `Γ ⊆ ℂ` of covolume
`N` and `N` charges `a i` with pairwise distinct classes modulo `Γ`, the gradient of the torus potential
belongs to `elec (periodicSites Γ a)`: it is locally integrable and
`∫ ⟪∇h, ∇φ⟫ = 2π (∑_{p ∈ Γ + a} φ p - ∫ φ)` for every smooth compactly supported `φ`.

**Corollary** (`SandierSerfaty.triangularField_mem_elec`): `triangularField ∈ elec Λ_tri`, the first
conjunct of `triangularField_spec`.

## Proof

Near a charge `p`, `h = v - log ‖· - p‖` with `v` smooth and `Δ v = 2π` (`IsTorusPotential.exists_local_form`),
so for `φ` supported in the ball of the local form
* `∫ ⟪∇v, ∇φ⟫ = -∫ Δv φ = -2π ∫ φ` (Green's identity, `integral_inner_gradient_eq`);
* `∫ ‖x - p‖⁻² ⟪x - p, ∇φ⟫ = -2π φ(p)` (`integral_fderiv_div_sq`, in polar coordinates);

and `∇ log ‖· - p‖ = (x - p) / ‖x - p‖²`. Away from the charges, Green's identity for `h` itself applies.
A test function is split into finitely many pieces, one near each charge of its support
(smooth bump functions), and the identity is additive.
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-! ### Polar coordinates: the logarithmic kernel -/

/-- The unit vector in direction `θ`. -/
@[expose] noncomputable def dir (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I

theorem norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := by
  have h : ‖dir θ‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, dir, Complex.normSq_add_mul_I]
    exact Real.cos_sq_add_sin_sq θ
  have h0 := norm_nonneg (dir θ)
  nlinarith

/-- A `C¹` compactly supported function and its derivative vanish far from the origin. -/
theorem exists_forall_norm_le_zero {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ y : ℂ, R < ‖y‖ → fderiv ℝ φ y = 0 ∧ φ y = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨R, fun y hy => ?_⟩
  have hy' : y ∉ tsupport φ := fun h => by
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have h2 : φ =ᶠ[𝓝 y] 0 := by
    rw [notMem_tsupport_iff_eventuallyEq] at hy'; exact hy'
  exact ⟨by simp [h2.fderiv_eq], image_eq_zero_of_notMem_tsupport hy'⟩

/-- The directional derivative of `φ` along the ray `r ↦ p + r e^{iθ}`. -/
theorem hasDerivAt_ray {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (p : ℂ) (θ r : ℝ) :
    HasDerivAt (fun s : ℝ => φ ((s : ℂ) * dir θ + p)) (fderiv ℝ φ ((r : ℂ) * dir θ + p) (dir θ)) r := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * dir θ + p) (dir θ) r := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (dir θ)).add_const p
    simpa using this
  have h2 : HasFDerivAt φ (fderiv ℝ φ ((r : ℂ) * dir θ + p)) ((r : ℂ) * dir θ + p) :=
    (hφ.differentiable (by norm_num) _).hasFDerivAt
  exact h2.comp_hasDerivAt r h1

/-- **The logarithmic kernel in the plane.** `∫ ‖x - p‖⁻² ⟪x - p, ∇φ⟫ = -2π φ(p)`, i.e.
`Δ log ‖· - p‖ = 2π δ_p`. -/
theorem integral_fderiv_div_sq {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (p : ℂ) :
    ∫ x : ℂ, (‖x - p‖ ^ 2)⁻¹ * fderiv ℝ φ x (x - p) = -(2 * Real.pi * φ p) := by
  obtain ⟨R, hR⟩ := exists_forall_norm_le_zero hc
  set Φ : ℂ → ℝ := fun y => (‖y‖ ^ 2)⁻¹ * fderiv ℝ φ (y + p) y with hΦ
  have h1 : ∫ x : ℂ, (‖x - p‖ ^ 2)⁻¹ * fderiv ℝ φ x (x - p) = ∫ y : ℂ, Φ y := by
    rw [← integral_sub_right_eq_self Φ p]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [hΦ]
  rw [h1, ← Complex.integral_comp_polarCoord_symm]
  set D : ℝ × ℝ → ℝ := fun z => fderiv ℝ φ ((z.1 : ℂ) * dir z.2 + p) (dir z.2) with hD
  have h2 : ∫ z in polarCoord.target, z.1 • Φ (Complex.polarCoord.symm z) =
      ∫ z in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, D z := by
    rw [polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun z hz => ?_
    have hr : 0 < z.1 := hz.1
    have hsymm : Complex.polarCoord.symm z = (z.1 : ℂ) * dir z.2 := by
      rw [Complex.polarCoord_symm_apply]; rfl
    simp only [hΦ, hD, hsymm, smul_eq_mul]
    have hn : ‖(z.1 : ℂ) * dir z.2‖ = z.1 := by
      rw [norm_mul, norm_dir, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hlin : fderiv ℝ φ ((z.1 : ℂ) * dir z.2 + p) ((z.1 : ℂ) * dir z.2) =
        z.1 * fderiv ℝ φ ((z.1 : ℂ) * dir z.2 + p) (dir z.2) := by
      have : (z.1 : ℂ) * dir z.2 = z.1 • dir z.2 := (Complex.real_smul).symm
      rw [this, map_smul, smul_eq_mul]
    rw [hn, hlin]
    field_simp
  rw [h2]
  have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
  have hdir : Continuous dir := by unfold dir; fun_prop
  have hDc : Continuous D := by
    have h1 : Continuous fun z : ℝ × ℝ => (z.1 : ℂ) * dir z.2 + p := by
      have hs2 : Continuous fun z : ℝ × ℝ => dir z.2 := hdir.comp continuous_snd
      exact ((Complex.continuous_ofReal.comp continuous_fst).mul hs2).add continuous_const
    exact ((hφ.continuous_fderiv (by norm_num)).comp h1).clm_apply (hdir.comp continuous_snd)
  have hfar : ∀ θ r : ℝ, R + ‖p‖ < r → fderiv ℝ φ ((r : ℂ) * dir θ + p) = 0 ∧
      φ ((r : ℂ) * dir θ + p) = 0 := by
    intro θ r hr
    apply hR
    have h1 : ‖(r : ℂ) * dir θ‖ = |r| := by
      rw [norm_mul, norm_dir, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(r : ℂ) * dir θ‖ ≤ ‖(r : ℂ) * dir θ + p‖ + ‖p‖ := by
      have := norm_sub_le ((r : ℂ) * dir θ + p) p
      simpa using this
    have h3 : r ≤ |r| := le_abs_self r
    linarith
  have hsw : ∫ z in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, D z =
      ∫ z in Ioo (-Real.pi) Real.pi ×ˢ Ioi (0 : ℝ), D z.swap := by
    rw [hvol]
    exact (setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ioi 0) (Ioo (-Real.pi) Real.pi) D).symm
  rw [hsw]
  have hint : IntegrableOn (fun z : ℝ × ℝ => D z.swap) (Ioo (-Real.pi) Real.pi ×ˢ Ioi (0 : ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have hg : Continuous fun z : ℝ × ℝ => D z.swap := hDc.comp continuous_swap
    have hs : IntegrableOn (fun z : ℝ × ℝ => D z.swap)
        (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) (R + ‖p‖))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hs.of_forall_sdiff_eq_zero (measurableSet_Ioo.prod measurableSet_Ioi) ?_
    intro z hz
    have hz2 : R + ‖p‖ < z.2 := by
      by_contra hle
      exact hz.2 ⟨⟨hz.1.1.1.le, hz.1.1.2.le⟩, hz.1.2.le, not_lt.1 hle⟩
    simp [hD, (hfar z.1 z.2 hz2).1]
  rw [hvol, setIntegral_prod _ hint]
  have hinner : ∀ θ ∈ Ioo (-Real.pi) Real.pi,
      ∫ r in Ioi (0 : ℝ), D (r, θ) = -φ p := by
    intro θ _
    have hcont : Continuous fun s : ℝ => φ ((s : ℂ) * dir θ + p) :=
      hφ.continuous.comp (by fun_prop)
    have hDθ : Continuous fun r : ℝ => D (r, θ) := hDc.comp (by fun_prop)
    have hf'int : IntegrableOn (fun r : ℝ => D (r, θ)) (Ioi 0) := by
      have hs : IntegrableOn (fun r : ℝ => D (r, θ)) (Icc 0 (R + ‖p‖)) :=
        hDθ.continuousOn.integrableOn_Icc
      refine hs.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
      intro r hr
      have hr2 : R + ‖p‖ < r := by
        by_contra hle
        exact hr.2 ⟨hr.1.le, not_lt.1 hle⟩
      simp [hD, (hfar θ r hr2).1]
    have htend : Tendsto (fun s : ℝ => φ ((s : ℂ) * dir θ + p)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (R + ‖p‖)] with s hs
      exact (hfar θ s hs).2.symm
    have := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (f := fun s : ℝ => φ ((s : ℂ) * dir θ + p)) (f' := fun r : ℝ => D (r, θ)) (m := 0)
      hcont.continuousWithinAt (fun r _ => hasDerivAt_ray hφ p θ r) hf'int htend
    simpa using this
  have h3 : ∫ θ in Ioo (-Real.pi) Real.pi, ∫ r in Ioi (0 : ℝ), D (r, θ) =
      ∫ _θ in Ioo (-Real.pi) Real.pi, -φ p :=
    setIntegral_congr_fun measurableSet_Ioo hinner
  simp only [Prod.swap_prod_mk]
  rw [h3, setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos]),
    smul_eq_mul]
  ring

/-! ### Green's identity in gradient form -/

theorem inner_gradient_gradient (u φ : ℂ → ℝ) (x : ℂ) :
    inner ℝ (gradient u x) (gradient φ x) =
      Weyl.pd 1 u x * Weyl.pd 1 φ x + Weyl.pd Complex.I u x * Weyl.pd Complex.I φ x := by
  have hre : ∀ f : ℂ → ℝ, (gradient f x).re = Weyl.pd 1 f x := by
    intro f
    show (gradient f x).re = fderiv ℝ f x 1
    have e : ∀ w : ℂ, inner ℝ w 1 = w.re := fun w => by simp [Complex.inner]
    rw [← inner_gradient_apply f x 1, e]
  have him : ∀ f : ℂ → ℝ, (gradient f x).im = Weyl.pd Complex.I f x := by
    intro f
    show (gradient f x).im = fderiv ℝ f x Complex.I
    have e : ∀ w : ℂ, inner ℝ w Complex.I = w.im := fun w => by simp [Complex.inner]
    rw [← inner_gradient_apply f x Complex.I, e]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, hre, him]
  ring

theorem continuousOn_pd {u : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hu : ContDiffOn ℝ 1 u W)
    (v : ℂ) : ContinuousOn (Weyl.pd v u) W := by
  intro x hx
  exact (Weyl.contDiffAt_pd (n := 0) (by simpa using hu.contDiffAt (hW.mem_nhds hx))
    v).continuousAt.continuousWithinAt

theorem integrable_inner_gradient {u φ : ℂ → ℝ} {W K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hW : IsOpen W) (hu : ContDiffOn ℝ 1 u W) (hφ : ContDiff ℝ 1 φ) (hφ0 : ∀ x ∉ K, φ x = 0) :
    Integrable (fun x => inner ℝ (gradient u x) (gradient φ x)) := by
  simp_rw [inner_gradient_gradient]
  have hp : ∀ v : ℂ, Integrable (fun x => Weyl.pd v u x * Weyl.pd v φ x) := fun v =>
    Weyl.integrable_mul_of_supp hK hKW (continuousOn_pd hW hu v)
      (Weyl.contDiff_pd (m := 0) hφ (by norm_num) v).continuous
      (Weyl.pd_eq_zero_of_notMem hK hφ0 v)
  exact (hp 1).add (hp Complex.I)

/-- **Green's identity in gradient form.** If `u` is `C²` on an open set `W` and `φ` is `C²` and vanishes
off a compact subset `K` of `W`, then `∫ ⟪∇u, ∇φ⟫ = -∫ Δu φ`. -/
theorem integral_inner_gradient_eq {u φ : ℂ → ℝ} {W K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hW : IsOpen W) (hu : ContDiffOn ℝ 2 u W) (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ x ∉ K, φ x = 0) :
    ∫ x, inner ℝ (gradient u x) (gradient φ x) = -∫ x, Δ u x * φ x := by
  have hu1 : ContDiffOn ℝ 1 u W := hu.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hpu : ∀ v : ℂ, ContDiffOn ℝ 1 (Weyl.pd v u) W := by
    intro v x hx
    exact (Weyl.contDiffAt_pd (n := 1) (by simpa using hu.contDiffAt (hW.mem_nhds hx))
      v).contDiffWithinAt
  have hR : ∀ x, Δ u x * φ x =
      Weyl.pd 1 (Weyl.pd 1 u) x * φ x + Weyl.pd Complex.I (Weyl.pd Complex.I u) x * φ x := by
    intro x
    by_cases hx : x ∈ K
    · rw [Weyl.lap_eq_pd (hu.contDiffAt (hW.mem_nhds (hKW hx)))]; ring
    · rw [hφ0 x hx]; simp
  have hint : ∀ v : ℂ, Integrable (fun x => Weyl.pd v (Weyl.pd v u) x * φ x) := fun v =>
    Weyl.integrable_mul_of_supp hK hKW (continuousOn_pd hW (hpu v) v) hφ.continuous hφ0
  have hint' : ∀ v : ℂ, Integrable (fun x => Weyl.pd v u x * Weyl.pd v φ x) := fun v =>
    Weyl.integrable_mul_of_supp hK hKW (continuousOn_pd hW hu1 v)
      (Weyl.contDiff_pd (m := 0) hφ1 (by norm_num) v).continuous
      (Weyl.pd_eq_zero_of_notMem hK hφ0 v)
  have key : ∀ v : ℂ, ∫ x, Weyl.pd v u x * Weyl.pd v φ x =
      -∫ x, Weyl.pd v (Weyl.pd v u) x * φ x := fun v =>
    Weyl.integral_mul_pd_eq_neg hK hKW hW (hpu v) hφ1 hφ0 v
  simp_rw [inner_gradient_gradient, hR]
  rw [integral_add (hint' 1) (hint' Complex.I), integral_add (hint 1) (hint Complex.I), key 1,
    key Complex.I]
  ring

/-! ### Test-function calculus -/

theorem fderiv_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 := by
  have h2 : φ =ᶠ[𝓝 x] 0 := by
    rw [notMem_tsupport_iff_eventuallyEq] at hx; exact hx
  simp [h2.fderiv_eq]

theorem gradient_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport φ) :
    gradient φ x = 0 := by
  simp [gradient, fderiv_eq_zero_of_notMem_tsupport hx]

theorem continuous_gradient {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) : Continuous (gradient φ) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hφ.continuous_fderiv (by norm_num))

theorem hasCompactSupport_gradient {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) :=
  HasCompactSupport.intro hc fun _ hx => gradient_eq_zero_of_notMem_tsupport hx

/-- A locally integrable field paired with the gradient of a `C¹` compactly supported function is
integrable. -/
theorem integrable_inner_gradient_of_locallyIntegrable {E : ℂ → ℂ}
    (hE : LocallyIntegrable E volume) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => inner ℝ (E x) (gradient φ x)) := by
  have hK : IsCompact (tsupport φ) := hc
  obtain ⟨M, hM⟩ := (hasCompactSupport_gradient hc).exists_bound_of_continuous
    (continuous_gradient hφ)
  have hEK : IntegrableOn (fun x => M * ‖E x‖) (tsupport φ) :=
    ((hE.integrableOn_isCompact hK).norm).const_mul M
  have hmeas : AEStronglyMeasurable (fun x => inner ℝ (E x) (gradient φ x)) volume :=
    AEStronglyMeasurable.inner (hE.aestronglyMeasurable : AEStronglyMeasurable E volume)
      (continuous_gradient hφ).aestronglyMeasurable
  refine Integrable.mono' (hEK.integrable_indicator hK.measurableSet) hmeas
    (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport φ
  · rw [indicator_of_mem hx]
    calc ‖inner ℝ (E x) (gradient φ x)‖ ≤ ‖E x‖ * ‖gradient φ x‖ := norm_inner_le_norm _ _
      _ ≤ ‖E x‖ * M := by gcongr; exact hM x
      _ = M * ‖E x‖ := mul_comm _ _
  · rw [indicator_of_notMem hx, gradient_eq_zero_of_notMem_tsupport hx]
    simp

theorem finite_inter_support {P : Set ℂ} (hlf : ∀ R : ℝ, (P ∩ closedBall (0 : ℂ) R).Finite)
    {φ : ℂ → ℝ} (hc : HasCompactSupport φ) : (P ∩ Function.support φ).Finite := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  exact (hlf R).subset fun x hx => ⟨hx.1, hR (subset_tsupport φ hx.2)⟩

/-- The weak electric-field identity for the test function `φ`. -/
@[expose] def ElecId (E : ℂ → ℂ) (C : Set ℂ) (φ : ℂ → ℝ) : Prop :=
  (∫ x, inner ℝ (E x) (gradient φ x)) = 2 * Real.pi * ((∑ᶠ p ∈ C, φ p) - ∫ x, φ x)

/-- The weak electric-field identity is additive in the test function. -/
theorem ElecId.add {E : ℂ → ℂ} (hE : LocallyIntegrable E volume) {C : Set ℂ}
    (hlf : ∀ R : ℝ, (C ∩ closedBall (0 : ℂ) R).Finite) {φ₁ φ₂ : ℂ → ℝ}
    (h₁ : ContDiff ℝ ∞ φ₁) (c₁ : HasCompactSupport φ₁)
    (h₂ : ContDiff ℝ ∞ φ₂) (c₂ : HasCompactSupport φ₂)
    (e₁ : ElecId E C φ₁) (e₂ : ElecId E C φ₂) : ElecId E C (fun x => φ₁ x + φ₂ x) := by
  have d₁ : Differentiable ℝ φ₁ := h₁.differentiable (by simp)
  have d₂ : Differentiable ℝ φ₂ := h₂.differentiable (by simp)
  have hg : ∀ x, gradient (fun y => φ₁ y + φ₂ y) x = gradient φ₁ x + gradient φ₂ x := by
    intro x
    simp only [gradient]
    rw [fderiv_fun_add (d₁ x) (d₂ x), map_add]
  have i₁ := integrable_inner_gradient_of_locallyIntegrable hE (h₁.of_le (by simp)) c₁
  have i₂ := integrable_inner_gradient_of_locallyIntegrable hE (h₂.of_le (by simp)) c₂
  have j₁ : Integrable φ₁ := h₁.continuous.integrable_of_hasCompactSupport c₁
  have j₂ : Integrable φ₂ := h₂.continuous.integrable_of_hasCompactSupport c₂
  unfold ElecId at *
  simp_rw [hg, inner_add_right]
  rw [integral_add i₁ i₂, integral_add j₁ j₂,
    finsum_mem_add_distrib' (finite_inter_support hlf c₁) (finite_inter_support hlf c₂), e₁, e₂]
  ring

end Torus

namespace IsTorusPotential

open Torus

/-- Away from the charges, the identity follows from Green's identity for `h`. -/
theorem elecId_of_subset_compl {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hK : tsupport φ ⊆ {x : ℂ | ∀ i, x - a i ∉ Γ}) :
    ElecId (gradient h) (chargeSet Γ a) φ := by
  have hopen := isOpen_notMem_chargeSet Γ a
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hG := integral_inner_gradient_eq (u := h) hc hK hopen (hP.2.1.of_le (by norm_num))
    (hφ.of_le (by norm_num)) hφ0
  have hG' : ∫ x, Δ h x * φ x = 2 * Real.pi * ∫ x, φ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only; rw [hP.2.2.1 x (hK hx)]
    · simp [hφ0 x hx]
  have hs : ∑ᶠ p ∈ chargeSet Γ a, φ p = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero fun p hp => hφ0 p fun hpK => ?_
    exact notMem_chargeSet_iff.2 (hK hpK) hp
  unfold ElecId
  rw [hG, hG', hs]
  ring

/-- **Near a charge:** the identity holds for every test function supported in the ball of the local
form. -/
theorem exists_radius_elecId {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {p : ℂ} (hp : p ∈ chargeSet Γ a) :
    ∃ r > 0, ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball p r →
      ElecId (gradient h) (chargeSet Γ a) φ := by
  obtain ⟨r, hr, v, hv, hvΔ, hloc⟩ := hP.exists_local_form hp
  refine ⟨r, hr, fun φ hφ hc hsub => ?_⟩
  have hK : IsCompact (tsupport φ) := hc
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hG := integral_inner_gradient_eq (u := v) hK hsub isOpen_ball (hv.of_le (by norm_num))
    (hφ.of_le (by norm_num)) hφ0
  have hG' : ∫ x, Δ v x * φ x = 2 * Real.pi * ∫ x, φ x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · simp only; rw [hvΔ x (hsub hx)]
    · simp [hφ0 x hx]
  have hA := integrable_inner_gradient hK hsub isOpen_ball (hv.of_le (by norm_num)) hφ1 hφ0
  have hL := integrable_inner_gradient_of_locallyIntegrable hP.locallyIntegrable_gradient hφ1 hc
  have hB := integral_fderiv_div_sq hφ1 hc p
  have hpt : ∀ x, x ≠ p → (‖x - p‖ ^ 2)⁻¹ * fderiv ℝ φ x (x - p) =
      inner ℝ (gradient v x) (gradient φ x) - inner ℝ (gradient h x) (gradient φ x) := by
    intro x hxp
    by_cases hx : x ∈ tsupport φ
    · have hfd := fderiv_eq_of_eq_sub_log hv (fun y hy hyp => (hloc y hy hyp).2) (hsub hx) hxp
      have e1 : inner ℝ (x - p) (gradient φ x) = fderiv ℝ φ x (x - p) := by
        rw [real_inner_comm]; exact inner_gradient_apply φ x (x - p)
      rw [inner_gradient_apply, inner_gradient_apply, hfd]
      simp only [sub_apply, smul_apply, innerSL_apply_apply,
        smul_eq_mul, e1]
      ring
    · simp [gradient_eq_zero_of_notMem_tsupport hx, fderiv_eq_zero_of_notMem_tsupport hx]
  have hae : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ p := by rw [ae_iff]; simp
  have hint : ∫ x, (‖x - p‖ ^ 2)⁻¹ * fderiv ℝ φ x (x - p) =
      (∫ x, inner ℝ (gradient v x) (gradient φ x)) - ∫ x, inner ℝ (gradient h x) (gradient φ x) := by
    rw [← integral_sub hA hL]
    exact integral_congr_ae (hae.mono fun x hx => hpt x hx)
  have hs : ∑ᶠ q ∈ chargeSet Γ a, φ q = φ p := by
    rw [finsum_mem_eq_sum_of_inter_support_eq φ (t := {p}), Finset.sum_singleton]
    ext x
    constructor
    · rintro ⟨hxP, hxs⟩
      have hxb : x ∈ ball p r := hsub (subset_tsupport φ hxs)
      by_cases hxp : x = p
      · subst hxp; exact ⟨by simp, hxs⟩
      · exact absurd hxP (hloc x hxb hxp).1
    · rintro ⟨hx, hxs⟩
      have : x = p := by simpa using hx
      subst this
      exact ⟨hp, hxs⟩
  unfold ElecId
  rw [hs]
  rw [hG, hG', hB] at hint
  linarith

/-- **The identity for every test function**, by induction on the finitely many charges in its support,
splitting off one charge at a time with a smooth bump function. -/
theorem elecId_of_subset {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h)
    (hlf : ∀ R : ℝ, (chargeSet Γ a ∩ closedBall (0 : ℂ) R).Finite) :
    ∀ (S : Finset ℂ) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x ∈ chargeSet Γ a, x ∈ tsupport φ → x ∈ S) → ElecId (gradient h) (chargeSet Γ a) φ := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro φ hφ hc hS
    refine hP.elecId_of_subset_compl hφ hc fun x hx => ?_
    exact notMem_chargeSet_iff.1 fun hxP => by simpa using hS x hxP hx
  | insert q S hq ih =>
    intro φ hφ hc hS
    by_cases hqP : q ∈ chargeSet Γ a
    · obtain ⟨r, hr, hloc⟩ := hP.exists_radius_elecId hqP
      set χ : ContDiffBump q := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hχdef
      have hχ : ContDiff ℝ ∞ (χ : ℂ → ℝ) := χ.contDiff
      have hφ₁ : ContDiff ℝ ∞ (fun x => φ x * χ x) := hφ.mul hχ
      have hφ₂ : ContDiff ℝ ∞ (fun x => φ x * (1 - χ x)) := hφ.mul (contDiff_const.sub hχ)
      have hc₁ : HasCompactSupport (fun x => φ x * χ x) := hc.mul_right
      have hc₂ : HasCompactSupport (fun x => φ x * (1 - χ x)) := hc.mul_right
      have ts₁ : tsupport (fun x => φ x * χ x) ⊆ ball q r := by
        refine (tsupport_mul_subset_right (f := φ) (g := (χ : ℂ → ℝ))).trans ?_
        rw [χ.tsupport_eq]
        exact closedBall_subset_ball (by show r / 2 < r; linarith)
      have ts₂ : tsupport (fun x => φ x * (1 - χ x)) ⊆ tsupport φ ∩ (ball q (r / 4))ᶜ := by
        refine closure_minimal (fun x hx => ⟨subset_tsupport φ ?_, ?_⟩)
          ((isClosed_tsupport φ).inter isOpen_ball.isClosed_compl)
        · intro h0; exact hx (by simp [h0])
        · intro hb
          apply hx
          have : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hb)
          simp [this]
      have hS₂ : ∀ x ∈ chargeSet Γ a, x ∈ tsupport (fun x => φ x * (1 - χ x)) → x ∈ S := by
        intro x hxP hx
        have h2 := ts₂ hx
        rcases Finset.mem_insert.1 (hS x hxP h2.1) with rfl | hxS
        · exact absurd (mem_ball_self (by positivity : (0 : ℝ) < r / 4)) h2.2
        · exact hxS
      have e₁ := hloc _ hφ₁ hc₁ ts₁
      have e₂ := ih _ hφ₂ hc₂ hS₂
      have := Torus.ElecId.add hP.locallyIntegrable_gradient hlf hφ₁ hc₁ hφ₂ hc₂ e₁ e₂
      have e : (fun x => φ x * χ x + φ x * (1 - χ x)) = φ := by funext x; ring
      rwa [e] at this
    · refine ih φ hφ hc fun x hxP hx => ?_
      rcases Finset.mem_insert.1 (hS x hxP hx) with rfl | hxS
      · exact absurd hxP hqP
      · exact hxS

/-- **The gradient of a torus potential is an electric field** with charge set the periodic sites. -/
theorem gradient_mem_elec {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) : gradient h ∈ elec (periodicSites Γ a) := by
  have hset : periodicSites Γ a = chargeSet Γ a := by
    ext x; exact mem_periodicSites_iff Γ a
  have hlf : ∀ R : ℝ, (chargeSet Γ a ∩ closedBall (0 : ℂ) R).Finite := fun R => by
    rw [← hset]; exact locallyFiniteSites_periodicSites Γ a 0 R
  refine ⟨fun R => by rw [hset]; exact hlf R, hP.locallyIntegrable_gradient, fun φ hφ hc => ?_⟩
  have hfin : (chargeSet Γ a ∩ tsupport φ).Finite := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
    exact (hlf R).subset fun x hx => ⟨hx.1, hR hx.2⟩
  have := hP.elecId_of_subset hlf hfin.toFinset φ hφ hc
    (fun x hxP hx => hfin.mem_toFinset.2 ⟨hxP, hx⟩)
  rw [hset]
  exact this

end IsTorusPotential

/-- `torusPotential Γ a` is a torus potential. -/
theorem isTorusPotential_torusPotential (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IsTorusPotential Γ a (torusPotential Γ a) :=
  Classical.epsilon_spec (Torus.exists_isTorusPotential Γ hΓ a ha)

/-- **Main theorem.** For a lattice `Γ ⊆ ℂ` of covolume `N` and `N` charges with pairwise distinct
classes modulo `Γ`, the gradient of the torus potential is an electric field with charges
`periodicSites Γ a = {x | ∃ i, x - a i ∈ Γ}`. -/
theorem gradient_torusPotential_mem_elec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ]
    [IsZLattice ℝ Γ] {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    gradient (torusPotential Γ a) ∈ elec (periodicSites Γ a) :=
  (isTorusPotential_torusPotential Γ hΓ a ha).gradient_mem_elec

/-- **Corollary.** `E_tri = ∇ h_tri ∈ Elec(Λ_tri, 1)`: the first conjunct of
`triangularField_spec`. -/
theorem triangularField_mem_elec : triangularField ∈ elec (triangularLattice : Set ℂ) := by
  have hcov : ZLattice.covolume triangularLattice = ((1 : ℕ) : ℝ) := by
    simpa using Torus.covolume_triangularLattice
  have h := gradient_torusPotential_mem_elec triangularLattice hcov (fun _ : Fin 1 => (0 : ℂ))
    (fun i j _ => Subsingleton.elim i j)
  have hset : periodicSites triangularLattice (fun _ : Fin 1 => (0 : ℂ)) =
      (triangularLattice : Set ℂ) := by
    ext x; rw [mem_periodicSites_iff]; simp
  rw [hset] at h
  exact h

end SandierSerfaty

end
