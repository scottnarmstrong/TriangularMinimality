/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.LaplacianComp
public import SandierSerfaty.Torus.ThetaFunction
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The single-charge Green function of a lattice `p (ℤ + ℤ τ)`

For `p ≠ 0` and `Im τ > 0`, `SandierSerfaty.Torus.greenOne p τ z = thetaGreen0 τ (z / p)` is

* periodic under the lattice `p (ℤ + ℤ τ)` (`greenOne_add_period`);
* `C^∞` off the lattice (`contDiffAt_greenOne`), with `Δ = 2π / (‖p‖² Im τ)`, that is `2π / covol`
  (`laplacian_greenOne`);
* logarithmically singular at the lattice points: `greenOne p τ z + log ‖z‖` has a finite limit as
  `z → 0` (`tendsto_greenOne_add_log`).

It is the building block of the torus potential (`SandierSerfaty.Torus.PotentialExists`).
-/

open Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- The real-linear map `z ↦ Im (z / p)`. -/
@[expose] noncomputable def imDiv (p : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.mul ℝ ℂ p⁻¹)

theorem imDiv_apply (p z : ℂ) : imDiv p z = (z / p).im := by
  simp [imDiv, div_eq_inv_mul]

theorem imDiv_sq_add_sq {p : ℂ} (hp : p ≠ 0) :
    imDiv p 1 ^ 2 + imDiv p Complex.I ^ 2 = (‖p‖ ^ 2)⁻¹ := by
  rw [imDiv_apply, imDiv_apply]
  have hn : Complex.normSq p ≠ 0 := (Complex.normSq_pos.2 hp).ne'
  rw [Complex.sq_norm]
  simp only [Complex.div_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  have : Complex.normSq p = p.re * p.re + p.im * p.im := Complex.normSq_apply p
  field_simp
  rw [this]
  ring

/-- The single-charge potential of the lattice `p (ℤ + ℤ τ)`. -/
@[expose] noncomputable def greenOne (p τ z : ℂ) : ℝ := thetaGreen0 τ (z / p)

theorem greenOne_add_period {τ : ℂ} (hτ : 0 < τ.im) {p : ℂ} (hp : p ≠ 0) (z : ℂ) (m n : ℤ) :
    greenOne p τ (z + p * (m + n * τ)) = greenOne p τ z := by
  unfold greenOne
  rw [add_div, mul_div_cancel_left₀ _ hp]
  exact thetaGreen0_add_int_add_int_mul hτ _ m n

theorem greenOne_eq {τ p z : ℂ} (h : theta τ (z / p) ≠ 0) :
    greenOne p τ z = -Real.log ‖theta τ (z / p)‖ + Real.pi / τ.im * imDiv p z ^ 2 +
      Real.pi * imDiv p z := by
  unfold greenOne thetaGreen0 thetaGreen
  simp only [h, ↓reduceIte, imDiv_apply]
  ring

theorem continuous_theta_div (τ : ℂ) (hτ : 0 < τ.im) (p : ℂ) :
    Continuous fun z : ℂ => theta τ (z / p) :=
  ((differentiable_theta hτ).continuous).comp (continuous_id.div_const p)

theorem eventuallyEq_greenOne {τ p z : ℂ} (hτ : 0 < τ.im) (h : theta τ (z / p) ≠ 0) :
    greenOne p τ =ᶠ[𝓝 z] fun x => -Real.log ‖theta τ (x / p)‖ +
      (Real.pi / τ.im * imDiv p x ^ 2 + Real.pi * imDiv p x) := by
  have hopen : IsOpen {x : ℂ | theta τ (x / p) ≠ 0} :=
    isOpen_ne_fun (continuous_theta_div τ hτ p) continuous_const
  filter_upwards [hopen.mem_nhds h] with x hx
  rw [greenOne_eq hx]
  ring

theorem contDiff_theta_div {τ : ℂ} (hτ : 0 < τ.im) (p : ℂ) :
    ContDiff ℝ ∞ fun z : ℂ => theta τ (z / p) := by
  have h : Differentiable ℂ fun z : ℂ => theta τ (z / p) :=
    (differentiable_theta hτ).comp (differentiable_id.div_const p)
  exact (h.contDiff (n := ∞)).restrict_scalars ℝ

theorem contDiffAt_log_norm_theta_div {τ : ℂ} (hτ : 0 < τ.im) (p z : ℂ)
    (h : theta τ (z / p) ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : ℂ => Real.log ‖theta τ (x / p)‖) z := by
  have h1 := (contDiff_theta_div hτ p).contDiffAt (x := z)
  have h2 := h1.norm ℝ h
  exact h2.log (norm_ne_zero_iff.2 h)

/-- The single-charge potential is `C^∞` off the lattice. -/
theorem contDiffAt_greenOne {τ p z : ℂ} (hτ : 0 < τ.im) (h : theta τ (z / p) ≠ 0) :
    ContDiffAt ℝ ∞ (greenOne p τ) z := by
  refine ContDiffAt.congr_of_eventuallyEq ?_ (eventuallyEq_greenOne hτ h)
  have h1 := (contDiffAt_log_norm_theta_div hτ p z h).neg
  have hL := (imDiv p).contDiff (n := ∞) (𝕜 := ℝ)
  have h2 : ContDiffAt ℝ ∞
      (fun x : ℂ => Real.pi / τ.im * imDiv p x ^ 2 + Real.pi * imDiv p x) z :=
    ((hL.pow 2).const_smul (Real.pi / τ.im) |>.add (hL.const_smul Real.pi)).contDiffAt
  exact h1.add h2

theorem iteratedDeriv_two_quad (c b t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => c * s ^ 2 + b * s) t = 2 * c := by
  have h1 : deriv (fun s : ℝ => c * s ^ 2 + b * s) = fun s => 2 * c * s + b := by
    funext s
    have : HasDerivAt (fun s : ℝ => c * s ^ 2 + b * s) (c * (2 * s) + b) s := by
      have := ((hasDerivAt_pow 2 s).const_mul c).add ((hasDerivAt_id' s).const_mul b)
      refine this.congr_deriv ?_
      simp
    rw [this.deriv]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  have : HasDerivAt (fun s : ℝ => 2 * c * s + b) (2 * c) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * c)).add_const b
  exact this.deriv

/-- The Laplacian of the single-charge potential off the lattice is `2π / covol`. -/
theorem laplacian_greenOne {τ p z : ℂ} (hτ : 0 < τ.im) (hp : p ≠ 0) (h : theta τ (z / p) ≠ 0) :
    Δ (greenOne p τ) z = 2 * Real.pi / (‖p‖ ^ 2 * τ.im) := by
  have hc := (InnerProductSpace.laplacian_congr_nhds (eventuallyEq_greenOne hτ h)).eq_of_nhds
  rw [hc]
  have hanal : AnalyticAt ℂ (fun x : ℂ => theta τ (x / p)) z :=
    ((differentiable_theta hτ).comp (differentiable_id.div_const p)).analyticAt z
  have hf1 : InnerProductSpace.HarmonicAt (fun x : ℂ => -Real.log ‖theta τ (x / p)‖) z :=
    (hanal.harmonicAt_log_norm h).neg
  have hP : ContDiff ℝ 2 (fun t : ℝ => Real.pi / τ.im * t ^ 2 + Real.pi * t) := by fun_prop
  have hf2 : ContDiffAt ℝ 2 ((fun t : ℝ => Real.pi / τ.im * t ^ 2 + Real.pi * t) ∘ imDiv p) z :=
    (hP.comp (imDiv p).contDiff).contDiffAt
  have e : (fun x : ℂ => -Real.log ‖theta τ (x / p)‖ +
      (Real.pi / τ.im * imDiv p x ^ 2 + Real.pi * imDiv p x)) =
      (fun x : ℂ => -Real.log ‖theta τ (x / p)‖) +
        ((fun t : ℝ => Real.pi / τ.im * t ^ 2 + Real.pi * t) ∘ imDiv p) := rfl
  rw [e, ContDiffAt.laplacian_add hf1.1 hf2, hf1.2.eq_of_nhds,
    Analysis.laplacian_comp_clm _ _ hP, iteratedDeriv_two_quad, imDiv_sq_add_sq hp]
  have : τ.im ≠ 0 := hτ.ne'
  have : ‖p‖ ≠ 0 := norm_ne_zero_iff.2 hp
  simp only [Pi.zero_apply]
  field_simp
  ring

/-- Logarithmic singularity at the lattice point `0`. -/
theorem tendsto_greenOne_add_log {τ p : ℂ} (hτ : 0 < τ.im) (hp : p ≠ 0) :
    ∃ c : ℝ, Tendsto (fun z : ℂ => greenOne p τ z + Real.log ‖z‖) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨c₀, hc₀⟩ := tendsto_log_norm_theta hτ
  have hmap : Tendsto (fun z : ℂ => z / p) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => z / p) (𝓝 0) (𝓝 (0 / p)) :=
        (continuous_id.div_const p).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [hp] using hz
  have hq : Tendsto (fun z : ℂ => Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z) (𝓝 0)
      (𝓝 0) := by
    have hc : Continuous fun z : ℂ => Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z := by
      fun_prop
    simpa using hc.tendsto 0
  refine ⟨-c₀ + Real.log ‖p‖, ?_⟩
  have hlim : Tendsto (fun z : ℂ => -(Real.log ‖theta τ (z / p)‖ - Real.log ‖z / p‖) +
      (Real.pi / τ.im * imDiv p z ^ 2 + Real.pi * imDiv p z) + Real.log ‖p‖) (𝓝[≠] 0)
      (𝓝 (-c₀ + 0 + Real.log ‖p‖)) :=
    (((hc₀.comp hmap).neg).add (hq.mono_left nhdsWithin_le_nhds)).add tendsto_const_nhds
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmap.eventually (eventually_theta_ne_zero hτ), self_mem_nhdsWithin]
    with z hz hz0
  have hz0' : z ≠ 0 := hz0
  rw [greenOne_eq hz]
  have h1 : ‖z / p‖ ≠ 0 := norm_ne_zero_iff.2 (div_ne_zero hz0' hp)
  have h2 : ‖p‖ ≠ 0 := norm_ne_zero_iff.2 hp
  have h3 : Real.log ‖z‖ = Real.log ‖z / p‖ + Real.log ‖p‖ := by
    rw [← Real.log_mul h1 h2, norm_div, div_mul_cancel₀ _ h2]
  rw [h3]
  ring

end Torus

end SandierSerfaty

end
