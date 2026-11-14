/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Coordinate calculus of the Laplacian on `ℂ`

Preparation for Weyl's lemma (`SandierSerfaty.Analysis.Weyl`) and the removable singularity theorem
(`SandierSerfaty.Analysis.RemovableSingularity`). The Laplacian is Mathlib's
`InnerProductSpace.laplacian` on `ℂ` (real inner product space).

* `Weyl.pd v f` is the directional derivative `∂_v f`, and `Weyl.lap_eq_pd` expresses `Δ f` through it;
* `Weyl.integral_mul_lap_eq`: Green's identity `∫ u Δφ = ∫ (Δu) φ`, for `u` of class `C²` on an open
  set containing the compact set off which `φ` vanishes (no boundary term);
* `Weyl.lap_comp_normSq_sub`: the Laplacian of a radial function `G (‖· - c‖²)`;
* `Weyl.lap_mul`: the product rule for `Δ`.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- The directional derivative `∂_v f` of `f : ℂ → ℝ`. -/
@[expose] noncomputable def pd (v : ℂ) (f : ℂ → ℝ) : ℂ → ℝ := fun x => fderiv ℝ f x v

theorem contDiffAt_pd {f : ℂ → ℝ} {x : ℂ} {n : ℕ} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x) (v : ℂ) :
    ContDiffAt ℝ n (pd v f) x := by
  have h := (hf.fderiv_right (m := n) (by push_cast; exact le_rfl))
  exact h.clm_apply contDiffAt_const

theorem contDiff_pd {f : ℂ → ℝ} {m n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n)
    (v : ℂ) : ContDiff ℝ m (pd v f) := by
  have h := hf.fderiv_right (m := m) hmn
  exact h.clm_apply contDiff_const

theorem pd_pd_eq {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    fderiv ℝ (pd v f) x v = iteratedFDeriv ℝ 2 f x ![v, v] := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : HasFDerivAt (pd v f)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x h1.hasFDerivAt
  rw [h2.fderiv, iteratedFDeriv_two_apply]
  simp

/-- The Laplacian on `ℂ` as a sum of two pure second directional derivatives. -/
theorem lap_eq_pd {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = pd 1 (pd 1 f) x + pd Complex.I (pd Complex.I f) x := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  show iteratedFDeriv ℝ 2 f x ![1, 1] + iteratedFDeriv ℝ 2 f x ![Complex.I, Complex.I] = _
  rw [← pd_pd_eq hf, ← pd_pd_eq hf]
  rfl

theorem pd_eq_zero_of_notMem {φ : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hφ0 : ∀ x ∉ K, φ x = 0) (v : ℂ) : ∀ x ∉ K, pd v φ x = 0 := by
  intro x hx
  have hx' : x ∉ tsupport φ := fun h => hx ((closure_minimal (fun y hy => by
    by_contra h; exact hy (hφ0 y h)) hK.isClosed : tsupport φ ⊆ K) h)
  have h2 : φ =ᶠ[nhds x] 0 := by
    rw [notMem_tsupport_iff_eventuallyEq] at hx'; exact hx'
  simp [pd, h2.fderiv_eq]

/-- The Laplacian vanishes outside the topological support. -/
theorem lap_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport φ) : Δ φ x = 0 := by
  have h2 : φ =ᶠ[nhds x] 0 := by
    rw [notMem_tsupport_iff_eventuallyEq] at hx; exact hx
  have h3 := (laplacian_congr_nhds h2).eq_of_nhds
  rw [h3]
  exact congrFun (laplacian_const (E := ℂ) (c := (0 : ℝ))) x

theorem integrable_mul_of_supp {F G : ℂ → ℝ} {K W : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hF : ContinuousOn F W) (hG : Continuous G) (hG0 : ∀ x ∉ K, G x = 0) :
    Integrable (fun x => F x * G x) := by
  have h1 : IntegrableOn (fun x => F x * G x) K :=
    ((hF.mono hKW).mul hG.continuousOn).integrableOn_compact hK
  exact h1.integrable_of_forall_notMem_eq_zero (fun x hx => by simp [hG0 x hx])

theorem integral_mul_pd_eq_neg {f g : ℂ → ℝ} {W K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hW : IsOpen W) (hf : ContDiffOn ℝ 1 f W) (hg : ContDiff ℝ 1 g)
    (hg0 : ∀ x ∉ K, g x = 0) (v : ℂ) :
    ∫ x, f x * pd v g x = -∫ x, pd v f x * g x := by
  have hg0' : tsupport g ⊆ K := closure_minimal (fun x hx => by
    by_contra h; exact hx (hg0 x h)) hK.isClosed
  have hgd : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x :=
    fun x _ => hg.differentiable (by norm_num) x
  have hfd : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hW.mem_nhds (hKW (hg0' hx)))).differentiableAt (by norm_num)
  have hfc : ContinuousOn (pd v f) W := by
    intro x hx
    exact (contDiffAt_pd (n := 0) (by simpa using hf.contDiffAt (hW.mem_nhds hx))
      v).continuousAt.continuousWithinAt
  have hgc : Continuous (pd v g) := (contDiff_pd (m := 0) hg (by norm_num) v).continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_supp hK hKW hfc hg.continuous hg0)
    (integrable_mul_of_supp hK hKW (hf.continuousOn) hgc (pd_eq_zero_of_notMem hK hg0 v))
    (integrable_mul_of_supp hK hKW (hf.continuousOn) hg.continuous hg0) hfd hgd

theorem integral_mul_pd_pd {u φ : ℂ → ℝ} {W K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hW : IsOpen W) (hu : ContDiffOn ℝ 2 u W) (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ x ∉ K, φ x = 0) (v : ℂ) :
    ∫ x, u x * pd v (pd v φ) x = ∫ x, pd v (pd v u) x * φ x := by
  have hφ1 : ContDiff ℝ 1 (pd v φ) := contDiff_pd (m := 1) hφ (by norm_num) v
  have hu1 : ContDiffOn ℝ 1 u W := hu.of_le (by norm_num)
  have hpu : ContDiffOn ℝ 1 (pd v u) W := by
    intro x hx
    exact (contDiffAt_pd (n := 1) (by simpa using hu.contDiffAt (hW.mem_nhds hx))
      v).contDiffWithinAt
  rw [integral_mul_pd_eq_neg hK hKW hW hu1 hφ1 (pd_eq_zero_of_notMem hK hφ0 v) v,
    integral_mul_pd_eq_neg hK hKW hW hpu (hφ.of_le (by norm_num)) hφ0 v]
  simp

/-- **Green's identity without boundary term.** If `u` is `C²` on an open set `W` and `φ` is `C²`
and vanishes off a compact subset `K` of `W`, then `∫ u Δφ = ∫ (Δu) φ`. -/
theorem integral_mul_lap_eq {u φ : ℂ → ℝ} {W K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hW : IsOpen W) (hu : ContDiffOn ℝ 2 u W) (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ x ∉ K, φ x = 0) :
    ∫ x, u x * Δ φ x = ∫ x, Δ u x * φ x := by
  have hL : ∀ x, Δ φ x = pd 1 (pd 1 φ) x + pd Complex.I (pd Complex.I φ) x :=
    fun x => lap_eq_pd (hφ.contDiffAt)
  have hR : ∀ x, Δ u x * φ x =
      pd 1 (pd 1 u) x * φ x + pd Complex.I (pd Complex.I u) x * φ x := by
    intro x
    by_cases hx : x ∈ K
    · rw [lap_eq_pd (hu.contDiffAt (hW.mem_nhds (hKW hx)))]; ring
    · rw [hφ0 x hx]; simp
  have hpd : ∀ v : ℂ, Continuous (pd v (pd v φ)) ∧ ∀ x ∉ K, pd v (pd v φ) x = 0 := by
    intro v
    have h1 : ContDiff ℝ 1 (pd v φ) := contDiff_pd (m := 1) hφ (by norm_num) v
    exact ⟨(contDiff_pd (m := 0) h1 (by norm_num) v).continuous,
      pd_eq_zero_of_notMem hK (pd_eq_zero_of_notMem hK hφ0 v) v⟩
  have hpu : ∀ v : ℂ, ContinuousOn (pd v (pd v u)) W := by
    intro v x hx
    have h1 : ContDiffAt ℝ 1 (pd v u) x :=
      contDiffAt_pd (n := 1) (by simpa using hu.contDiffAt (hW.mem_nhds hx)) v
    exact (contDiffAt_pd (n := 0) (by simpa using h1) v).continuousAt.continuousWithinAt
  simp_rw [hL, hR, mul_add]
  rw [integral_add, integral_add]
  · rw [integral_mul_pd_pd hK hKW hW hu hφ hφ0 1,
      integral_mul_pd_pd hK hKW hW hu hφ hφ0 Complex.I]
  · exact integrable_mul_of_supp hK hKW (hpu 1) hφ.continuous hφ0
  · exact integrable_mul_of_supp hK hKW (hpu Complex.I) hφ.continuous hφ0
  · exact integrable_mul_of_supp hK hKW (hu.continuousOn) (hpd 1).1 (hpd 1).2
  · exact integrable_mul_of_supp hK hKW (hu.continuousOn) (hpd Complex.I).1 (hpd Complex.I).2

/-! ### Radial functions of the form `G (‖z - c‖²)` -/

theorem hasFDerivAt_normSq_sub (c y : ℂ) :
    HasFDerivAt (fun z : ℂ => ‖z - c‖ ^ 2) (2 • (innerSL ℝ (y - c))) y := by
  have h := ((hasFDerivAt_id y).sub_const c).norm_sq
  simpa using h

theorem hasFDerivAt_inner_sub (c v y : ℂ) :
    HasFDerivAt (fun z : ℂ => inner ℝ v (z - c)) (innerSL ℝ v) y := by
  have := (innerSL ℝ v).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const c)
  rw [ContinuousLinearMap.comp_id] at this
  exact this

theorem pd_comp_normSq {G : ℝ → ℝ} (hG : Differentiable ℝ G) (c v : ℂ) :
    pd v (fun z : ℂ => G (‖z - c‖ ^ 2)) =
      fun y => deriv G (‖y - c‖ ^ 2) * (2 * inner ℝ v (y - c)) := by
  funext y
  have h := (hG (‖y - c‖ ^ 2)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_normSq_sub c y)
  simp only [pd]
  have := h.fderiv
  simp only [Function.comp_def] at this
  rw [this]
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul, innerSL_apply_apply]
  rw [real_inner_comm]; ring

theorem pd_pd_comp_normSq {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (c v y : ℂ) :
    pd v (pd v (fun z : ℂ => G (‖z - c‖ ^ 2))) y =
      deriv (deriv G) (‖y - c‖ ^ 2) * (2 * inner ℝ v (y - c)) * (2 * inner ℝ v (y - c))
        + deriv G (‖y - c‖ ^ 2) * (2 * inner ℝ v v) := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hG2 : Differentiable ℝ (deriv G) := by
    have h := (contDiff_succ_iff_deriv (n := 1)).1
      (show ContDiff ℝ ((1 : ℕ) + 1 : ℕ) G by exact_mod_cast hG)
    exact (h.2.2).differentiable (by norm_num)
  rw [pd_comp_normSq hG1 c v]
  simp only [pd]
  have hq := hasFDerivAt_normSq_sub c y
  have hin := hasFDerivAt_inner_sub c v y
  have hd : HasFDerivAt (fun z : ℂ => deriv G (‖z - c‖ ^ 2))
      (deriv (deriv G) (‖y - c‖ ^ 2) • (2 • (innerSL ℝ (y - c)))) y :=
    (hG2 (‖y - c‖ ^ 2)).hasDerivAt.comp_hasFDerivAt (h₂ := deriv G) y hq
  have hprod : HasFDerivAt (fun z : ℂ => deriv G (‖z - c‖ ^ 2) * (2 * inner ℝ v (z - c))) _ y :=
    hd.mul (hin.const_mul 2)
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, two_smul, smul_eq_mul, innerSL_apply_apply]
  rw [real_inner_comm (y - c) v]
  ring

theorem contDiff_comp_normSq_sub {G : ℝ → ℝ} {n : ℕ∞ω} (hG : ContDiff ℝ n G) (c : ℂ) :
    ContDiff ℝ n (fun z : ℂ => G (‖z - c‖ ^ 2)) :=
  hG.comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

/-- **Laplacian of a radial function.** `Δ (G (‖· - c‖²)) = 4 s G'' (s) + 4 G' (s)`, `s = ‖y - c‖²`. -/
theorem lap_comp_normSq_sub {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (c y : ℂ) :
    Δ (fun z : ℂ => G (‖z - c‖ ^ 2)) y =
      4 * ‖y - c‖ ^ 2 * deriv (deriv G) (‖y - c‖ ^ 2) + 4 * deriv G (‖y - c‖ ^ 2) := by
  rw [lap_eq_pd (contDiff_comp_normSq_sub hG c).contDiffAt, pd_pd_comp_normSq hG,
    pd_pd_comp_normSq hG]
  have h1 : inner ℝ (1 : ℂ) (y - c) = (y - c).re := by simp [Complex.inner]
  have h2 : inner ℝ Complex.I (y - c) = (y - c).im := by simp [Complex.inner]
  have h3 : inner ℝ (1 : ℂ) 1 = 1 := by simp
  have h4 : inner ℝ Complex.I Complex.I = 1 := by simp
  have h5 : ‖y - c‖ ^ 2 = (y - c).re ^ 2 + (y - c).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [h1, h2, h3, h4, h5]
  ring

/-! ### Product rule -/

theorem pd_mul_eventually {f g : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (v : ℂ) :
    pd v (fun y => f y * g y) =ᶠ[𝓝 x] fun y => pd v f y * g y + f y * pd v g y := by
  filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
  simp only [pd]
  rw [fderiv_fun_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem pd_pd_mul {f g : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v : ℂ) :
    pd v (pd v (fun y => f y * g y)) x =
      pd v (pd v f) x * g x + 2 * (pd v f x * pd v g x) + f x * pd v (pd v g) x := by
  have hf1 : ContDiffAt ℝ 1 (pd v f) x := contDiffAt_pd (n := 1) (by simpa using hf) v
  have hg1 : ContDiffAt ℝ 1 (pd v g) x := contDiffAt_pd (n := 1) (by simpa using hg) v
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hf1d : DifferentiableAt ℝ (pd v f) x := hf1.differentiableAt (by norm_num)
  have hg1d : DifferentiableAt ℝ (pd v g) x := hg1.differentiableAt (by norm_num)
  have hpf : DifferentiableAt ℝ (fun y => pd v f y * g y) x := hf1d.mul hgd
  have hpg : DifferentiableAt ℝ (fun y => f y * pd v g y) x := hfd.mul hg1d
  simp only [pd]
  rw [(pd_mul_eventually hf hg v).fderiv_eq]
  rw [fderiv_fun_add hpf hpg, fderiv_fun_mul hf1d hgd, fderiv_fun_mul hfd hg1d]
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [pd]
  ring

/-- **Product rule for the Laplacian.** -/
theorem lap_mul {f g : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y => f y * g y) x = Δ f x * g x + f x * Δ g x
      + 2 * (pd 1 f x * pd 1 g x + pd Complex.I f x * pd Complex.I g x) := by
  rw [lap_eq_pd (hf.mul hg), lap_eq_pd hf, lap_eq_pd hg, pd_pd_mul hf hg, pd_pd_mul hf hg]
  ring

end SandierSerfaty.Weyl

end
