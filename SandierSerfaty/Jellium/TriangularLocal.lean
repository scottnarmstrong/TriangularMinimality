/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Analysis.RemovableSingularity
public import SandierSerfaty.Statements.Jellium.Defs.TruncField
public import SandierSerfaty.Statements.Jellium.Defs.TruncLog

/-!
# The truncated field of a one-point torus potential

Let `Γ ⊆ ℂ` be a lattice all of whose nonzero points have norm `≥ 1`, and `h` a torus potential of
the single charge at `0` (`IsTorusPotential Γ (fun _ : Fin 1 => 0) h`). With the radius `η = ¼` at every
point, the truncated field `E_η = ∇h - ∑_{p ∈ Γ} ∇f_η(· - p)` (`SandierSerfaty.truncField`) is
`SandierSerfaty.Torus.tField`. This file establishes its local structure:

* `tField_add`: `Γ`-periodicity;
* `tField_of_far`: `E_η x = ∇h x` if `‖x - γ‖ > η` for every `γ ∈ Γ`;
* `exists_local_form_ball`: `h = v - log ‖·‖` on `B(0,1) \ {0}` with `v` smooth on `B(0,1)`, `Δ v = 2π`;
* `tField_eq_gradient`: `E_η x = ∇v x` for `0 < ‖x‖ < η`;
* `norm_sq_gradient_eq`: `‖∇h x‖² = ‖∇v x‖² - 2 ‖x‖⁻² ∂v(x)[x] + ‖x‖⁻²` on `B(0,1) \ {0}`.
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- The single charge at the origin. -/
@[expose] def zeroCharge : Fin 1 → ℂ := fun _ => 0

/-- The truncated field of `h` for the lattice `Γ` with radius `¼` at every point. -/
@[expose] noncomputable def tField (Γ : Submodule ℤ ℂ) (h : ℂ → ℝ) : ℂ → ℂ :=
  truncField (Γ : Set ℂ) (fun _ => (1 / 4 : ℝ)) (gradient h)

/-! ### Gradient calculus -/

theorem gradient_congr_nhds {f g : ℂ → ℝ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) :
    gradient f x = gradient g x := by
  simp only [gradient, h.fderiv_eq]

theorem toDual_symm_smul_innerSL (c : ℝ) (y : ℂ) :
    (toDual ℝ ℂ).symm (c • innerSL ℝ y) = c • y := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext w
  simp [toDual_apply_apply]
  ring

theorem gradient_truncLog_of_gt {η : ℝ} (hη : 0 < η) {y : ℂ} (hy : η < ‖y‖) :
    gradient (truncLog η) y = 0 := by
  have hev : truncLog η =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    have hz' : η < ‖z‖ := hz
    unfold truncLog
    have : Real.log η < Real.log ‖z‖ := Real.log_lt_log hη hz'
    exact max_eq_right (by linarith)
  rw [gradient_congr_nhds hev]
  simp [gradient]

theorem gradient_truncLog_of_lt {η : ℝ} {y : ℂ} (hy0 : 0 < ‖y‖) (hy : ‖y‖ < η) :
    gradient (truncLog η) y = -((‖y‖ ^ 2)⁻¹ : ℝ) • y := by
  have hη : 0 < η := hy0.trans hy
  have hyne : y ≠ 0 := norm_pos_iff.1 hy0
  have hev : truncLog η =ᶠ[𝓝 y] fun z => Real.log η - Real.log ‖z - 0‖ := by
    filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hy0, hy⟩] with z hz
    have h1 : 0 < ‖z‖ := hz.1
    have h2 : ‖z‖ < η := hz.2
    unfold truncLog
    have : Real.log ‖z‖ ≤ Real.log η := Real.log_le_log h1 h2.le
    rw [sub_zero, max_eq_left (by linarith)]
    ring
  have hd := hasFDerivAt_log_norm_sub (p := 0) hyne
  rw [gradient_congr_nhds hev]
  simp only [gradient]
  have hh : HasFDerivAt (fun z : ℂ => Real.log η - Real.log ‖z - 0‖)
      (0 - (‖y - 0‖ ^ 2)⁻¹ • innerSL ℝ (y - 0)) y := (hasFDerivAt_const (Real.log η) y).sub hd
  rw [hh.fderiv, zero_sub, sub_zero, map_neg, toDual_symm_smul_innerSL]
  simp

/-! ### Periodicity and the formulas for the truncated field -/

section Lattice

variable {Γ : Submodule ℤ ℂ}

theorem bijOn_sub (γ : ℂ) (hγ : γ ∈ Γ) :
    BijOn (fun p : ℂ => p - γ) (Γ : Set ℂ) (Γ : Set ℂ) :=
  ⟨fun p hp => Γ.sub_mem hp hγ, fun p _ q _ h => by simpa using h,
    fun q hq => ⟨q + γ, Γ.add_mem hq hγ, by simp⟩⟩

theorem gradient_add_periodic {h : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) {γ : ℂ}
    (hγ : γ ∈ Γ) (x : ℂ) : gradient h (x + γ) = gradient h x := by
  have e : (fun y => h (y + γ)) = h := funext (hper γ hγ)
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := h) (x := x) γ
  rw [e] at this
  simp only [gradient]
  rw [this]

theorem finsum_mem_eq_single' {s : Set ℂ} {g : ℂ → ℂ} {a : ℂ} (ha : a ∈ s)
    (h : ∀ x ∈ s, x ≠ a → g x = 0) : ∑ᶠ x ∈ s, g x = g a := by
  rw [finsum_eq_single (fun x => ∑ᶠ (_ : x ∈ s), g x) a]
  · simp [ha]
  · intro x hx
    by_cases hxs : x ∈ s
    · simp [hxs, h x hxs hx]
    · simp [hxs]

theorem tField_add {h : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) {γ : ℂ} (hγ : γ ∈ Γ)
    (x : ℂ) : tField Γ h (x + γ) = tField Γ h x := by
  unfold tField truncField
  rw [gradient_add_periodic hper hγ x]
  congr 1
  refine finsum_mem_eq_of_bijOn (fun p => p - γ) (bijOn_sub γ hγ) (fun p _ => ?_)
  show gradient (truncLog (1 / 4)) (x + γ - p) = gradient (truncLog (1 / 4)) (x - (p - γ))
  rw [show x + γ - p = x - (p - γ) by ring]

theorem tField_of_far {h : ℂ → ℝ} {x : ℂ} (hx : ∀ γ ∈ Γ, (1 / 4 : ℝ) < ‖x - γ‖) :
    tField Γ h x = gradient h x := by
  unfold tField truncField
  rw [finsum_mem_eq_zero_of_forall_eq_zero
    (fun p hp => gradient_truncLog_of_gt (by norm_num) (hx p hp)), sub_zero]

theorem tField_of_near (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h : ℂ → ℝ} {x : ℂ} (hx0 : 0 < ‖x‖)
    (hx : ‖x‖ < 1 / 4) :
    tField Γ h x = gradient h x + ((‖x‖ ^ 2)⁻¹ : ℝ) • x := by
  unfold tField truncField
  have hsingle : ∑ᶠ p ∈ (Γ : Set ℂ), gradient (truncLog (1 / 4)) (x - p) =
      gradient (truncLog (1 / 4)) (x - 0) := by
    refine finsum_mem_eq_single' (SetLike.mem_coe.2 Γ.zero_mem) (fun p hp hp0 => ?_)
    refine gradient_truncLog_of_gt (by norm_num) ?_
    have h1 := hmin p hp hp0
    have h2 := norm_sub_norm_le p x
    rw [norm_sub_rev] at h2
    linarith
  show gradient h x - ∑ᶠ p ∈ (Γ : Set ℂ), gradient (truncLog (1 / 4)) (x - p) = _
  rw [hsingle, sub_zero, gradient_truncLog_of_lt hx0 hx, neg_smul, sub_neg_eq_add]

theorem mem_chargeSet_zero {x : ℂ} : x ∈ chargeSet Γ zeroCharge ↔ x ∈ Γ := by
  simp [chargeSet, zeroCharge]

/-- **Local form on the unit ball.** If the nonzero lattice points have norm `≥ 1`, a torus potential
of the charge at `0` is `v - log ‖·‖` on `B(0,1) \ {0}` with `v` smooth on `B(0,1)` and `Δ v = 2π`. -/
theorem exists_local_form_ball [DiscreteTopology Γ] (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h : ℂ → ℝ}
    (hP : IsTorusPotential Γ zeroCharge h) :
    ∃ v : ℂ → ℝ, ContDiffOn ℝ ∞ v (ball 0 1) ∧ (∀ x ∈ ball (0 : ℂ) 1, Δ v x = 2 * Real.pi) ∧
      ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → h x = v x - Real.log ‖x‖ := by
  have h0 : (0 : ℂ) ∈ chargeSet Γ zeroCharge := mem_chargeSet_zero.2 Γ.zero_mem
  obtain ⟨c, hc⟩ := hP.exists_tendsto_of_mem_chargeSet h0
  have hbd : ∀ᶠ y in 𝓝[≠] (0 : ℂ), |h y + Real.log ‖y - 0‖| ≤ ‖c‖ + 1 := by
    have := (hc.norm).eventually (eventually_lt_nhds (a := ‖c‖) (b := ‖c‖ + 1) (by linarith))
    filter_upwards [this] with y hy
    exact hy.le
  have hnot : ∀ y ∈ ball (0 : ℂ) 1, y ≠ 0 → y ∉ chargeSet Γ zeroCharge := fun y hy hy0 hmem => by
    rw [mem_chargeSet_zero] at hmem
    have := hmin y hmem hy0
    rw [mem_ball_zero_iff] at hy; linarith
  have hopen := isOpen_notMem_chargeSet Γ zeroCharge
  have hcd : ∀ y ∈ ball (0 : ℂ) 1 \ {0}, ContDiffAt ℝ ∞ h y := fun y hy =>
    hP.2.1.contDiffAt (hopen.mem_nhds (notMem_chargeSet_iff.1 (hnot y hy.1 hy.2)))
  have hlog : ∀ y ∈ ball (0 : ℂ) 1 \ {0}, ContDiffAt ℝ ∞ (fun z : ℂ => Real.log ‖z - 0‖) y := by
    intro y hy
    have hxp : y - 0 ≠ 0 := by simpa using hy.2
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z - 0‖) y :=
      (contDiffAt_id.sub contDiffAt_const).norm ℝ hxp
    exact h1.log (norm_ne_zero_iff.2 hxp)
  have hu : ContDiffOn ℝ 2 (fun y => h y + Real.log ‖y - 0‖) (ball (0 : ℂ) 1 \ {0}) := fun y hy =>
    (((hcd y hy).add (hlog y hy)).of_le (by norm_num)).contDiffWithinAt
  have hΔ : ∀ y ∈ ball (0 : ℂ) 1 \ {0}, Δ (fun z => h z + Real.log ‖z - 0‖) y = 2 * Real.pi := by
    intro y hy
    have e : (fun z => h z + Real.log ‖z - 0‖) = h + fun z : ℂ => Real.log ‖z - 0‖ := rfl
    rw [e, ContDiffAt.laplacian_add ((hcd y hy).of_le (by norm_num))
      ((hlog y hy).of_le (by norm_num)),
      hP.2.2.1 y (notMem_chargeSet_iff.1 (hnot y hy.1 hy.2)),
      laplacian_log_norm_sub (p := 0) (by simpa using hy.2), add_zero]
  obtain ⟨v, hv, hveq, hvΔ⟩ := Weyl.removable_singularity isOpen_ball (mem_ball_self one_pos)
    (2 * Real.pi) hu hΔ ⟨‖c‖ + 1, by filter_upwards [hbd] with y hy using hy⟩
  refine ⟨v, hv, hvΔ, fun x hx hx0 => ?_⟩
  have := hveq ⟨hx, hx0⟩
  simp only [sub_zero] at this
  linarith

theorem gradient_eq_of_local {h v : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (hloc : ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → h x = v x - Real.log ‖x‖) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1) (hx0 : x ≠ 0) :
    gradient h x = gradient v x - ((‖x‖ ^ 2)⁻¹ : ℝ) • x := by
  have := fderiv_eq_of_eq_sub_log (p := 0) hv (fun y hy hyp => by
    simpa using hloc y hy hyp) hx hx0
  simp only [gradient, this, sub_zero, map_sub, toDual_symm_smul_innerSL]

/-- On `B(0,η) \ {0}` the truncated field is the gradient of the smooth part `v`. -/
theorem tField_eq_gradient (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h v : ℂ → ℝ}
    (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (hloc : ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → h x = v x - Real.log ‖x‖) {x : ℂ} (hx0 : x ≠ 0)
    (hx : ‖x‖ < 1 / 4) : tField Γ h x = gradient v x := by
  have hxb : x ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  rw [tField_of_near hmin (norm_pos_iff.2 hx0) hx, gradient_eq_of_local hv hloc hxb hx0]
  simp

/-- `‖∇h‖² = ‖∇v‖² - 2 ‖x‖⁻² ∂v(x)[x] + ‖x‖⁻²` on `B(0,1) \ {0}`. -/
theorem norm_sq_gradient_eq {h v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (hloc : ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → h x = v x - Real.log ‖x‖) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1) (hx0 : x ≠ 0) :
    ‖gradient h x‖ ^ 2 =
      ‖gradient v x‖ ^ 2 - 2 * ((‖x‖ ^ 2)⁻¹ * fderiv ℝ v x x) + (‖x‖ ^ 2)⁻¹ := by
  rw [gradient_eq_of_local hv hloc hx hx0, norm_sub_sq_real, real_inner_smul_right,
    inner_gradient_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx0)
  field_simp

end Lattice

end Torus

end SandierSerfaty

end
