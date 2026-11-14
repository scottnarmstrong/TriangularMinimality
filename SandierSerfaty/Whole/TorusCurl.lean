/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.Regularity
public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Jellium.TriangularLocal
public import SandierSerfaty.Geometry.LatticeCount
public import SandierSerfaty.Statements.Whole.Defs.PaperTriangularField

/-!
# The paper's triangular field is admissible (first conjunct of `paperTriangularField_spec`)

**Theorem** (`isAdmissibleField_paperTriangularField`). `E_△ = -∇h_△ ∈ 𝒜₁` with `Λ = Λ_△`.

The divergence equation is `triangularField_mem_elec` (with the sign of `E_△`); the new point is
`curl ∇h = 0` weakly for a torus potential `h` (`IsTorusPotential.integral_inner_gradient_I_gradient`):
away from the charges `h` is smooth and `∫ ⟪∇h, i∇φ⟫ = ∫ (∂₂∂₁h - ∂₁∂₂h) φ = 0` (integration by parts);
near a charge `p`, `∇h = ∇v - κ(· - p)` with `v` smooth and `curl κ = 0` weakly
(`Whole.integral_inner_kernel_I_gradient`); a test function is split by smooth bumps, one charge at a
time, as in `IsTorusPotential.elecId_of_subset`.
-/

open MeasureTheory Filter Topology Metric Set InnerProductSpace
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Whole

theorem pd_pd_comm_at {ψ : ℂ → ℝ} {x : ℂ} (h2 : ContDiffAt ℝ 2 ψ x) :
    Weyl.pd Complex.I (Weyl.pd 1 ψ) x = Weyl.pd 1 (Weyl.pd Complex.I ψ) x := by
  have hs := ContDiffAt.isSymmSndFDerivAt h2 (by simp)
  show fderiv ℝ (fun y => fderiv ℝ ψ y 1) x Complex.I =
    fderiv ℝ (fun y => fderiv ℝ ψ y Complex.I) x 1
  rw [Analysis.fderiv_fderiv_apply h2, Analysis.fderiv_fderiv_apply h2]
  exact hs Complex.I 1

/-- **Weak curl of a smooth gradient.** If `u` is `C²` on an open set `W` and `φ` is `C²` and vanishes
off a compact subset of `W`, then `∫ ⟪∇u, i∇φ⟫ = 0`. -/
theorem integral_inner_gradient_I_gradient_eq_zero {u φ : ℂ → ℝ} {W K : Set ℂ} (hK : IsCompact K)
    (hKW : K ⊆ W) (hW : IsOpen W) (hu : ContDiffOn ℝ 2 u W) (hφ : ContDiff ℝ 2 φ)
    (hφ0 : ∀ x ∉ K, φ x = 0) :
    ∫ x, inner ℝ (gradient u x) (Complex.I * gradient φ x) = 0 := by
  have hu1 : ContDiffOn ℝ 1 u W := hu.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hpu : ∀ v : ℂ, ContDiffOn ℝ 1 (Weyl.pd v u) W := by
    intro v x hx
    exact (Weyl.contDiffAt_pd (n := 1) (by simpa using hu.contDiffAt (hW.mem_nhds hx))
      v).contDiffWithinAt
  have hpt : ∀ x, inner ℝ (gradient u x) (Complex.I * gradient φ x) =
      -(Weyl.pd 1 u x * Weyl.pd Complex.I φ x) + Weyl.pd Complex.I u x * Weyl.pd 1 φ x := by
    intro x
    rw [inner_I_mul_eq_re_im, gradient_re_eq_pd, gradient_im_eq_pd, gradient_re_eq_pd,
      gradient_im_eq_pd]
  have i1 : Integrable fun x => Weyl.pd 1 u x * Weyl.pd Complex.I φ x :=
    Weyl.integrable_mul_of_supp hK hKW (Torus.continuousOn_pd hW hu1 1)
      (Weyl.contDiff_pd (m := 0) hφ1 (by norm_num) Complex.I).continuous
      (Weyl.pd_eq_zero_of_notMem hK hφ0 Complex.I)
  have i2 : Integrable fun x => Weyl.pd Complex.I u x * Weyl.pd 1 φ x :=
    Weyl.integrable_mul_of_supp hK hKW (Torus.continuousOn_pd hW hu1 Complex.I)
      (Weyl.contDiff_pd (m := 0) hφ1 (by norm_num) 1).continuous
      (Weyl.pd_eq_zero_of_notMem hK hφ0 1)
  have e1 := Weyl.integral_mul_pd_eq_neg hK hKW hW (hpu 1) hφ1 hφ0 Complex.I
  have e2 := Weyl.integral_mul_pd_eq_neg hK hKW hW (hpu Complex.I) hφ1 hφ0 1
  have hsym : ∫ x, Weyl.pd Complex.I (Weyl.pd 1 u) x * φ x =
      ∫ x, Weyl.pd 1 (Weyl.pd Complex.I u) x * φ x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K
    · simp only
      rw [pd_pd_comm_at (hu.contDiffAt (hW.mem_nhds (hKW hx)))]
    · simp [hφ0 x hx]
  simp_rw [hpt]
  rw [integral_add (f := fun x => -(Weyl.pd 1 u x * Weyl.pd Complex.I φ x)) i1.neg i2,
    integral_neg, e1, e2, hsym]
  ring

/-- The weak curl identity `∫ ⟪E, i∇φ⟫ = 0` for the test function `φ`. -/
@[expose] def CurlId (E : ℂ → ℂ) (φ : ℂ → ℝ) : Prop :=
  ∫ x, inner ℝ (E x) (Complex.I * gradient φ x) = 0

theorem CurlId.add {E : ℂ → ℂ} (hE : LocallyIntegrable E volume) {φ₁ φ₂ : ℂ → ℝ}
    (h₁ : ContDiff ℝ ∞ φ₁) (c₁ : HasCompactSupport φ₁) (h₂ : ContDiff ℝ ∞ φ₂)
    (c₂ : HasCompactSupport φ₂) (e₁ : CurlId E φ₁) (e₂ : CurlId E φ₂) :
    CurlId E (fun x => φ₁ x + φ₂ x) := by
  have d₁ : Differentiable ℝ φ₁ := h₁.differentiable (by simp)
  have d₂ : Differentiable ℝ φ₂ := h₂.differentiable (by simp)
  have hg : ∀ x, gradient (fun y => φ₁ y + φ₂ y) x = gradient φ₁ x + gradient φ₂ x := by
    intro x
    simp only [gradient]
    rw [fderiv_fun_add (d₁ x) (d₂ x), map_add]
  have i₁ := integrable_inner_of_locallyIntegrable hE (continuous_I_mul_gradient (h₁.of_le (by simp)))
    (hasCompactSupport_I_mul_gradient c₁)
  have i₂ := integrable_inner_of_locallyIntegrable hE (continuous_I_mul_gradient (h₂.of_le (by simp)))
    (hasCompactSupport_I_mul_gradient c₂)
  unfold CurlId at *
  simp_rw [hg, mul_add, inner_add_right]
  rw [integral_add i₁ i₂, e₁, e₂, add_zero]

end Whole

namespace IsTorusPotential

open Torus Whole

theorem curlId_of_subset_compl {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hK : tsupport φ ⊆ {x : ℂ | ∀ i, x - a i ∉ Γ}) :
    CurlId (gradient h) φ :=
  integral_inner_gradient_I_gradient_eq_zero hc hK (isOpen_notMem_chargeSet Γ a)
    (hP.2.1.of_le (by norm_num)) (hφ.of_le (by norm_num)) fun _ hx =>
      image_eq_zero_of_notMem_tsupport hx

theorem exists_radius_curlId {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) {p : ℂ} (hp : p ∈ chargeSet Γ a) :
    ∃ r > 0, ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ ball p r →
      CurlId (gradient h) φ := by
  obtain ⟨r, hr, v, hv, -, hloc⟩ := hP.exists_local_form hp
  refine ⟨r, hr, fun φ hφ hc hsub => ?_⟩
  have hK : IsCompact (tsupport φ) := hc
  have hφ0 : ∀ x ∉ tsupport φ, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hA := integral_inner_gradient_I_gradient_eq_zero hK hsub isOpen_ball (hv.of_le (by norm_num))
    (hφ.of_le (by norm_num)) hφ0
  have hB := integral_inner_kernel_I_gradient hφ1 hc p
  have hG := continuous_I_mul_gradient hφ1
  have hGc := hasCompactSupport_I_mul_gradient hc
  have iA : Integrable fun x => inner ℝ (gradient v x) (Complex.I * gradient φ x) := by
    have hpt : ∀ x, inner ℝ (gradient v x) (Complex.I * gradient φ x) =
        -(Weyl.pd 1 v x * Weyl.pd Complex.I φ x) + Weyl.pd Complex.I v x * Weyl.pd 1 φ x := by
      intro x
      rw [inner_I_mul_eq_re_im, gradient_re_eq_pd, gradient_im_eq_pd, gradient_re_eq_pd,
        gradient_im_eq_pd]
    simp_rw [hpt]
    have hv1 : ContDiffOn ℝ 1 v (ball p r) := hv.of_le (by norm_num)
    exact (Weyl.integrable_mul_of_supp hK hsub (Torus.continuousOn_pd isOpen_ball hv1 1)
      (Weyl.contDiff_pd (m := 0) hφ1 (by norm_num) Complex.I).continuous
      (Weyl.pd_eq_zero_of_notMem hK hφ0 Complex.I)).neg.add
      (Weyl.integrable_mul_of_supp hK hsub (Torus.continuousOn_pd isOpen_ball hv1 Complex.I)
        (Weyl.contDiff_pd (m := 0) hφ1 (by norm_num) 1).continuous
        (Weyl.pd_eq_zero_of_notMem hK hφ0 1))
  have iB := integrable_inner_of_locallyIntegrable (locallyIntegrable_kernel_sub p) hG hGc
  have hpt : ∀ x, x ≠ p → inner ℝ (gradient h x) (Complex.I * gradient φ x) =
      inner ℝ (gradient v x) (Complex.I * gradient φ x) -
        inner ℝ (kernel (x - p)) (Complex.I * gradient φ x) := by
    intro x hxp
    by_cases hx : x ∈ tsupport φ
    · have hfd := fderiv_eq_of_eq_sub_log hv (fun y hy hyp => (hloc y hy hyp).2) (hsub hx) hxp
      have hgr : gradient h x = gradient v x - kernel (x - p) := by
        simp only [gradient]
        rw [hfd, map_sub, Torus.toDual_symm_smul_innerSL]
        rfl
      rw [hgr, inner_sub_left]
    · simp [gradient_eq_zero_of_notMem_tsupport hx]
  have hae : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ p := by rw [ae_iff]; simp
  unfold CurlId
  rw [integral_congr_ae (hae.mono fun x hx => hpt x hx), integral_sub iA iB, hA, hB, sub_zero]

theorem curlId_of_subset {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ} {a : Fin N → ℂ}
    {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h) :
    ∀ (S : Finset ℂ) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x ∈ chargeSet Γ a, x ∈ tsupport φ → x ∈ S) → CurlId (gradient h) φ := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro φ hφ hc hS
    refine hP.curlId_of_subset_compl hφ hc fun x hx => ?_
    exact notMem_chargeSet_iff.1 fun hxP => by simpa using hS x hxP hx
  | insert q S hq ih =>
    intro φ hφ hc hS
    by_cases hqP : q ∈ chargeSet Γ a
    · obtain ⟨r, hr, hloc⟩ := hP.exists_radius_curlId hqP
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
      have := CurlId.add hP.locallyIntegrable_gradient hφ₁ hc₁ hφ₂ hc₂ e₁ e₂
      have e : (fun x => φ x * χ x + φ x * (1 - χ x)) = φ := by funext x; ring
      rwa [e] at this
    · refine ih φ hφ hc fun x hxP hx => ?_
      rcases Finset.mem_insert.1 (hS x hxP hx) with rfl | hxS
      · exact absurd hxP hqP
      · exact hxS

/-- **`curl ∇h = 0` weakly** for a torus potential `h`. -/
theorem integral_inner_gradient_I_gradient {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {N : ℕ}
    {a : Fin N → ℂ} {h : ℂ → ℝ} (hP : IsTorusPotential Γ a h)
    (hlf : ∀ R : ℝ, (chargeSet Γ a ∩ closedBall (0 : ℂ) R).Finite) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ x, inner ℝ (gradient h x) (Complex.I * gradient φ x) = 0 := by
  have hfin : (chargeSet Γ a ∩ tsupport φ).Finite := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
    exact (hlf R).subset fun x hx => ⟨hx.1, hR hx.2⟩
  exact hP.curlId_of_subset hfin.toFinset φ hφ hc fun x hxP hx => hfin.mem_toFinset.2 ⟨hxP, hx⟩

end IsTorusPotential

namespace Whole

/-- The one-point triangular torus potential is a torus potential. -/
theorem isTorusPotential_triangular :
    IsTorusPotential triangularLattice (fun _ : Fin 1 => (0 : ℂ))
      (torusPotential triangularLattice (fun _ : Fin 1 => (0 : ℂ))) := by
  have hcov : ZLattice.covolume triangularLattice = ((1 : ℕ) : ℝ) := by
    simpa using Torus.covolume_triangularLattice
  exact isTorusPotential_torusPotential triangularLattice hcov (fun _ : Fin 1 => (0 : ℂ))
    (fun i j _ => Subsingleton.elim i j)

theorem chargeSet_triangular :
    Torus.chargeSet triangularLattice (fun _ : Fin 1 => (0 : ℂ)) = (triangularLattice : Set ℂ) := by
  ext x; simp [Torus.chargeSet]

/-- **`E_△ ∈ 𝒜₁`** (first conjunct of `paperTriangularField_spec`). -/
theorem isAdmissibleField_paperTriangularField :
    IsAdmissibleField (triangularLattice : Set ℂ) paperTriangularField := by
  have hel := triangularField_mem_elec
  have hP := isTorusPotential_triangular
  have hlf : ∀ R : ℝ, (Torus.chargeSet triangularLattice (fun _ : Fin 1 => (0 : ℂ)) ∩
      closedBall (0 : ℂ) R).Finite := fun R => by rw [chargeSet_triangular]; exact hel.1 R
  have hpf : paperTriangularField = fun x => -triangularField x := rfl
  refine ⟨hel.1, ?_, fun φ hφ hc => ?_, fun φ hφ hc => ?_, ?_⟩
  · rw [hpf]; exact hel.2.1.neg
  · rw [hpf]
    simp_rw [inner_neg_left]
    rw [integral_neg, hel.2.2 φ hφ hc]
  · rw [hpf]
    simp_rw [inner_neg_left]
    rw [integral_neg, neg_eq_zero]
    exact hP.integral_inner_gradient_I_gradient hlf hφ hc
  · -- the growth bound, from the lattice count
    have hcount := Torus.tendsto_ncard_inter_cube_div triangularLattice Torus.covolume_triangularLattice
    obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 (hcount.eventually (eventually_le_nhds (by norm_num :
      (1 : ℝ) < 2)))
    set ℓ₂ : ℝ := max ℓ₁ 1 with hℓ₂
    set N₁ : ℝ := (((triangularLattice : Set ℂ) ∩ cube ℓ₂).ncard : ℝ) with hN₁
    refine ⟨8 / Real.pi + N₁, fun R hR => ?_⟩
    have hball : (triangularLattice : Set ℂ) ∩ ball 0 R ⊆ (triangularLattice : Set ℂ) ∩ cube (2 * R) :=
      inter_subset_inter_right _ fun x hx => by
        rw [mem_ball_zero_iff] at hx
        rw [Torus.mem_cube_iff]
        exact ⟨by linarith [Complex.abs_re_le_norm x], by linarith [Complex.abs_im_le_norm x]⟩
    have hfin : ∀ ℓ, ((triangularLattice : Set ℂ) ∩ cube ℓ).Finite := fun ℓ =>
      Torus.finite_lattice_inter (Torus.isBounded_cube ℓ)
    have h1 : (((triangularLattice : Set ℂ) ∩ ball 0 R).ncard : ℝ) ≤
        (((triangularLattice : Set ℂ) ∩ cube (2 * R)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hball (hfin _)
    have hpi := Real.pi_pos
    have hN0 : 0 ≤ N₁ := Nat.cast_nonneg _
    have hR2 : 0 < R ^ 2 := by positivity
    have hR21 : 1 ≤ R ^ 2 := by nlinarith
    by_cases hbig : ℓ₂ ≤ 2 * R
    · have h2 := hℓ₁ (2 * R) ((le_max_left _ _).trans hbig)
      rw [div_le_iff₀ (by positivity)] at h2
      have h3 : (8 / Real.pi + N₁) * (Real.pi * R ^ 2) = 8 * R ^ 2 + N₁ * (Real.pi * R ^ 2) := by
        field_simp
      have h4 : 0 ≤ N₁ * (Real.pi * R ^ 2) := by positivity
      have h5 : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
      rw [h3]
      linarith
    · have h2 : (((triangularLattice : Set ℂ) ∩ cube (2 * R)).ncard : ℝ) ≤ N₁ := by
        rw [hN₁]
        exact_mod_cast Set.ncard_le_ncard (inter_subset_inter_right _
          (Torus.cube_mono (a := 2 * R) (b := ℓ₂) (by linarith))) (hfin _)
      have h3 : N₁ ≤ N₁ * (Real.pi * R ^ 2) := by
        have : 1 ≤ Real.pi * R ^ 2 := by nlinarith [Real.two_le_pi]
        nlinarith
      have h4 : 0 ≤ 8 / Real.pi * (Real.pi * R ^ 2) := by positivity
      nlinarith

end Whole

end SandierSerfaty

end
