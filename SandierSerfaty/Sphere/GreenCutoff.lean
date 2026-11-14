/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.GreenPlane
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Green's identity on the plane with punctures and a cutoff

For finitely many punctures `P`, a function `u` of class `C²` off `P` with `Δ u = L` there, and a
cutoff `χ` of class `C^∞` with compact support and `χ = 1` near every puncture,
`Sphere.green_cutoff` is the identity, for `0 < η ≤ ρ`,
```
(∫_{Ω_η} χ (|∇u|² + u L)) + ∫_ℂ u ⟨∇χ, ∇u⟩ = - ∑_{p ∈ P} circleTerm u p η,
Ω_η = {x | ∀ p ∈ P, η ≤ |x - p|}.
```
It is obtained by splitting `χ = (χ - B) + B` with `B = ∑ₚ βₚ` a sum of bumps, applying the plane
Green identity (`Sphere.plane_green`) to `χ - B` and the local one (`Sphere.local_green_var`) to each `βₚ`.
-/

open MeasureTheory Filter Topology Laplacian Metric SandierSerfaty.Analysis
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

/-- A smooth bump equal to `1` on `closedBall c ρ` and to `0` outside `ball c (2ρ)`. -/
@[expose] noncomputable def bump (ρ : ℝ) (hρ : 0 < ρ) (c : ℂ) : ℂ → ℝ := fun x =>
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c) x

theorem contDiff_bump {ρ : ℝ} (hρ : 0 < ρ) (c : ℂ) : ContDiff ℝ ∞ (bump ρ hρ c) :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).contDiff

theorem bump_eq_one {ρ : ℝ} (hρ : 0 < ρ) {c x : ℂ} (hx : ‖x - c‖ ≤ ρ) : bump ρ hρ c x = 1 :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).one_of_mem_closedBall
    (by simpa [mem_closedBall, dist_eq_norm] using hx)

theorem bump_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {c x : ℂ} (hx : 2 * ρ ≤ ‖x - c‖) :
    bump ρ hρ c x = 0 :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).zero_of_le_dist
    (by simpa [dist_eq_norm] using hx)

theorem bump_hasCompactSupport {ρ : ℝ} (hρ : 0 < ρ) (c : ℂ) : HasCompactSupport (bump ρ hρ c) :=
  HasCompactSupport.intro (isCompact_closedBall c (2 * ρ)) fun x hx => by
    refine bump_eq_zero hρ ?_
    by_contra hlt
    exact hx (by simpa [dist_eq_norm] using (not_le.1 hlt).le)

theorem bump_eventuallyEq_zero {ρ : ℝ} (hρ : 0 < ρ) {c x : ℂ} (hx : 2 * ρ < ‖x - c‖) :
    bump ρ hρ c =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [ball_mem_nhds x (by linarith : 0 < ‖x - c‖ - 2 * ρ)] with y hy
  refine bump_eq_zero hρ ?_
  have h1 : ‖y - x‖ < ‖x - c‖ - 2 * ρ := by simpa [dist_eq_norm] using hy
  have h2 : ‖x - c‖ ≤ ‖y - c‖ + ‖y - x‖ := by
    calc ‖x - c‖ = ‖(y - c) - (y - x)‖ := by ring_nf
      _ ≤ ‖y - c‖ + ‖y - x‖ := norm_sub_le _ _
  linarith

/-- The sum of the bumps at the punctures. -/
@[expose] noncomputable def bumpSum (P : Finset ℂ) (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) : ℝ :=
  ∑ p ∈ P, bump ρ hρ p x

theorem contDiff_bumpSum (P : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ) : ContDiff ℝ ∞ (bumpSum P ρ hρ) := by
  unfold bumpSum
  exact ContDiff.sum fun p _ => contDiff_bump hρ p

theorem bumpSum_hasCompactSupport (P : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasCompactSupport (bumpSum P ρ hρ) := by
  refine HasCompactSupport.intro
    (P.finite_toSet.isCompact_biUnion fun p _ => isCompact_closedBall p (2 * ρ)) fun x hx => ?_
  unfold bumpSum
  refine Finset.sum_eq_zero fun p hp => bump_eq_zero hρ ?_
  by_contra hlt
  exact hx (Set.mem_biUnion hp (by simpa [dist_eq_norm] using (not_le.1 hlt).le))

/-! ### Calculus helpers -/

theorem gradDot_eq_zero_of_eventuallyEq {φ u : ℂ → ℝ} {x : ℂ} {c : ℝ}
    (h : φ =ᶠ[𝓝 x] fun _ => c) : gradDot φ u x = 0 := by
  have h1 := (pd_eventuallyEq_zero_of_const h 1).self_of_nhds
  have h2 := (pd_eventuallyEq_zero_of_const h Complex.I).self_of_nhds
  simp [gradDot, pd₁, pd₂, h1, h2]

theorem gradDot_sub {f g u : ℂ → ℝ} {x : ℂ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradDot (fun y => f y - g y) u x = gradDot f u x - gradDot g u x := by
  have e : ∀ v, fderiv ℝ (fun y => f y - g y) x v = fderiv ℝ f x v - fderiv ℝ g x v := by
    intro v
    rw [fderiv_fun_sub hf hg]; rfl
  simp only [gradDot, pd₁, pd₂, e]
  ring

theorem gradDot_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℝ} {u : ℂ → ℝ} {x : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    gradDot (fun y => ∑ i ∈ s, f i y) u x = ∑ i ∈ s, gradDot (f i) u x := by
  have e : ∀ v, fderiv ℝ (fun y => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, fderiv ℝ (f i) x v := by
    intro v
    rw [fderiv_fun_sum hf]
    simp
  simp only [gradDot, pd₁, pd₂, e, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- A function continuous on a closed set and vanishing off a compact set is integrable there. -/
theorem integrableOn_closed_of_zero {f : ℂ → ℝ} {Ω K : Set ℂ} (hΩ : IsClosed Ω)
    (hcont : ∀ x ∈ Ω, ContinuousAt f x) (hK : IsCompact K) (hzero : ∀ x, x ∉ K → f x = 0) :
    IntegrableOn f Ω := by
  have hint : IntegrableOn f (Ω ∩ K) :=
    ContinuousOn.integrableOn_compact (hK.inter_left hΩ)
      fun x hx => (hcont x hx.1).continuousWithinAt
  exact IntegrableOn.of_forall_sdiff_eq_zero hint hΩ.measurableSet fun x hx =>
    hzero x fun hxK => hx.2 ⟨hx.1, hxK⟩

/-! ### The standing data -/

/-- Cutoff data: separated punctures `P`, a radius `ρ`, and a cutoff `χ` equal to `1` near `P`. -/
structure CutoffData (P : Finset ℂ) (ρ : ℝ) (χ : ℂ → ℝ) : Prop where
  pos : 0 < ρ
  sep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 4 * ρ ≤ ‖p - q‖
  smooth : ContDiff ℝ ∞ χ
  compact : HasCompactSupport χ
  one : ∀ x, (∃ p ∈ P, ‖x - p‖ < 3 * ρ) → χ x = 1

/-- Regularity data: `u` is `C²` off `P` with `Δ u = L` there, and `L` is continuous off `P`. -/
structure GreenData (P : Finset ℂ) (u L : ℂ → ℝ) : Prop where
  c2 : ∀ x, x ∉ (P : Set ℂ) → ContDiffAt ℝ 2 u x
  lap : ∀ x, x ∉ (P : Set ℂ) → Δ u x = L x
  cont : ∀ x, x ∉ (P : Set ℂ) → ContinuousAt L x

section Cutoff

variable {P : Finset ℂ} {ρ : ℝ} {χ u L : ℂ → ℝ}

/-- The cutoff vanishing near the punctures: `φ = χ - B`. -/
@[expose] noncomputable def cutPhi (P : Finset ℂ) (ρ : ℝ) (hρ : 0 < ρ) (χ : ℂ → ℝ) (x : ℂ) : ℝ :=
  χ x - bumpSum P ρ hρ x

theorem CutoffData.bump_other (D : CutoffData P ρ χ) {p q : ℂ} (hp : p ∈ P) (hq : q ∈ P)
    (hpq : p ≠ q) {x : ℂ} (hx : ‖x - p‖ < ρ) : 2 * ρ < ‖x - q‖ := by
  have h1 := D.sep p hp q hq hpq
  have h2 : ‖p - q‖ ≤ ‖p - x‖ + ‖x - q‖ := by
    calc ‖p - q‖ = ‖(p - x) + (x - q)‖ := by ring_nf
      _ ≤ ‖p - x‖ + ‖x - q‖ := norm_add_le _ _
  rw [norm_sub_rev p x] at h2
  linarith [D.pos]

theorem CutoffData.bumpSum_eq_one (D : CutoffData P ρ χ) {p : ℂ} (hp : p ∈ P) {x : ℂ}
    (hx : ‖x - p‖ < ρ) : bumpSum P ρ D.pos x = 1 := by
  unfold bumpSum
  rw [Finset.sum_eq_single p]
  · exact bump_eq_one D.pos hx.le
  · intro q hq hqp
    exact bump_eq_zero D.pos (D.bump_other hp hq (Ne.symm hqp) hx).le
  · intro h; exact absurd hp h

theorem CutoffData.phi_eventuallyEq_zero (D : CutoffData P ρ χ) {p : ℂ} (hp : p ∈ P) {x : ℂ}
    (hx : ‖x - p‖ < ρ) : cutPhi P ρ D.pos χ =ᶠ[𝓝 x] fun _ => 0 := by
  have hn : ball p ρ ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa [dist_eq_norm] using hx)
  filter_upwards [hn] with y hy
  have hy' : ‖y - p‖ < ρ := by simpa [dist_eq_norm] using hy
  unfold cutPhi
  rw [D.bumpSum_eq_one hp hy', D.one y ⟨p, hp, by linarith [D.pos]⟩]
  ring

theorem CutoffData.chi_eventuallyEq_one (D : CutoffData P ρ χ) {p : ℂ} (hp : p ∈ P) {x : ℂ}
    (hx : ‖x - p‖ < 3 * ρ) : χ =ᶠ[𝓝 x] fun _ => 1 := by
  have hn : ball p (3 * ρ) ∈ 𝓝 x := isOpen_ball.mem_nhds (by simpa [dist_eq_norm] using hx)
  filter_upwards [hn] with y hy
  have hy' : ‖y - p‖ < 3 * ρ := by simpa [dist_eq_norm] using hy
  exact D.one y ⟨p, hp, hy'⟩

/-- The exterior of the `η`-discs about the punctures. -/
@[expose] def Omega (P : Finset ℂ) (η : ℝ) : Set ℂ := {x | ∀ p ∈ P, η ≤ ‖x - p‖}

theorem isClosed_exterior (p : ℂ) (η : ℝ) : IsClosed {x : ℂ | η ≤ ‖x - p‖} :=
  isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))

theorem isClosed_Omega (P : Finset ℂ) (η : ℝ) : IsClosed (Omega P η) := by
  have : Omega P η = ⋂ p ∈ P, {x : ℂ | η ≤ ‖x - p‖} := by
    ext x; simp [Omega]
  rw [this]
  exact isClosed_biInter fun p _ => isClosed_exterior p η

end Cutoff

section Main

variable {P : Finset ℂ} {ρ : ℝ} {χ u L : ℂ → ℝ}

/-- **Green's identity on the plane with punctures and a cutoff.** -/
theorem green_cutoff (D : CutoffData P ρ χ) (G : GreenData P u L) {η : ℝ} (hη : 0 < η)
    (hηρ : η ≤ ρ) :
    (∫ x in Omega P η, χ x * (gradSq u x + u x * L x)) + ∫ x, u x * gradDot χ u x =
      -∑ p ∈ P, circleTerm u p η := by
  have hρ := D.pos
  set φ : ℂ → ℝ := cutPhi P ρ hρ χ with hφ
  set A : ℂ → ℝ := gradSq u with hA
  set Gint : ℂ → ℝ := fun x => φ x * A x + u x * gradDot φ u x + φ x * u x * L x with hGint
  set Lint : ℂ → ℂ → ℝ := fun p x =>
    bump ρ hρ p x * A x + u x * gradDot (bump ρ hρ p) u x + bump ρ hρ p x * u x * L x with hLint
  have hφs : ContDiff ℝ ∞ φ := D.smooth.sub (contDiff_bumpSum P hρ)
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.sub D.compact (bumpSum_hasCompactSupport P hρ)
  have hvan : ∀ x ∈ (P : Set ℂ), φ =ᶠ[𝓝 x] fun _ => 0 := fun x hx =>
    D.phi_eventuallyEq_zero hx (by simpa using hρ)
  -- the plane identity
  have hG : ∫ x, Gint x = 0 :=
    plane_green G.c2 G.lap (hφs.of_le (by norm_cast)) hφc hvan
  -- the local identities
  have hLp : ∀ p ∈ P, ∫ x in {x : ℂ | η ≤ ‖x - p‖}, Lint p x = -circleTerm u p η := by
    intro p hp
    have key := local_green_var (u := u) (β := bump ρ hρ p) (L := L) (p := p) (η := η) (ρ := ρ)
      (S := (P : Set ℂ)) hη hηρ G.c2 G.lap (contDiff_bump hρ p) (fun x hx => bump_eq_one hρ hx)
      (fun x hx => bump_eq_zero hρ hx) (fun x hx hxp => by
        refine bump_eventuallyEq_zero hρ ?_
        have := D.sep x hx p hp hxp
        linarith)
    simp only [circleTerm]
    rw [← key]
  -- regularity: `Gint`
  have hzeroG : ∀ x, x ∉ tsupport φ → Gint x = 0 := by
    intro x hx
    have h0 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    have h1 := h0.self_of_nhds
    have h2 : gradDot φ u x = 0 := gradDot_eq_zero_of_eventuallyEq (c := 0) h0
    simp [hGint, h1, h2]
  have hcontG : Continuous Gint := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hxP : x ∈ P
    · have h0 := hvan x hxP
      have : Gint =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0, pd_eventuallyEq_zero h0 1, pd_eventuallyEq_zero h0 Complex.I] with
          y hy h1 h2
        simp [hGint, gradDot, pd₁, pd₂, hy, h1, h2]
      exact continuousAt_const.congr this.symm
    · have hp := contDiffAt_green_pieces (u := u) hφs (Or.inl (G.c2 x hxP))
      have c1 := hp.1.continuousAt
      have c2 := hp.2.1.continuousAt
      have c3 := (hp.2.2.continuousAt).mul (G.cont x hxP)
      exact (c1.add c2).add c3
  have hintG : Integrable Gint :=
    hcontG.integrable_of_hasCompactSupport (HasCompactSupport.intro hφc hzeroG)
  -- regularity: `Lint p`
  have hintL : ∀ p ∈ P, IntegrableOn (Lint p) {x : ℂ | η ≤ ‖x - p‖} := by
    intro p hp
    refine integrableOn_exterior_of_zero (R := 3 * ρ) hη (fun x hx => ?_) (fun x hx => ?_)
    · have hxp : x ≠ p := by
        intro h; rw [h, sub_self, norm_zero] at hx; exact absurd hx (not_le.2 hη)
      by_cases hxP : x ∈ P
      · have h0 : bump ρ hρ p =ᶠ[𝓝 x] fun _ => 0 := by
          refine bump_eventuallyEq_zero hρ ?_
          have := D.sep x hxP p hp hxp
          linarith
        have : Lint p =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [h0, pd_eventuallyEq_zero h0 1, pd_eventuallyEq_zero h0 Complex.I] with
            y hy h1 h2
          simp [hLint, gradDot, pd₁, pd₂, hy, h1, h2]
        exact continuousAt_const.congr this.symm
      · have hpc := contDiffAt_green_pieces (u := u) (contDiff_bump hρ p) (Or.inl (G.c2 x hxP))
        exact (hpc.1.continuousAt.add hpc.2.1.continuousAt).add
          ((hpc.2.2.continuousAt).mul (G.cont x hxP))
    · have h0 : bump ρ hρ p =ᶠ[𝓝 x] fun _ => 0 :=
        bump_eventuallyEq_zero hρ (by linarith)
      have h1 := h0.self_of_nhds
      have h2 : gradDot (bump ρ hρ p) u x = 0 := gradDot_eq_zero_of_eventuallyEq (c := 0) h0
      simp [hLint, h1, h2]
  -- the cutoff-gradient term
  have hQcont : Continuous fun x => u x * gradDot χ u x := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : ∃ p ∈ P, ‖x - p‖ < 3 * ρ
    · obtain ⟨p, hp, hxp⟩ := hx
      have h0 := D.chi_eventuallyEq_one hp hxp
      have : (fun x => u x * gradDot χ u x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [h0, pd_eventuallyEq_zero_of_const h0 1,
          pd_eventuallyEq_zero_of_const h0 Complex.I] with y hy h1 h2
        simp [gradDot, pd₁, pd₂, h1, h2]
      exact continuousAt_const.congr this.symm
    · have hxP : x ∉ P := fun h => hx ⟨x, h, by simpa using (by linarith : (0 : ℝ) < 3 * ρ)⟩
      exact (contDiffAt_green_piece₂ (φ := χ) D.smooth (Or.inl (G.c2 x hxP))).continuousAt
  have hintQ : Integrable fun x => u x * gradDot χ u x := by
    refine hQcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro D.compact fun x hx => ?_)
    have h0 : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    simp [gradDot_eq_zero_of_eventuallyEq (c := 0) h0]
  -- the main integrand
  have hintM : IntegrableOn (fun x => χ x * (A x + u x * L x)) (Omega P η) := by
    refine integrableOn_closed_of_zero (isClosed_Omega P η) (fun x hx => ?_) D.compact
      (fun x hx => ?_)
    · have hxP : x ∉ P := fun h => by
        have := hx x h
        rw [sub_self, norm_zero] at this; exact absurd this (not_le.2 hη)
      have hpc := contDiffAt_green_pieces (u := u) D.smooth (Or.inl (G.c2 x hxP))
      have := hpc.1.continuousAt.add ((hpc.2.2.continuousAt).mul (G.cont x hxP))
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.add_apply, Pi.mul_apply, hA]; ring
    · have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  -- the pointwise identity
  have hpt : ∀ x, Gint x + ∑ p ∈ P, (({x : ℂ | η ≤ ‖x - p‖} : Set ℂ).indicator (Lint p)) x =
      (Omega P η).indicator (fun x => χ x * (A x + u x * L x)) x + u x * gradDot χ u x := by
    intro x
    by_cases hx : x ∈ Omega P η
    · have hind : ∀ p ∈ P, (({x : ℂ | η ≤ ‖x - p‖} : Set ℂ).indicator (Lint p)) x = Lint p x :=
        fun p hp => Set.indicator_of_mem (show x ∈ {x : ℂ | η ≤ ‖x - p‖} from hx p hp) _
      rw [Finset.sum_congr rfl hind, Set.indicator_of_mem hx]
      have hdiff : ∀ p ∈ P, DifferentiableAt ℝ (bump ρ hρ p) x := fun p _ =>
        ((contDiff_bump hρ p).differentiable (by simp)) x
      have hgB : gradDot (fun y => bumpSum P ρ hρ y) u x =
          ∑ p ∈ P, gradDot (bump ρ hρ p) u x := gradDot_finset_sum P hdiff
      have hgφ : gradDot φ u x = gradDot χ u x - gradDot (fun y => bumpSum P ρ hρ y) u x :=
        gradDot_sub ((D.smooth.differentiable (by simp)) x)
          (((contDiff_bumpSum P hρ).differentiable (by simp)) x)
      have hB : ∑ p ∈ P, bump ρ hρ p x = bumpSum P ρ hρ x := rfl
      have hφx : φ x = χ x - bumpSum P ρ hρ x := rfl
      simp only [hGint, hLint, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hB,
        hgφ, hgB, hφx]
      ring
    · have hx' : ∃ p ∈ P, ‖x - p‖ < η := by
        by_contra hcon
        apply hx
        intro p hp
        by_contra hlt
        exact hcon ⟨p, hp, not_le.1 hlt⟩
      obtain ⟨p0, hp0, hxp0⟩ := hx'
      have hxρ : ‖x - p0‖ < ρ := lt_of_lt_of_le hxp0 hηρ
      have h0 := D.phi_eventuallyEq_zero hp0 hxρ
      have hG0 : Gint x = 0 := by
        have h1 : φ x = 0 := h0.self_of_nhds
        have h2 : gradDot φ u x = 0 := gradDot_eq_zero_of_eventuallyEq (c := 0) h0
        simp [hGint, h1, h2]
      have hc := D.chi_eventuallyEq_one hp0 (by linarith)
      have hQ0 : u x * gradDot χ u x = 0 := by
        simp [gradDot_eq_zero_of_eventuallyEq hc]
      have hΩ : x ∉ Omega P η := fun h => absurd (h p0 hp0) (not_le.2 hxp0)
      rw [Set.indicator_of_notMem hΩ, hG0, hQ0]
      simp only [zero_add]
      refine Finset.sum_eq_zero fun p hp => ?_
      by_cases hpp : p = p0
      · subst hpp
        exact Set.indicator_of_notMem (by simpa using hxp0) _
      · have h0' : bump ρ hρ p =ᶠ[𝓝 x] fun _ => 0 :=
          bump_eventuallyEq_zero hρ (D.bump_other hp0 hp (Ne.symm hpp) hxρ)
        have h1 := h0'.self_of_nhds
        have h2 : gradDot (bump ρ hρ p) u x = 0 := gradDot_eq_zero_of_eventuallyEq (c := 0) h0'
        have : Lint p x = 0 := by simp [hLint, h1, h2]
        simp only [Set.indicator_apply, this, ite_self]
  -- integrate the pointwise identity
  have hint1 : ∀ p ∈ P, Integrable (({x : ℂ | η ≤ ‖x - p‖} : Set ℂ).indicator (Lint p)) :=
    fun p hp => (integrable_indicator_iff (isClosed_exterior p η).measurableSet).2 (hintL p hp)
  have hint2 : Integrable (fun x =>
      ∑ p ∈ P, (({x : ℂ | η ≤ ‖x - p‖} : Set ℂ).indicator (Lint p)) x) :=
    integrable_finsetSum P hint1
  have hint3 : Integrable ((Omega P η).indicator (fun x => χ x * (A x + u x * L x))) :=
    (integrable_indicator_iff (isClosed_Omega P η).measurableSet).2 hintM
  have hmain := congrArg (fun F : ℂ → ℝ => ∫ x, F x) (funext hpt)
  rw [integral_add hintG hint2, integral_add hint3 hintQ, integral_finsetSum P hint1, hG,
    zero_add, integral_indicator (isClosed_Omega P η).measurableSet] at hmain
  have hsum : ∑ p ∈ P, ∫ x, (({x : ℂ | η ≤ ‖x - p‖} : Set ℂ).indicator (Lint p)) x =
      -∑ p ∈ P, circleTerm u p η := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [integral_indicator (isClosed_exterior p η).measurableSet, hLp p hp]
  rw [hsum] at hmain
  exact hmain.symm

end Main

end Sphere

end SandierSerfaty

end
