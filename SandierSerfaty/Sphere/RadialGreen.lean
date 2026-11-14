/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.PolarDivergence
public import SandierSerfaty.Analysis.PeriodicGreen
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SandierSerfaty.Analysis.PolarAnnulus
public import SandierSerfaty.Screening.TruncDiff

/-!
# The radial Green identity (sphere note, Lemma 3.10, Green step; Theorem 4.2, isotropic averaging)

`Sphere.circleAverage_sub_eq_integral`: if `u` is `C¹` at `p`, `C²` on `\bar B(p, α) ∖ {p}` and
`Δ u = 2π ϱ` there, with `ϱ` continuous on `\bar B(p, α)`, then
`⨍_{∂B(p, α)} u - u(p) = ∫_{B(p, α)} f_α(x - p) ϱ(x) dx`, `f_α = truncLog α`.

The proof is one-dimensional calculus in polar coordinates `(r, θ)`: with `R = r ∂_r u`,
`r Δ u = ∂_r R + ∂_θ(u_θ)`. Integrating `log (α/r) · r Δ u` over `[ε, α] × [-π, π]`, the angular part
vanishes by periodicity, and `log (α/r) ∂_r R = ∂_r [log (α/r) R + u]`; the boundary term at `ε` is
`O(ε log (1/ε)) → 0` and `⨍_{∂B(ε)} u → u(p)`. All integrands are continuous on the compact box, so
Fubini applies there; `ε ↓ 0` is dominated convergence.

The local-in-radius continuity statements of `Analysis.PolarDivergence` (hypotheses only on
`0 < ‖x‖ ≤ α`) are `continuousOn_radialDeriv_le`, `continuousOn_angularDeriv_le`,
`continuousOn_radialComp_le`.
-/

open MeasureTheory Filter Topology Set SandierSerfaty.Analysis Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

section Continuity

variable {Y₁ Y₂ : ℂ → ℝ} {α : ℝ}
  (h₁ : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 1 Y₁ x)
  (h₂ : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 1 Y₂ x)
include h₁ h₂

theorem continuousAt_polar_pieces_le {q : ℝ × ℝ} (hq : 0 < q.1) (hqα : q.1 ≤ α) :
    ContinuousAt (fun q : ℝ × ℝ => Y₁ (polarPt q.1 q.2)) q ∧
    ContinuousAt (fun q : ℝ × ℝ => Y₂ (polarPt q.1 q.2)) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₁ (polarPt q.1 q.2) 1) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₁ (polarPt q.1 q.2) Complex.I) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₂ (polarPt q.1 q.2) 1) q ∧
    ContinuousAt (fun q : ℝ × ℝ => fderiv ℝ Y₂ (polarPt q.1 q.2) Complex.I) q := by
  have hne : polarPt q.1 q.2 ≠ 0 := polarPt_ne_zero hq q.2
  have hn : ‖polarPt q.1 q.2‖ ≤ α := by rwa [norm_polarPt hq.le]
  have hp : ContinuousAt (fun q : ℝ × ℝ => polarPt q.1 q.2) q := continuous_polarPt.continuousAt
  have e1 := h₁ _ hne hn
  have e2 := h₂ _ hne hn
  exact ⟨ContinuousAt.comp_of_eq e1.continuousAt hp rfl, ContinuousAt.comp_of_eq e2.continuousAt hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e1 1) hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e1 Complex.I) hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e2 1) hp rfl,
    ContinuousAt.comp_of_eq (continuousAt_fderiv_apply e2 Complex.I) hp rfl⟩

theorem continuousOn_radialDeriv_le :
    ContinuousOn (fun q : ℝ × ℝ => radialDeriv Y₁ Y₂ q.1 q.2) {q | 0 < q.1 ∧ q.1 ≤ α} := by
  intro q hq
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := continuousAt_polar_pieces_le h₁ h₂ hq.1 hq.2
  refine ContinuousAt.continuousWithinAt ?_
  have hr : ContinuousAt (fun q : ℝ × ℝ => q.1) q := continuousAt_fst
  have hc : ContinuousAt (fun q : ℝ × ℝ => Real.cos q.2) q :=
    (Real.continuous_cos.comp continuous_snd).continuousAt
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sin q.2) q :=
    (Real.continuous_sin.comp continuous_snd).continuousAt
  unfold radialDeriv radialComp
  apply_rules [ContinuousAt.add, ContinuousAt.mul, ContinuousAt.neg]

theorem continuousOn_angularDeriv_le :
    ContinuousOn (fun q : ℝ × ℝ => angularDeriv Y₁ Y₂ q.1 q.2) {q | 0 < q.1 ∧ q.1 ≤ α} := by
  intro q hq
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := continuousAt_polar_pieces_le h₁ h₂ hq.1 hq.2
  refine ContinuousAt.continuousWithinAt ?_
  have hr : ContinuousAt (fun q : ℝ × ℝ => q.1) q := continuousAt_fst
  have hc : ContinuousAt (fun q : ℝ × ℝ => Real.cos q.2) q :=
    (Real.continuous_cos.comp continuous_snd).continuousAt
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sin q.2) q :=
    (Real.continuous_sin.comp continuous_snd).continuousAt
  unfold angularDeriv radialComp
  apply_rules [ContinuousAt.add, ContinuousAt.mul, ContinuousAt.neg]

theorem continuousOn_radialComp_le :
    ContinuousOn (fun q : ℝ × ℝ => radialComp Y₁ Y₂ q.1 q.2) {q | 0 < q.1 ∧ q.1 ≤ α} := by
  intro q hq
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := continuousAt_polar_pieces_le h₁ h₂ hq.1 hq.2
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun q : ℝ × ℝ => Real.cos q.2) q :=
    (Real.continuous_cos.comp continuous_snd).continuousAt
  have hs : ContinuousAt (fun q : ℝ × ℝ => Real.sin q.2) q :=
    (Real.continuous_sin.comp continuous_snd).continuousAt
  unfold radialComp
  apply_rules [ContinuousAt.add, ContinuousAt.mul, ContinuousAt.neg]

end Continuity

section Identity

theorem intervalIntegral_swap_of_continuousOn {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h : ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by
  apply intervalIntegral_intervalIntegral_swap
  rw [uIoc_of_le hab, uIoc_of_le hcd]
  exact (h.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

variable {u : ℂ → ℝ} {α : ℝ}

theorem contDiffAt_pd₁_le (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 1 (pd₁ u) x := fun x hx hxα => by
  have := contDiffAt_pd (n := 1) (by norm_num; exact hu2 x hx hxα) 1
  exact this

theorem contDiffAt_pd₂_le (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 1 (pd₂ u) x := fun x hx hxα => by
  have := contDiffAt_pd (n := 1) (by norm_num; exact hu2 x hx hxα) Complex.I
  exact this

theorem radialDeriv_add_angularDeriv_laplacian (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x)
    {r : ℝ} (hr : 0 < r) (hrα : r ≤ α) (θ : ℝ) :
    radialDeriv (pd₁ u) (pd₂ u) r θ + angularDeriv (pd₁ u) (pd₂ u) r θ =
      r * Laplacian.laplacian u (polarPt r θ) := by
  rw [radialDeriv_add_angularDeriv, laplacian_eq_pd (hu2 _ (polarPt_ne_zero hr θ)
    (by rwa [norm_polarPt hr.le]))]
  rfl

theorem hasDerivAt_log_radial (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {r θ : ℝ}
    (hr : 0 < r) (hrα : r ≤ α) :
    HasDerivAt (fun s : ℝ => (Real.log α - Real.log s) * (s * radialComp (pd₁ u) (pd₂ u) s θ) +
        u (polarPt s θ))
      ((Real.log α - Real.log r) * radialDeriv (pd₁ u) (pd₂ u) r θ) r := by
  have hx : polarPt r θ ≠ 0 := polarPt_ne_zero hr θ
  have hxα : ‖polarPt r θ‖ ≤ α := by rwa [norm_polarPt hr.le]
  have hdu : DifferentiableAt ℝ u (polarPt r θ) := (hu2 _ hx hxα).differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (pd₁ u) (polarPt r θ) :=
    (contDiffAt_pd₁_le hu2 _ hx hxα).differentiableAt one_ne_zero
  have hd2 : DifferentiableAt ℝ (pd₂ u) (polarPt r θ) :=
    (contDiffAt_pd₂_le hu2 _ hx hxα).differentiableAt one_ne_zero
  have hR := hasDerivAt_radial hd1 hd2
  have hL : HasDerivAt (fun s : ℝ => Real.log α - Real.log s) (-r⁻¹) r :=
    ((hasDerivAt_const r (Real.log α)).fun_sub (Real.hasDerivAt_log hr.ne')).congr_deriv (by ring)
  have hw := hasDerivAt_comp_polarPt_r hdu
  refine ((hL.mul hR).add hw).congr_deriv ?_
  simp only [radialComp, pd₁, pd₂]
  field_simp
  ring

theorem box_subset {ε α : ℝ} (hε : 0 < ε) :
    Icc ε α ×ˢ Icc (-Real.pi) Real.pi ⊆ {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ α} :=
  fun _ hq => ⟨lt_of_lt_of_le hε hq.1.1, hq.1.2⟩

theorem continuousOn_logWeight {ε α : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun q : ℝ × ℝ => Real.log α - Real.log q.1) (Icc ε α ×ˢ Icc (-Real.pi) Real.pi) :=
  continuousOn_const.sub (ContinuousOn.log continuous_fst.continuousOn
    (fun _ hq => (lt_of_lt_of_le hε hq.1.1).ne'))

theorem integral_log_radialDeriv (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {ε : ℝ}
    (hε : 0 < ε) (hεα : ε ≤ α) (θ : ℝ) :
    ∫ r in ε..α, (Real.log α - Real.log r) * radialDeriv (pd₁ u) (pd₂ u) r θ =
      u (polarPt α θ) - u (polarPt ε θ) -
        (Real.log α - Real.log ε) * (ε * radialComp (pd₁ u) (pd₂ u) ε θ) := by
  have hint : IntervalIntegrable (fun r => (Real.log α - Real.log r) *
      radialDeriv (pd₁ u) (pd₂ u) r θ) volume ε α := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hεα]
    have h1 : ContinuousOn (fun r : ℝ => Real.log α - Real.log r) (Icc ε α) :=
      continuousOn_const.sub (ContinuousOn.log continuousOn_id (fun r hr => (lt_of_lt_of_le hε hr.1).ne'))
    have h2 : ContinuousOn (fun r : ℝ => radialDeriv (pd₁ u) (pd₂ u) r θ) (Icc ε α) := by
      have := (continuousOn_radialDeriv_le (contDiffAt_pd₁_le hu2) (contDiffAt_pd₂_le hu2)).comp
        (continuous_id.prodMk (continuous_const (y := θ))).continuousOn
        (s := Icc ε α) (t := {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ α})
        (fun r hr => ⟨lt_of_lt_of_le hε hr.1, hr.2⟩)
      exact this
    exact h1.mul h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hasDerivAt_log_radial hu2 (lt_of_lt_of_le hε (uIcc_of_le hεα ▸ hr).1)
      (uIcc_of_le hεα ▸ hr).2) hint]
  simp only [sub_self, zero_mul, zero_add]
  ring

theorem integral_angularDeriv (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {r : ℝ}
    (hr : 0 < r) (hrα : r ≤ α) :
    ∫ θ in (-Real.pi)..Real.pi, angularDeriv (pd₁ u) (pd₂ u) r θ = 0 := by
  have hx : ∀ θ, polarPt r θ ≠ 0 := polarPt_ne_zero hr
  have hxα : ∀ θ, ‖polarPt r θ‖ ≤ α := fun θ => by rwa [norm_polarPt hr.le]
  have hder : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
      HasDerivAt (fun θ => angularComp (pd₁ u) (pd₂ u) r θ) (angularDeriv (pd₁ u) (pd₂ u) r θ) θ :=
    fun θ _ => hasDerivAt_angular ((contDiffAt_pd₁_le hu2 _ (hx θ) (hxα θ)).differentiableAt one_ne_zero)
      ((contDiffAt_pd₂_le hu2 _ (hx θ) (hxα θ)).differentiableAt one_ne_zero)
  have hcont : ContinuousOn (fun θ : ℝ => angularDeriv (pd₁ u) (pd₂ u) r θ) (uIcc (-Real.pi) Real.pi) := by
    have := (continuousOn_angularDeriv_le (contDiffAt_pd₁_le hu2) (contDiffAt_pd₂_le hu2)).comp
      (continuous_const (y := r) |>.prodMk continuous_id).continuousOn
      (s := uIcc (-Real.pi) Real.pi) (t := {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ α})
      (fun θ _ => ⟨hr, hrα⟩)
    exact this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable)]
  simp [angularComp, polarPt_pi, Real.cos_neg, Real.sin_neg, Real.sin_pi]

theorem swap_box {G : ℝ → ℝ → ℝ} {ε α : ℝ} (hεα : ε ≤ α)
    (h : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) (Icc ε α ×ˢ Icc (-Real.pi) Real.pi)) :
    ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α, G r θ =
      ∫ r in ε..α, ∫ θ in (-Real.pi)..Real.pi, G r θ := by
  refine intervalIntegral_swap_of_continuousOn (F := fun θ r => G r θ)
    (by linarith [Real.pi_pos]) hεα ?_
  have := h.comp continuous_swap.continuousOn
    (s := Icc (-Real.pi) Real.pi ×ˢ Icc ε α) (t := Icc ε α ×ˢ Icc (-Real.pi) Real.pi)
    (fun q hq => ⟨hq.2, hq.1⟩)
  exact this

theorem continuousOn_theta {G : ℝ → ℝ → ℝ} {ε α r : ℝ} (hr : r ∈ Icc ε α)
    (h : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) (Icc ε α ×ˢ Icc (-Real.pi) Real.pi)) :
    ContinuousOn (fun θ => G r θ) (Icc (-Real.pi) Real.pi) := by
  have := h.comp (continuous_const (y := r) |>.prodMk continuous_id).continuousOn
    (s := Icc (-Real.pi) Real.pi) (t := Icc ε α ×ˢ Icc (-Real.pi) Real.pi)
    (fun θ hθ => ⟨hr, hθ⟩)
  exact this

/-- **The integrated radial identity** on `ε ≤ r ≤ α`. -/
theorem radial_identity (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) {ε : ℝ}
    (hε : 0 < ε) (hεα : ε ≤ α) :
    ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α,
        (Real.log α - Real.log r) * (r * Laplacian.laplacian u (polarPt r θ)) =
      ∫ θ in (-Real.pi)..Real.pi, (u (polarPt α θ) - u (polarPt ε θ) -
        (Real.log α - Real.log ε) * (ε * radialComp (pd₁ u) (pd₂ u) ε θ)) := by
  have hcRD : ContinuousOn (fun q : ℝ × ℝ => radialDeriv (pd₁ u) (pd₂ u) q.1 q.2)
      (Icc ε α ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_radialDeriv_le (contDiffAt_pd₁_le hu2) (contDiffAt_pd₂_le hu2)).mono (box_subset hε)
  have hcAD : ContinuousOn (fun q : ℝ × ℝ => angularDeriv (pd₁ u) (pd₂ u) q.1 q.2)
      (Icc ε α ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_angularDeriv_le (contDiffAt_pd₁_le hu2) (contDiffAt_pd₂_le hu2)).mono (box_subset hε)
  have hL := continuousOn_logWeight (α := α) hε
  have hbox : ∀ r ∈ Icc ε α, 0 < r ∧ r ≤ α := fun r hr => ⟨lt_of_lt_of_le hε hr.1, hr.2⟩
  calc ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α,
        (Real.log α - Real.log r) * (r * Laplacian.laplacian u (polarPt r θ))
      = ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α, (Real.log α - Real.log r) *
          (radialDeriv (pd₁ u) (pd₂ u) r θ + angularDeriv (pd₁ u) (pd₂ u) r θ) := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hεα] at hr
        rw [radialDeriv_add_angularDeriv_laplacian hu2 (hbox r hr).1 (hbox r hr).2]
    _ = ∫ r in ε..α, ∫ θ in (-Real.pi)..Real.pi, (Real.log α - Real.log r) *
          (radialDeriv (pd₁ u) (pd₂ u) r θ + angularDeriv (pd₁ u) (pd₂ u) r θ) := by
        refine swap_box hεα (G := fun r θ => (Real.log α - Real.log r) *
          (radialDeriv (pd₁ u) (pd₂ u) r θ + angularDeriv (pd₁ u) (pd₂ u) r θ)) ?_
        exact hL.mul (hcRD.add hcAD)
    _ = ∫ r in ε..α, ∫ θ in (-Real.pi)..Real.pi, (Real.log α - Real.log r) *
          radialDeriv (pd₁ u) (pd₂ u) r θ := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hεα] at hr
        have h1 : IntervalIntegrable (fun θ => radialDeriv (pd₁ u) (pd₂ u) r θ) volume
            (-Real.pi) Real.pi := by
          refine ContinuousOn.intervalIntegrable ?_
          rw [uIcc_of_le (by linarith [Real.pi_pos])]
          exact continuousOn_theta hr hcRD
        have h2 := integral_angularDeriv hu2 (hbox r hr).1 (hbox r hr).2
        simp only [mul_add]
        rw [intervalIntegral.integral_add (h1.const_mul _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, h2]
        · simp only [mul_zero, add_zero]
        · refine (ContinuousOn.intervalIntegrable ?_).const_mul _
          rw [uIcc_of_le (by linarith [Real.pi_pos])]
          exact continuousOn_theta hr hcAD
    _ = ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α, (Real.log α - Real.log r) *
          radialDeriv (pd₁ u) (pd₂ u) r θ := by
        symm
        refine swap_box hεα (G := fun r θ => (Real.log α - Real.log r) *
          radialDeriv (pd₁ u) (pd₂ u) r θ) ?_
        exact hL.mul hcRD
    _ = _ := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        exact integral_log_radialDeriv hu2 hε hεα θ

end Identity

section Limit

variable {u : ℂ → ℝ} {α : ℝ}

theorem polarPt_eq_circleMap (r θ : ℝ) : polarPt r θ = circleMap 0 r θ := by
  rw [circleMap, zero_add, Complex.exp_mul_I]
  simp [polarPt, Complex.ofReal_cos, Complex.ofReal_sin]

theorem polarPt_zero (θ : ℝ) : polarPt 0 θ = 0 := by simp [polarPt]

theorem continuousOn_closedBall_of_c1_c2 (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) : ContinuousOn u (Metric.closedBall 0 α) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx
  by_cases h0 : x = 0
  · subst h0; exact hu1.continuousAt.continuousWithinAt
  · exact (hu2 x h0 hx).continuousAt.continuousWithinAt

theorem continuous_polarPt_theta (ε : ℝ) : Continuous (polarPt ε) :=
  continuous_polarPt.comp (continuous_const.prodMk continuous_id)

theorem continuous_polarPt_r (θ : ℝ) : Continuous (fun r => polarPt r θ) :=
  continuous_polarPt.comp (continuous_id.prodMk continuous_const)

/-- `∫_{-π}^{π} u(ε e^{iθ}) dθ → 2π u(0)` as `ε ↓ 0`. -/
theorem tendsto_integral_circle (hα : 0 < α) (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x) :
    Tendsto (fun ε : ℝ => ∫ θ in (-Real.pi)..Real.pi, u (polarPt ε θ)) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * u 0)) := by
  have hcb := continuousOn_closedBall_of_c1_c2 hu1 hu2
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) α).exists_bound_of_continuousOn hcb
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ α := by
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hα] with ε h1 h2 using ⟨h1, h2.2⟩
  have hmem : ∀ ε : ℝ, 0 < ε → ε ≤ α → ∀ θ, polarPt ε θ ∈ Metric.closedBall (0 : ℂ) α := by
    intro ε h1 h2 θ
    rw [mem_closedBall_zero_iff, norm_polarPt h1.le]; exact h2
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -Real.pi) (b := Real.pi) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε θ => u (polarPt ε θ)) (f := fun _ => u 0) (fun _ => M) ?_ ?_
    intervalIntegrable_const ?_
  · have e : (∫ _ in (-Real.pi)..Real.pi, u 0) = 2 * Real.pi * u 0 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    rwa [e] at key
  · filter_upwards [hev] with ε hε
    exact (hcb.comp (continuous_polarPt_theta ε).continuousOn
      (fun θ _ => hmem ε hε.1 hε.2 θ)).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hev] with ε hε
    exact Eventually.of_forall fun θ _ => hM _ (hmem ε hε.1 hε.2 θ)
  · refine Eventually.of_forall fun θ _ => ?_
    have h1 : Tendsto (fun r : ℝ => polarPt r θ) (𝓝 0) (𝓝 0) := by
      have := (continuous_polarPt_r θ).tendsto 0
      rwa [polarPt_zero] at this
    exact (hu1.continuousAt.tendsto.comp h1).mono_left nhdsWithin_le_nhds

theorem tendsto_mul_log_weight (α : ℝ) :
    Tendsto (fun ε : ℝ => ε * (Real.log α - Real.log ε)) (𝓝 0) (𝓝 0) := by
  have h : Continuous fun ε : ℝ => ε * Real.log α - ε * Real.log ε :=
    (continuous_id.mul continuous_const).sub Real.continuous_mul_log
  have := h.tendsto 0
  simp only [zero_mul, Real.log_zero, mul_zero, sub_zero] at this
  refine this.congr fun ε => ?_
  ring

/-- The boundary term of the radial identity vanishes as `ε ↓ 0`. -/
theorem tendsto_boundary_term (hu1 : ContDiffAt ℝ 1 u 0) :
    Tendsto (fun ε : ℝ => ∫ θ in (-Real.pi)..Real.pi,
        (Real.log α - Real.log ε) * (ε * radialComp (pd₁ u) (pd₂ u) ε θ)) (𝓝[>] 0) (𝓝 0) := by
  have hfd : ContinuousAt (fderiv ℝ u) 0 := (hu1.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hK : ∀ᶠ x in 𝓝 (0 : ℂ), ‖fderiv ℝ u x‖ < ‖fderiv ℝ u 0‖ + 1 :=
    hfd.norm.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨δ, hδ, hδK⟩ := Metric.eventually_nhds_iff.1 hK
  set K := ‖fderiv ℝ u 0‖ + 1 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < δ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hδ] with ε h1 h2 using ⟨h1, h2.2⟩
  have hg : Tendsto (fun ε : ℝ => |ε * (Real.log α - Real.log ε)| * K * (2 * Real.pi))
      (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_mul_log_weight α).abs.mul_const K).mul_const (2 * Real.pi)
    simp only [abs_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hev] with ε hε
  have hb : ∀ θ, ‖radialComp (pd₁ u) (pd₂ u) ε θ‖ ≤ K := by
    intro θ
    have hxd : dist (polarPt ε θ) 0 < δ := by
      rw [dist_zero_right, norm_polarPt hε.1.le]; exact hε.2
    have h1 := hδK hxd
    have h2 : radialComp (pd₁ u) (pd₂ u) ε θ =
        fderiv ℝ u (polarPt ε θ) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) := by
      rw [fderiv_polar_dir]; simp only [radialComp, pd₁, pd₂]; ring
    rw [h2]
    have h3 : ‖(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I‖ = 1 := by
      have := norm_polarPt (zero_le_one) θ
      simp
    calc ‖fderiv ℝ u (polarPt ε θ) ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)‖
        ≤ ‖fderiv ℝ u (polarPt ε θ)‖ * ‖(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K := by rw [h3, mul_one]; exact h1.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi) (C := |ε * (Real.log α - Real.log ε)| * K)
    (f := fun θ => (Real.log α - Real.log ε) * (ε * radialComp (pd₁ u) (pd₂ u) ε θ))
    (fun θ _ => by
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (ε)]
      calc |Real.log α - Real.log ε| * (|ε| * ‖radialComp (pd₁ u) (pd₂ u) ε θ‖)
          ≤ |Real.log α - Real.log ε| * (|ε| * K) := by gcongr; exact hb θ
        _ = |ε * (Real.log α - Real.log ε)| * K := by
          rw [abs_mul]; ring)
  refine this.trans (le_of_eq ?_)
  rw [show |Real.pi - -Real.pi| = 2 * Real.pi by
    rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring]

theorem integrableOn_truncLog_mul {ϱ : ℂ → ℝ} (hα : 0 < α)
    (hϱ : ContinuousOn ϱ (Metric.closedBall 0 α)) :
    IntegrableOn (fun x => truncLog α x * ϱ x) (Metric.ball 0 α) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) α).exists_bound_of_continuousOn hϱ
  refine Integrable.mono' (g := fun x => M * truncLog α x)
    ((Screening.integrable_truncLog hα).const_mul M).integrableOn ?_ ?_
  · exact ((Screening.measurable_truncLog α).aestronglyMeasurable.mul
      ((hϱ.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball))
  · refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Screening.truncLog_nonneg α x)]
    have h1 := hM x (Metric.ball_subset_closedBall hx)
    rw [Real.norm_eq_abs] at h1
    calc truncLog α x * |ϱ x| ≤ truncLog α x * M :=
          mul_le_mul_of_nonneg_left h1 (Screening.truncLog_nonneg α x)
      _ = M * truncLog α x := mul_comm _ _

/-- The annular integrals `∫_{ε ≤ ‖x‖ < α} h` converge to `∫_{B(0,α)} h`. -/
theorem tendsto_integral_annulus {h : ℂ → ℝ} (hh : IntegrableOn h (Metric.ball 0 α)) :
    Tendsto (fun ε : ℝ => ∫ x in {x : ℂ | ‖x‖ ∈ Ico ε α}, h x) (𝓝[>] 0)
      (𝓝 (∫ x in Metric.ball 0 α, h x)) := by
  set H : ℂ → ℝ := (Metric.ball (0 : ℂ) α).indicator h with hH
  have hHi : Integrable H := (integrable_indicator_iff measurableSet_ball).2 hh
  have hS : ∀ ε : ℝ, MeasurableSet {x : ℂ | ‖x‖ ∈ Ico ε α} :=
    fun ε => measurable_norm measurableSet_Ico
  have hSsub : ∀ ε : ℝ, {x : ℂ | ‖x‖ ∈ Ico ε α} ⊆ Metric.ball 0 α := by
    intro ε x hx
    rw [mem_ball_zero_iff]; exact hx.2
  have hind : ∀ ε : ℝ, ∫ x in {x : ℂ | ‖x‖ ∈ Ico ε α}, h x =
      ∫ x, {x : ℂ | ‖x‖ ∈ Ico ε α}.indicator H x := by
    intro ε
    rw [← integral_indicator (hS ε)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ {x : ℂ | ‖x‖ ∈ Ico ε α}
    · rw [indicator_of_mem hx, indicator_of_mem hx, hH, indicator_of_mem (hSsub ε hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
  simp only [hind]
  have e : ∫ x in Metric.ball (0 : ℂ) α, h x = ∫ x, H x := by
    rw [hH, integral_indicator measurableSet_ball]
  rw [e]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖H x‖) ?_ ?_ hHi.norm ?_
  · exact Eventually.of_forall fun ε => hHi.aestronglyMeasurable.indicator (hS ε)
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun x => norm_indicator_le_norm_self _ _
  · filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with x hx
    have hx0 : x ≠ 0 := hx
    by_cases hxa : ‖x‖ < α
    · have hxb : x ∈ Metric.ball (0 : ℂ) α := by rwa [mem_ball_zero_iff]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.2 hx0)] with ε hε
      rw [indicator_of_mem (show x ∈ {x : ℂ | ‖x‖ ∈ Ico ε α} from ⟨hε.2.le, hxa⟩)]
    · have : ∀ ε : ℝ, x ∉ {x : ℂ | ‖x‖ ∈ Ico ε α} := fun ε hx' => hxa hx'.2
      have hxb : x ∉ Metric.ball (0 : ℂ) α := by rwa [mem_ball_zero_iff]
      simp only [this, indicator_of_notMem, not_false_eq_true, hH, hxb]
      exact tendsto_const_nhds

theorem polar_annulus_eq {ϱ : ℂ → ℝ} {ε : ℝ} (hε : 0 < ε) (hεα : ε ≤ α)
    (hϱ : ContinuousOn ϱ (Metric.closedBall 0 α)) :
    ∫ x in {x : ℂ | ‖x‖ ∈ Ico ε α}, truncLog α x * ϱ x =
      ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α,
        (Real.log α - Real.log r) * (r * ϱ (polarPt r θ)) := by
  have hnorm : ∀ r θ : ℝ, 0 < r → ‖(r : ℂ) * Torus.dir θ‖ = r := fun r θ hr => by
    rw [Torus.norm_ofReal_mul_dir, abs_of_pos hr]
  have hform : ∀ r θ : ℝ, r ∈ Icc ε α →
      (r * (truncLog α ((r : ℂ) * Torus.dir θ) * ϱ ((r : ℂ) * Torus.dir θ))) =
        (Real.log α - Real.log r) * (r * ϱ (polarPt r θ)) := by
    intro r θ hr
    have hr0 : 0 < r := lt_of_lt_of_le hε hr.1
    rw [Screening.truncLog_eq_log_sub (by rw [hnorm r θ hr0]; exact hr0)
      (by rw [hnorm r θ hr0]; exact hr.2), hnorm r θ hr0]
    have : (r : ℂ) * Torus.dir θ = polarPt r θ := rfl
    rw [this]; ring
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.1 * (truncLog α ((p.1 : ℂ) * Torus.dir p.2) *
      ϱ ((p.1 : ℂ) * Torus.dir p.2))) (Icc ε α ×ˢ Icc (-Real.pi) Real.pi) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.log α - Real.log p.1) * (p.1 * ϱ (polarPt p.1 p.2)))
        (Icc ε α ×ˢ Icc (-Real.pi) Real.pi) := by
      refine (continuousOn_logWeight hε).mul (continuous_fst.continuousOn.mul ?_)
      refine hϱ.comp continuous_polarPt.continuousOn fun p hp => ?_
      rw [mem_closedBall_zero_iff, norm_polarPt (lt_of_lt_of_le hε hp.1.1).le]; exact hp.1.2
    exact h1.congr fun p hp => hform p.1 p.2 hp.1
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * (truncLog α ((p.1 : ℂ) * Torus.dir p.2) *
      ϱ ((p.1 : ℂ) * Torus.dir p.2))) (Ico ε α ×ˢ Ioo (-Real.pi) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
  have := Torus.integral_polar_radial (f := fun x : ℂ => truncLog α x * ϱ x) measurableSet_Ico
    (fun r hr => lt_of_lt_of_le hε hr.1) hint
  rw [this, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  rw [Torus.setIntegral_Ico_eq_intervalIntegral hεα]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hεα] at hr
  exact hform r θ hr

theorem integral_polarPt_eq_circleAverage (u : ℂ → ℝ) (α : ℝ) :
    ∫ θ in (-Real.pi)..Real.pi, u (polarPt α θ) = 2 * Real.pi * Real.circleAverage u 0 α := by
  have h := Screening.integral_Ioo_circleMap_eq u α
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  simp only [polarPt_eq_circleMap]
  rw [h, Real.circleAverage_def, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **Radial Green identity** (centre `0`): if `Δu = 2π ϱ` off the centre in `\bar B(0, α)`, `u` is
`C¹` at `0` and `C²` elsewhere on `\bar B(0, α)`, then `⨍_{∂B(0,α)} u - u(0) = ∫_{B(0,α)} f_α ϱ`. -/
theorem circleAverage_sub_eq_integral_zero {ϱ : ℂ → ℝ} (hα : 0 < α) (hu1 : ContDiffAt ℝ 1 u 0)
    (hu2 : ∀ x, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 u x)
    (hϱ : ContinuousOn ϱ (Metric.closedBall 0 α))
    (hΔ : ∀ x, x ≠ 0 → ‖x‖ ≤ α → Laplacian.laplacian u x = 2 * Real.pi * ϱ x) :
    Real.circleAverage u 0 α - u 0 = ∫ x in Metric.ball 0 α, truncLog α x * ϱ x := by
  have hcb := continuousOn_closedBall_of_c1_c2 hu1 hu2
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ α := by
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hα] with ε h1 h2 using ⟨h1, h2.2⟩
  have hmem : ∀ ε : ℝ, 0 < ε → ε ≤ α → ∀ θ, polarPt ε θ ∈ Metric.closedBall (0 : ℂ) α := by
    intro ε h1 h2 θ
    rw [mem_closedBall_zero_iff, norm_polarPt h1.le]; exact h2
  set A : ℝ := ∫ θ in (-Real.pi)..Real.pi, u (polarPt α θ) with hA
  have hid : ∀ᶠ ε : ℝ in 𝓝[>] 0, 2 * Real.pi * ∫ x in {x : ℂ | ‖x‖ ∈ Ico ε α}, truncLog α x * ϱ x =
      A - (∫ θ in (-Real.pi)..Real.pi, u (polarPt ε θ)) -
        ∫ θ in (-Real.pi)..Real.pi,
          (Real.log α - Real.log ε) * (ε * radialComp (pd₁ u) (pd₂ u) ε θ) := by
    filter_upwards [hev] with ε hε
    have hrad := radial_identity hu2 hε.1 hε.2
    have hL : ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α,
        (Real.log α - Real.log r) * (r * Laplacian.laplacian u (polarPt r θ)) =
        2 * Real.pi * ∫ θ in (-Real.pi)..Real.pi, ∫ r in ε..α,
          (Real.log α - Real.log r) * (r * ϱ (polarPt r θ)) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hε.2] at hr
      have hr0 : 0 < r := lt_of_lt_of_le hε.1 hr.1
      rw [hΔ _ (polarPt_ne_zero hr0 θ) (by rw [norm_polarPt hr0.le]; exact hr.2)]
      ring
    rw [polar_annulus_eq hε.1 hε.2 hϱ, ← hL, hrad]
    have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    have c1 : ContinuousOn (fun θ => u (polarPt α θ)) (uIcc (-Real.pi) Real.pi) :=
      hcb.comp (continuous_polarPt_theta α).continuousOn (fun θ _ => hmem α hα le_rfl θ)
    have c2 : ContinuousOn (fun θ => u (polarPt ε θ)) (uIcc (-Real.pi) Real.pi) :=
      hcb.comp (continuous_polarPt_theta ε).continuousOn (fun θ _ => hmem ε hε.1 hε.2 θ)
    have c3 : ContinuousOn (fun θ => (Real.log α - Real.log ε) *
        (ε * radialComp (pd₁ u) (pd₂ u) ε θ)) (uIcc (-Real.pi) Real.pi) := by
      refine continuousOn_const.mul (continuousOn_const.mul ?_)
      have := (continuousOn_radialComp_le (contDiffAt_pd₁_le hu2) (contDiffAt_pd₂_le hu2)).comp
        (continuous_const (y := ε) |>.prodMk continuous_id).continuousOn
        (s := uIcc (-Real.pi) Real.pi) (t := {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ α})
        (fun θ _ => ⟨hε.1, hε.2⟩)
      exact this
    have h12 : IntervalIntegrable (fun θ => u (polarPt α θ) - u (polarPt ε θ)) volume
        (-Real.pi) Real.pi := (c1.sub c2).intervalIntegrable
    rw [intervalIntegral.integral_sub h12 c3.intervalIntegrable,
      intervalIntegral.integral_sub c1.intervalIntegrable c2.intervalIntegrable]
  have hlim1 := tendsto_integral_circle hα hu1 hu2
  have hlim2 := tendsto_boundary_term (α := α) hu1
  have hlimR : Tendsto (fun ε : ℝ => A - (∫ θ in (-Real.pi)..Real.pi, u (polarPt ε θ)) -
      ∫ θ in (-Real.pi)..Real.pi, (Real.log α - Real.log ε) * (ε * radialComp (pd₁ u) (pd₂ u) ε θ))
      (𝓝[>] 0) (𝓝 (A - 2 * Real.pi * u 0 - 0)) :=
    (tendsto_const_nhds.sub hlim1).sub hlim2
  have hlimL := (tendsto_integral_annulus (integrableOn_truncLog_mul hα hϱ)).const_mul
    (2 * Real.pi)
  have := tendsto_nhds_unique (hlimL.congr' hid) hlimR
  have hA' : A = 2 * Real.pi * Real.circleAverage u 0 α := integral_polarPt_eq_circleAverage u α
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpi
  rw [this, hA']
  ring

/-- **Radial Green identity** (general centre `p`): for `Δu = 2π ϱ` on `\bar B(p, α) ∖ {p}`, `u` of class `C¹`
at `p` and `C²` on `\bar B(p, α) ∖ {p}`, `⨍_{∂B(p,α)} u - u(p) = ∫_{B(p,α)} f_α(· - p) ϱ`. -/
theorem circleAverage_sub_eq_integral {ϱ : ℂ → ℝ} {p : ℂ} (hα : 0 < α) (hu1 : ContDiffAt ℝ 1 u p)
    (hu2 : ∀ x, x ≠ p → ‖x - p‖ ≤ α → ContDiffAt ℝ 2 u x)
    (hϱ : ContinuousOn ϱ (Metric.closedBall p α))
    (hΔ : ∀ x, x ≠ p → ‖x - p‖ ≤ α → Laplacian.laplacian u x = 2 * Real.pi * ϱ x) :
    Real.circleAverage u p α - u p = ∫ x in Metric.ball p α, truncLog α (x - p) * ϱ x := by
  have hadd : ContDiff ℝ ∞ (fun z : ℂ => z + p) := contDiff_id.add contDiff_const
  have hmap : ∀ z : ℂ, ‖z‖ ≤ α → ‖z + p - p‖ ≤ α := fun z hz => by simpa using hz
  have h1 : ContDiffAt ℝ 1 (fun z => u (z + p)) 0 := by
    have h0 : ContDiffAt ℝ 1 u ((fun z : ℂ => z + p) 0) := by simpa using hu1
    exact h0.comp (0 : ℂ) (hadd.contDiffAt.of_le (by norm_num))
  have h2 : ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ α → ContDiffAt ℝ 2 (fun z => u (z + p)) x := fun x hx hxα =>
    (hu2 (x + p) (fun h => hx (by simpa using h)) (hmap x hxα)).comp x
      (hadd.contDiffAt.of_le (by norm_num))
  have h3 : ContinuousOn (fun z => ϱ (z + p)) (Metric.closedBall 0 α) :=
    hϱ.comp hadd.continuous.continuousOn (fun z hz => by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_closedBall_iff_norm]; exact hmap z hz)
  have h4 : ∀ x : ℂ, x ≠ 0 → ‖x‖ ≤ α →
      Laplacian.laplacian (fun z => u (z + p)) x = 2 * Real.pi * ϱ (x + p) := fun x hx hxα => by
    have := laplacian_comp_sub u (-p) x
    simp only [sub_neg_eq_add] at this
    rw [this]
    exact hΔ (x + p) (fun h => hx (by simpa using h)) (hmap x hxα)
  have key := circleAverage_sub_eq_integral_zero (u := fun z => u (z + p))
    (ϱ := fun z => ϱ (z + p)) hα h1 h2 h3 h4
  have hc : Real.circleAverage (fun z => u (z + p)) 0 α = Real.circleAverage u p α := by
    exact Real.circleAverage_map_add_const
  rw [hc] at key
  simp only [zero_add] at key
  rw [key]
  have hmp := (measurePreserving_add_right (volume : Measure ℂ) p).setIntegral_preimage_emb
    (measurableEmbedding_addRight p) (fun x => truncLog α (x - p) * ϱ x) (Metric.ball p α)
  have hpre : (fun z : ℂ => z + p) ⁻¹' Metric.ball p α = Metric.ball 0 α := by
    ext z; simp
  rw [hpre] at hmp
  rw [← hmp]
  simp

end Limit

end Sphere

end SandierSerfaty

end
