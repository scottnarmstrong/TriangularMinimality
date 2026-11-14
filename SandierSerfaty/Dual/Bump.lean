/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Radial cut-off bumps with a `1/ε` gradient bound

`cutBump ε c x = ψ((2ε - ‖x - c‖)/ε)` with `ψ = Real.smoothTransition`: it equals `1` on
`closedBall c ε`, `0` outside `ball c (2ε)`, is smooth (`contDiff_cutBump`) and is `(L/ε)`-Lipschitz
with `L` independent of `ε` and `c` (`lipschitzWith_cutBump`). They are the scale-`ε` cut-offs used to
integrate by parts away from the charges.
-/

open Set Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

/-- The radial cut-off bump of the paper's proof scheme: `1` on `B̄(c, ε)`, `0` off `B(c, 2ε)`. -/
@[expose] noncomputable def cutBump (ε : ℝ) (c x : ℂ) : ℝ :=
  Real.smoothTransition ((2 * ε - ‖x - c‖) / ε)

variable {ε : ℝ} {c x : ℂ}

theorem cutBump_eq_one (hε : 0 < ε) (h : ‖x - c‖ ≤ ε) : cutBump ε c x = 1 := by
  unfold cutBump
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ hε]; linarith

theorem cutBump_eq_zero (hε : 0 < ε) (h : 2 * ε ≤ ‖x - c‖) : cutBump ε c x = 0 := by
  unfold cutBump
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le

theorem cutBump_nonneg : 0 ≤ cutBump ε c x := Real.smoothTransition.nonneg _

theorem cutBump_le_one : cutBump ε c x ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_cutBump (hε : 0 < ε) : ContDiff ℝ ∞ (cutBump ε c) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x = c
  · subst hx
    have : cutBump ε x =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [ball_mem_nhds x hε] with y hy
      exact cutBump_eq_one hε (by have := mem_ball_iff_norm.1 hy; exact this.le)
    exact (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq this
  · have h1 : ContDiffAt ℝ ∞ (fun y : ℂ => ‖y - c‖) x :=
      (contDiffAt_norm ℝ (sub_ne_zero.2 hx)).comp x (contDiffAt_id.sub contDiffAt_const)
    have h2 : ContDiffAt ℝ ∞ (fun y : ℂ => (2 * ε - ‖y - c‖) / ε) x :=
      (contDiffAt_const.sub h1).div_const ε
    exact Real.smoothTransition.contDiff.contDiffAt.comp x h2

/-- The basic cut-off profile is Lipschitz. -/
theorem exists_lipschitzWith_smoothTransition : ∃ L : NNReal, LipschitzWith L Real.smoothTransition := by
  obtain ⟨L, hL⟩ := ((Real.smoothTransition.contDiff (n := 1)).contDiffOn (s := Icc (0 : ℝ) 1)).exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 1) isCompact_Icc
  refine ⟨L, ?_⟩
  have hclamp : ∀ t : ℝ, Real.smoothTransition t = Real.smoothTransition (max 0 (min 1 t)) := by
    intro t
    rcases le_total t 0 with h | h
    · rw [Real.smoothTransition.zero_of_nonpos h]
      have : max 0 (min 1 t) = 0 := by simp [h]
      rw [this, Real.smoothTransition.zero_of_nonpos le_rfl]
    · rcases le_total 1 t with h' | h'
      · rw [Real.smoothTransition.one_of_one_le h']
        have : max 0 (min 1 t) = 1 := by simp [h']
        rw [this, Real.smoothTransition.one_of_one_le le_rfl]
      · have : max 0 (min 1 t) = t := by simp [h, h']
        rw [this]
  have hcl : LipschitzWith 1 (fun t : ℝ => max 0 (min 1 t)) :=
    (LipschitzWith.id.const_min 1).const_max 0
  have := hL.comp hcl.lipschitzOnWith (s := univ) (fun t _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩)
  rw [mul_one] at this
  have h2 : Real.smoothTransition = Real.smoothTransition ∘ fun t : ℝ => max 0 (min 1 t) :=
    funext hclamp
  rw [h2]
  exact lipschitzOnWith_univ.1 this

theorem exists_lipschitzWith_cutBump :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ε > 0, ∀ c : ℂ, LipschitzWith (Real.toNNReal (L / ε)) (cutBump ε c) := by
  obtain ⟨L, hL⟩ := exists_lipschitzWith_smoothTransition
  refine ⟨L, L.2, fun ε hε c => ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  have h1 := hL.dist_le_mul ((2 * ε - ‖x - c‖) / ε) ((2 * ε - ‖y - c‖) / ε)
  refine h1.trans ?_
  have : dist ((2 * ε - ‖x - c‖) / ε) ((2 * ε - ‖y - c‖) / ε) ≤ dist x y / ε := by
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hε]
    refine div_le_div_of_nonneg_right ?_ hε.le
    have := abs_norm_sub_norm_le (x - c) (y - c)
    rw [dist_eq_norm]
    calc |2 * ε - ‖x - c‖ - (2 * ε - ‖y - c‖)| = |‖y - c‖ - ‖x - c‖| := by ring_nf
      _ ≤ ‖(y - c) - (x - c)‖ := abs_norm_sub_norm_le _ _
      _ = ‖x - y‖ := by rw [← norm_neg]; congr 1; ring
  calc (L : ℝ) * dist ((2 * ε - ‖x - c‖) / ε) ((2 * ε - ‖y - c‖) / ε) ≤ L * (dist x y / ε) :=
        mul_le_mul_of_nonneg_left this L.2
    _ = L / ε * dist x y := by ring

theorem norm_fderiv_cutBump_le {L : ℝ} (hL : ∀ ε > 0, ∀ c : ℂ, LipschitzWith (Real.toNNReal (L / ε)) (cutBump ε c))
    (hL0 : 0 ≤ L) (hε : 0 < ε) (c x : ℂ) : ‖fderiv ℝ (cutBump ε c) x‖ ≤ L / ε := by
  have := norm_fderiv_le_of_lipschitz ℝ (hL ε hε c) (x₀ := x)
  rwa [Real.coe_toNNReal _ (by positivity)] at this

end Dual

end SandierSerfaty

end
