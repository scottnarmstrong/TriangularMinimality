/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.Green
public import SandierSerfaty.Torus.ScreenedGreen
public import SandierSerfaty.Torus.Periodize
public import SandierSerfaty.Screening.TruncLogCalculus
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Test functions for the projection onto the torus

For the projection step (I5, the screening note's §5) the truncated torus potential
`H - ∑ᵢ f_η(· - aᵢ)` is split, in a neighbourhood of the fundamental square, into a smooth periodic
part and compactly supported Lipschitz parts. With `G = torusGreen Γ`, a smooth bump `b` equal to
`1` on `closedBall 0 η` and supported in a small ball:

* `Torus.greenReg Γ y = G y + log ‖y‖` (`= torusRobin Γ` at `0`), smooth near `0`
  (`Torus.contDiffAt_greenReg`);
* `projSmooth Γ b = G · (1 - ∑_γ b(γ + ·))`: smooth and `Γ`-periodic (`contDiff_projSmooth`,
  `projSmooth_add_period`), hence Lipschitz (`exists_lipschitzWith_of_periodic`);
* `projSing Γ b η = b · (greenReg Γ - log (max ‖·‖ η))`: Lipschitz with compact support
  (`exists_lipschitzWith_projSing`, `projSing_eq_zero`);
* `projSmooth_add_projSing`: `projSmooth + projSing = G - f_η` off `0`, where the periodization of
  `b` reduces to `b`.

This replaces the "Lipschitz truncated potential" of the screening note's Lemma `lem:Htilde` by an explicit
decomposition (no segment argument).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

public section

namespace SandierSerfaty

namespace Screening

open Torus

variable (Γ : Submodule ℤ ℂ)

/-- `-log (max ‖y‖ η)`: equal to `-log ‖y‖` outside `B(0, η)` and to `-log η` inside. -/
@[expose] noncomputable def logOut (η : ℝ) (y : ℂ) : ℝ := -Real.log (max ‖y‖ η)

/-- The smooth periodic part `G_Γ · (1 - ∑_γ b(γ + ·))`. -/
@[expose] noncomputable def projSmooth (b : ContDiffBump (0 : ℂ)) (y : ℂ) : ℝ :=
  torusGreen Γ y * (1 - periodize Γ b y)

/-- The compactly supported Lipschitz part `b · (greenReg Γ + logOut η)`. -/
@[expose] noncomputable def projSing (b : ContDiffBump (0 : ℂ)) (η : ℝ) (y : ℂ) : ℝ :=
  b y * (greenReg Γ y + logOut η y)

variable {Γ}

/-! ### Periodization of a function with small support -/

/-- If `f` vanishes outside `ball 0 s` and every translate `γ + z`, `γ ≠ γ₀`, is outside it, the
periodization at `z` is the single term `f (γ₀ + z)`. -/
theorem periodize_eq_single {f : ℂ → ℝ} {s : ℝ} (hf : ∀ w, s ≤ ‖w‖ → f w = 0) {z : ℂ} (γ₀ : Γ)
    (h : ∀ γ : Γ, γ ≠ γ₀ → s ≤ ‖(γ : ℂ) + z‖) : periodize Γ f z = f ((γ₀ : ℂ) + z) := by
  unfold periodize
  exact tsum_eq_single γ₀ fun γ hγ => hf _ (h γ hγ)

theorem bump_eq_zero_of_le_norm (b : ContDiffBump (0 : ℂ)) {w : ℂ} (hw : b.rOut ≤ ‖w‖) :
    b w = 0 :=
  b.zero_of_le_dist (by rwa [dist_zero_right])

theorem bump_eq_one_of_norm_le (b : ContDiffBump (0 : ℂ)) {w : ℂ} (hw : ‖w‖ ≤ b.rIn) :
    b w = 1 :=
  b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hw)

/-- Near a lattice point `y`, the periodized bump is `b (· - y)`. -/
theorem periodize_bump_eq {d : ℝ} (hd : ∀ γ ∈ Γ, γ ≠ 0 → d ≤ ‖γ‖) (b : ContDiffBump (0 : ℂ))
    {y z : ℂ} (hy : y ∈ Γ) (hz : ‖z - y‖ + b.rOut ≤ d) :
    periodize Γ b z = b (z - y) := by
  have h := periodize_eq_single (f := b) (s := b.rOut) (fun w hw => bump_eq_zero_of_le_norm b hw)
    (z := z) ⟨-y, Γ.neg_mem hy⟩ fun γ hγ => ?_
  · rw [h]; congr 1; push_cast; ring
  · have hne : (γ : ℂ) + y ≠ 0 := by
      intro h0; apply hγ; ext; linear_combination h0
    have h1 := hd _ (Γ.add_mem γ.2 hy) hne
    have h2 : ‖(γ : ℂ) + y‖ ≤ ‖(γ : ℂ) + z‖ + ‖z - y‖ := by
      have e : (γ : ℂ) + y = ((γ : ℂ) + z) - (z - y) := by ring
      rw [e]; exact norm_sub_le _ _
    linarith

/-! ### The regular part of the Green function -/

section Green

variable [DiscreteTopology Γ] [IsZLattice ℝ Γ]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem greenReg_of_ne {y : ℂ} (hy : y ≠ 0) : greenReg Γ y = torusGreen Γ y + Real.log ‖y‖ := by
  simp [greenReg, hy]

/-! ### The smooth periodic part -/

theorem projSmooth_add_period (b : ContDiffBump (0 : ℂ)) {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    projSmooth Γ b (x + γ) = projSmooth Γ b x := by
  unfold projSmooth
  rw [torusGreen_add_period Γ hγ x, periodize_add_period _ hγ x]

theorem contDiff_projSmooth {d : ℝ} (hd : ∀ γ ∈ Γ, γ ≠ 0 → d ≤ ‖γ‖) (b : ContDiffBump (0 : ℂ))
    (hb : b.rIn + b.rOut ≤ d) : ContDiff ℝ ∞ (projSmooth Γ b) := by
  have hper : ContDiff ℝ ∞ (periodize Γ b) :=
    contDiff_periodize (c := 0) (ρ := b.rOut) b.contDiff fun w hw => bump_eq_zero_of_le_norm b
      (by rw [sub_zero] at hw; exact hw.le)
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : y ∈ Γ
  · refine contDiffAt_const (c := (0 : ℝ)) |>.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds y b.rIn_pos] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    unfold projSmooth
    rw [periodize_bump_eq hd b hy (by linarith), bump_eq_one_of_norm_le b hz.le, sub_self, mul_zero]
  · exact (contDiffAt_torusGreen Γ hy).mul (contDiffAt_const.sub hper.contDiffAt)

end Green

/-- A `C¹` periodic function is Lipschitz. -/
theorem exists_lipschitzWith_of_periodic [DiscreteTopology Γ] [IsZLattice ℝ Γ] {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) : ∃ K, LipschitzWith K f := by
  have hc : Continuous fun x => ‖fderiv ℝ f x‖ := (hf.continuous_fderiv one_ne_zero).norm
  obtain ⟨M, hM⟩ := exists_bound_of_periodic Γ hc fun γ hγ x => by
    simp only [fderiv_periodic Γ hper hγ x]
  refine ⟨Real.toNNReal M, lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero)
    fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (le_abs_self _).trans ((hM x).trans (le_max_left _ _))

/-! ### The singular Lipschitz part -/

theorem lipschitzWith_logOut {η : ℝ} (hη : 0 < η) :
    LipschitzWith (Real.toNNReal η⁻¹) (logOut η) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hη.le)]
  unfold logOut
  have h1 := abs_log_sub_log_le hη (le_max_right ‖x‖ η) (le_max_right ‖y‖ η)
  have h2 : |max ‖x‖ η - max ‖y‖ η| ≤ dist x y :=
    (abs_max_sub_max_le_abs _ _ _).trans (by rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y)
  rw [show -Real.log (max ‖x‖ η) - -Real.log (max ‖y‖ η) =
    -(Real.log (max ‖x‖ η) - Real.log (max ‖y‖ η)) by ring, abs_neg]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hη.le))

/-- Product of a bounded Lipschitz function `f` and a Lipschitz function `g` bounded where `f ≠ 0`. -/
theorem exists_lipschitzWith_mul {f g : ℂ → ℝ} {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) {Mf Mg : ℝ} (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, f x ≠ 0 → |g x| ≤ Mg) :
    ∃ K, LipschitzWith K fun x => f x * g x := by
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf 0)
  refine ⟨Real.toNNReal (max Mg 0 * Kf + Mf * Kg), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have hfx := hf.dist_le_mul x y
  have hgx := hg.dist_le_mul x y
  rw [Real.dist_eq] at hfx hgx
  have hdist : 0 ≤ dist x y := dist_nonneg
  have key : ∀ u v : ℂ, f u ≠ 0 → |f u * g u - f v * g v| ≤ (max Mg 0 * Kf + Mf * Kg) * dist u v := by
    intro u v hu
    have hfu := hf.dist_le_mul u v
    have hgu := hg.dist_le_mul u v
    rw [Real.dist_eq] at hfu hgu
    have e : f u * g u - f v * g v = g u * (f u - f v) + f v * (g u - g v) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |g u| * |f u - f v| ≤ max Mg 0 * (Kf * dist u v) :=
      mul_le_mul ((hMg u hu).trans (le_max_left _ _)) hfu (abs_nonneg _) (le_max_right _ _)
    have h2 : |f v| * |g u - g v| ≤ Mf * (Kg * dist u v) :=
      mul_le_mul (hMf v) hgu (abs_nonneg _) hMf0
    nlinarith
  by_cases hx : f x ≠ 0
  · exact key x y hx
  · by_cases hy : f y ≠ 0
    · rw [abs_sub_comm, dist_comm]; exact key y x hy
    · simp only [ne_eq, not_not] at hx hy
      rw [hx, hy, zero_mul, zero_mul, sub_self, abs_zero]
      positivity

theorem projSing_eq_zero (b : ContDiffBump (0 : ℂ)) (η : ℝ) {y : ℂ} (hy : b.rOut ≤ ‖y‖) :
    projSing Γ b η y = 0 := by
  unfold projSing; rw [bump_eq_zero_of_le_norm b hy, zero_mul]

section Green

variable [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem contDiff_bump_mul_greenReg {d : ℝ} (hd : ∀ γ ∈ Γ, γ ≠ 0 → d ≤ ‖γ‖)
    (b : ContDiffBump (0 : ℂ)) (hb : b.rOut < d) :
    ContDiff ℝ ∞ fun y => b y * greenReg Γ y := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : ‖y‖ < d
  · refine b.contDiff.contDiffAt.mul (Torus.contDiffAt_greenReg Γ ?_)
    by_cases h0 : y = 0
    · exact Or.inl h0
    · exact Or.inr fun hyΓ => absurd (hd y hyΓ h0) (not_le.2 hy)
  · refine contDiffAt_const (c := (0 : ℝ)) |>.congr_of_eventuallyEq ?_
    have hopen : IsOpen {z : ℂ | b.rOut < ‖z‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds (show b.rOut < ‖y‖ by linarith [not_lt.1 hy])] with z hz
    rw [bump_eq_zero_of_le_norm b (le_of_lt hz), zero_mul]

/-- **The singular part is Lipschitz.** -/
theorem exists_lipschitzWith_projSing {d : ℝ} (hd : ∀ γ ∈ Γ, γ ≠ 0 → d ≤ ‖γ‖)
    (b : ContDiffBump (0 : ℂ)) (hb : b.rOut < d) {η : ℝ} (hη : 0 < η) :
    ∃ K, LipschitzWith K (projSing Γ b η) := by
  have hc1 : HasCompactSupport fun y => b y * greenReg Γ y := b.hasCompactSupport.mul_right
  obtain ⟨K1, hK1⟩ := (contDiff_bump_mul_greenReg hd b hb).lipschitzWith_of_hasCompactSupport hc1
    (by simp)
  obtain ⟨Kb, hKb⟩ := (b.contDiff (n := 1)).lipschitzWith_of_hasCompactSupport b.hasCompactSupport
    (by simp)
  set T : ℝ := max b.rOut η with hT
  obtain ⟨K2, hK2⟩ := exists_lipschitzWith_mul hKb (lipschitzWith_logOut hη)
    (Mf := 1) (Mg := |Real.log η| + |Real.log T|)
    (fun x => by rw [abs_of_nonneg b.nonneg]; exact b.le_one) fun x hx => by
      have hxr : ‖x‖ < b.rOut := not_le.1 fun h => hx (bump_eq_zero_of_le_norm b h)
      unfold logOut
      have h1 : η ≤ max ‖x‖ η := le_max_right _ _
      have h2 : max ‖x‖ η ≤ T := max_le_max hxr.le le_rfl
      have l1 : Real.log η ≤ Real.log (max ‖x‖ η) := Real.log_le_log hη h1
      have l2 : Real.log (max ‖x‖ η) ≤ Real.log T := Real.log_le_log (hη.trans_le h1) h2
      rw [abs_neg, abs_le]
      constructor <;> linarith [neg_abs_le (Real.log η), le_abs_self (Real.log T),
        abs_nonneg (Real.log η), abs_nonneg (Real.log T)]
  refine ⟨K1 + K2, ?_⟩
  have e : projSing Γ b η = (fun y => b y * greenReg Γ y) + fun y => b y * logOut η y := by
    ext y; simp only [projSing, Pi.add_apply]; ring
  rw [e]
  exact hK1.add hK2

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
/-- **The splitting identity.** Off `0`, where the periodized bump reduces to `b`,
`projSmooth + projSing = G_Γ - f_η`. -/
theorem projSmooth_add_projSing (b : ContDiffBump (0 : ℂ)) {η : ℝ} (hη : 0 < η)
    (hηb : η ≤ b.rIn) {y : ℂ} (hy0 : y ≠ 0) (hper : periodize Γ b y = b y) :
    projSmooth Γ b y + projSing Γ b η y = torusGreen Γ y - truncLog η y := by
  unfold projSmooth projSing logOut truncLog
  rw [hper, greenReg_of_ne hy0]
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  rcases le_total ‖y‖ η with h | h
  · rw [bump_eq_one_of_norm_le b (h.trans hηb), max_eq_right h,
      max_eq_left (by linarith [Real.log_le_log hn h])]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith [Real.log_le_log hη h])]
    ring

end Green

end Screening

end SandierSerfaty

end
