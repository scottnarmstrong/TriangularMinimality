/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.Bump
public import SandierSerfaty.Analysis.PolarAnnulus
public import SandierSerfaty.Analysis.PeriodicGreen
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The pairing of the logarithmic singularity with a Lipschitz function, at scale `ε`

Near a charge `c`, the potential is `u = s - log ‖· - c‖` with `s` smooth. For the cut-off
`β = cutBump ε c` and a Lipschitz `w`:
`∫ w ⟨∇β, ∇u⟩ = 2π w(c) + O(ε)` (`local_pairing_estimate`). The exact input is
`∫ ‖x - c‖⁻² ∂β(x)[x - c] dx = -2π` (`integral_inv_sq_fderiv_cutBump`), the weak form of
`Δ log = 2π δ`; the rest are `O(ε)` bounds on the annulus `ε ≤ ‖x - c‖ ≤ 2ε`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis Torus

variable {ε : ℝ} {c : ℂ}

theorem fderiv_cutBump_eq_zero_of_lt (hε : 0 < ε) {x : ℂ} (hx : ‖x - c‖ < ε) :
    fderiv ℝ (cutBump ε c) x = 0 := by
  have : cutBump ε c =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [isOpen_lt (by fun_prop : Continuous fun y : ℂ => ‖y - c‖) continuous_const
      |>.mem_nhds hx] with y hy
    exact cutBump_eq_one hε hy.le
  rw [this.fderiv_eq]; simp

theorem fderiv_cutBump_eq_zero_of_gt (hε : 0 < ε) {x : ℂ} (hx : 2 * ε < ‖x - c‖) :
    fderiv ℝ (cutBump ε c) x = 0 := by
  have : cutBump ε c =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [isOpen_lt continuous_const (by fun_prop : Continuous fun y : ℂ => ‖y - c‖)
      |>.mem_nhds hx] with y hy
    exact cutBump_eq_zero hε hy.le
  rw [this.fderiv_eq]; simp

/-- **The weak form of `Δ log = 2π δ`** for the cut-off: `∫ ‖x - c‖⁻² ∂β(x)[x - c] = -2π`. -/
theorem integral_inv_sq_fderiv_cutBump (hε : 0 < ε) :
    ∫ x, (‖x - c‖ ^ 2)⁻¹ * fderiv ℝ (cutBump ε c) x (x - c) = -(2 * Real.pi) := by
  set v : ℂ → ℝ := fun y => cutBump ε c (c + y) with hv
  have hvd : ContDiff ℝ ∞ v := (contDiff_cutBump hε).comp (contDiff_const.add contDiff_id)
  have h := integral_fderiv_div_sq_annulus (v := v) (R := 4 * ε) (ε := ε) (ρ := 3 * ε)
    (hvd.of_le (by norm_cast)).contDiffOn hε (by linarith) (by linarith)
  have hfd : ∀ y, fderiv ℝ v y = fderiv ℝ (cutBump ε c) (c + y) := fun y => by
    simp only [hv]; exact fderiv_comp_add_left c
  -- the integrand on the plane, in the frame centred at `c`
  have hshift : ∫ x, (‖x - c‖ ^ 2)⁻¹ * fderiv ℝ (cutBump ε c) x (x - c) =
      ∫ y, (‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y := by
    rw [← integral_add_left_eq_self (fun x => (‖x - c‖ ^ 2)⁻¹ * fderiv ℝ (cutBump ε c) x (x - c)) c]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hfd]
  rw [hshift]
  have hsupp : ∫ y, (‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y =
      ∫ y in {y : ℂ | ε ≤ ‖y‖ ∧ ‖y‖ < 3 * ε}, (‖y‖ ^ 2)⁻¹ * fderiv ℝ v y y := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    simp only [mem_ofPred_eq, not_and_or, not_le, not_lt] at hy
    rcases hy with hy | hy
    · rw [hfd, fderiv_cutBump_eq_zero_of_lt hε (by simpa using hy)]; simp
    · rw [hfd, fderiv_cutBump_eq_zero_of_gt hε (by simpa using (by linarith : 2 * ε < ‖y‖))]; simp
  rw [hsupp, h]
  have hθ : ∀ θ : ℝ, v (((3 * ε : ℝ) : ℂ) * dir θ) - v (((ε : ℝ) : ℂ) * dir θ) = -1 := by
    intro θ
    have h1 : cutBump ε c (c + ((3 * ε : ℝ) : ℂ) * dir θ) = 0 := by
      refine cutBump_eq_zero hε ?_
      rw [add_sub_cancel_left, norm_ofReal_mul_dir, abs_of_pos (by linarith)]; linarith
    have h2 : cutBump ε c (c + ((ε : ℝ) : ℂ) * dir θ) = 1 := by
      refine cutBump_eq_one hε ?_
      rw [add_sub_cancel_left, norm_ofReal_mul_dir, abs_of_pos hε]
    simp only [hv, h1, h2]; ring
  simp_rw [hθ]
  rw [integral_const_Ioo_pi]; ring

theorem fderiv_apply_eq (f : ℂ → ℝ) (x z : ℂ) :
    fderiv ℝ f x z = z.re * fderiv ℝ f x 1 + z.im * fderiv ℝ f x Complex.I := by
  have : z = (z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [this]
  rw [map_add, map_smul, map_smul]; simp

/-- Pointwise: `⟨∇β, ∇u⟩ = ⟨∇β, ∇s⟩ - ‖x - c‖⁻² ∂β[x - c]` where `∇u = ∇s - (x - c)/‖x - c‖²`. -/
theorem gradDot_eq_of_fderiv (β s u : ℂ → ℝ) {x : ℂ}
    (hu : fderiv ℝ u x = fderiv ℝ s x - (‖x - c‖ ^ 2)⁻¹ • innerSL ℝ (x - c)) :
    gradDot β u x = gradDot β s x - (‖x - c‖ ^ 2)⁻¹ * fderiv ℝ β x (x - c) := by
  have h1 : fderiv ℝ u x 1 = fderiv ℝ s x 1 - (‖x - c‖ ^ 2)⁻¹ * (x - c).re := by
    rw [hu]; simp [Complex.inner]
  have h2 : fderiv ℝ u x Complex.I = fderiv ℝ s x Complex.I - (‖x - c‖ ^ 2)⁻¹ * (x - c).im := by
    rw [hu]; simp [Complex.inner]
  simp only [gradDot, pd₁, pd₂, h1, h2]
  rw [fderiv_apply_eq β x (x - c)]
  ring

theorem measure_annulus_le (hε : 0 < ε) :
    (volume (closedBall c (2 * ε))).toReal ≤ 4 * Real.pi * ε ^ 2 := by
  rw [Measure.addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * ε)]
  have : (↑NNReal.pi : ℝ) = Real.pi := rfl
  have h2 : (↑(NNReal.pi) : ENNReal).toReal = Real.pi := by simp
  rw [h2]; nlinarith [Real.pi_pos]

/-- **Local pairing estimate:** `∫ w ⟨∇β_ε, ∇u⟩ = 2π w(c) + O(ε)`. -/
theorem local_pairing_estimate {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ε > 0, ∀ c : ℂ, LipschitzWith (Real.toNNReal (L / ε)) (cutBump ε c))
    {w : ℂ → ℝ} {Kw : NNReal} (hw : LipschitzWith Kw w) {Mw : ℝ} (hMw : ∀ x, |w x| ≤ Mw)
    {r : ℝ} (hr : 0 < r) {s u : ℂ → ℝ} (hs : ContDiffOn ℝ ∞ s (ball c r))
    (hu : ∀ x ∈ ball c r, x ≠ c →
      fderiv ℝ u x = fderiv ℝ s x - (‖x - c‖ ^ 2)⁻¹ • innerSL ℝ (x - c)) :
    ∃ C : ℝ, ∀ ε ∈ Ioc 0 (r / 4),
      Integrable (fun x => w x * gradDot (cutBump ε c) u x) ∧
      |(∫ x, w x * gradDot (cutBump ε c) u x) - 2 * Real.pi * w c| ≤ C * ε := by
  -- bound for `∇s` near `c`
  have hcont : ContinuousOn (fun x => fderiv ℝ s x) (ball c r) :=
    hs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨Ms, hMs⟩ := (isCompact_closedBall c (r / 2)).exists_bound_of_continuousOn
    (hcont.mono (closedBall_subset_ball (by linarith)))
  have hMs0 : 0 ≤ Ms := (norm_nonneg _).trans (hMs c (mem_closedBall_self (by linarith)))
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw c)
  refine ⟨8 * Real.pi * Mw * L * Ms + 4 * Real.pi * Kw * L, fun ε hε => ?_⟩
  obtain ⟨hε0, hεr⟩ := hε
  set β := cutBump ε c with hβ
  have hfβ : ∀ x, ‖fderiv ℝ β x‖ ≤ L / ε := fun x => norm_fderiv_cutBump_le hL hL0 hε0 c x
  set A : Set ℂ := {x | ε ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ 2 * ε} with hA
  have hnm : Measurable fun x : ℂ => ‖x - c‖ := by fun_prop
  have hAm : MeasurableSet A := (measurableSet_le measurable_const hnm).inter
    (measurableSet_le hnm measurable_const)
  have hAsub : A ⊆ closedBall c (2 * ε) := fun x hx => by
    rw [mem_closedBall, dist_eq_norm]; exact hx.2
  have hAfin : volume A < ⊤ := (measure_mono hAsub).trans_lt measure_closedBall_lt_top
  have hAvol : (volume A).toReal ≤ 4 * Real.pi * ε ^ 2 :=
    (ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono hAsub)).trans
      (measure_annulus_le hε0)
  have hxnA : ∀ x, x ∉ A → fderiv ℝ β x = 0 := by
    intro x hx
    rw [hA, mem_ofPred_eq, not_and_or, not_le, not_le] at hx
    rcases hx with h1 | h2
    · exact fderiv_cutBump_eq_zero_of_lt hε0 h1
    · exact fderiv_cutBump_eq_zero_of_gt hε0 h2
  -- the three functions
  set F1 : ℂ → ℝ := fun x => w x * gradDot β s x with hF1
  set F3 : ℂ → ℝ := fun x => (‖x - c‖ ^ 2)⁻¹ * fderiv ℝ β x (x - c) with hF3
  set F2 : ℂ → ℝ := fun x => (w x - w c) * F3 x with hF2
  have hid : ∀ x, w x * gradDot β u x = F1 x - F2 x - w c * F3 x := by
    intro x
    by_cases hxA : x ∈ A
    · have hxb : x ∈ ball c r := by
        rw [mem_ball, dist_eq_norm]; linarith [hxA.2]
      have hxc : x ≠ c := by
        intro h
        have h1 := hxA.1
        rw [h, sub_self, norm_zero] at h1; linarith
      rw [gradDot_eq_of_fderiv β s u (hu x hxb hxc)]
      simp only [hF1, hF2, hF3]; ring
    · have h0 := hxnA x hxA
      simp only [hF1, hF2, hF3, gradDot, pd₁, pd₂, h0]; simp
  have hF3supp : ∀ x, x ∉ A → F3 x = 0 := fun x hx => by simp [hF3, hxnA x hx]
  have hF1supp : ∀ x, x ∉ A → F1 x = 0 := fun x hx => by
    simp [hF1, gradDot, pd₁, pd₂, hxnA x hx]
  have hF2supp : ∀ x, x ∉ A → F2 x = 0 := fun x hx => by simp [hF2, hF3supp x hx]
  -- bounds on `A`
  have hrx : ∀ x ∈ A, ε ≤ ‖x - c‖ ∧ ‖x - c‖ ≤ 2 * ε := fun x hx => hx
  have hF1b : ∀ x ∈ A, ‖F1 x‖ ≤ 2 * Mw * Ms * (L / ε) := by
    intro x hx
    have hxb : x ∈ closedBall c (r / 2) := by
      rw [mem_closedBall, dist_eq_norm]; linarith [hx.2]
    have hs1 := hMs x hxb
    have h1 : |fderiv ℝ β x 1| ≤ L / ε := (Complex.abs_re_le_norm (1 : ℂ) |> fun _ =>
      (le_trans (by simpa using (fderiv ℝ β x).le_opNorm 1) (hfβ x)))
    have h2 : |fderiv ℝ β x Complex.I| ≤ L / ε := le_trans (by simpa using (fderiv ℝ β x).le_opNorm Complex.I) (hfβ x)
    have h3 : |fderiv ℝ s x 1| ≤ Ms := le_trans (by simpa using (fderiv ℝ s x).le_opNorm 1) hs1
    have h4 : |fderiv ℝ s x Complex.I| ≤ Ms := le_trans (by simpa using (fderiv ℝ s x).le_opNorm Complex.I) hs1
    rw [Real.norm_eq_abs, hF1]
    simp only [gradDot, pd₁, pd₂, abs_mul]
    have hLε : 0 ≤ L / ε := by positivity
    calc |w x| * |fderiv ℝ β x 1 * fderiv ℝ s x 1 + fderiv ℝ β x Complex.I * fderiv ℝ s x Complex.I|
        ≤ Mw * (|fderiv ℝ β x 1| * |fderiv ℝ s x 1| + |fderiv ℝ β x Complex.I| * |fderiv ℝ s x Complex.I|) := by
          refine mul_le_mul (hMw x) ?_ (abs_nonneg _) hMw0
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ Mw * ((L / ε) * Ms + (L / ε) * Ms) := by
          gcongr
      _ = 2 * Mw * Ms * (L / ε) := by ring
  have hF2b : ∀ x ∈ A, ‖F2 x‖ ≤ Kw * (L / ε) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hrx x hx
    have hxn : 0 < ‖x - c‖ := lt_of_lt_of_le hε0 h1
    have hlip : |w x - w c| ≤ Kw * ‖x - c‖ := by
      have := hw.dist_le_mul x c
      rwa [Real.dist_eq, dist_eq_norm] at this
    have hlin : |fderiv ℝ β x (x - c)| ≤ (L / ε) * ‖x - c‖ :=
      le_trans (by simpa using (fderiv ℝ β x).le_opNorm (x - c))
        (mul_le_mul_of_nonneg_right (hfβ x) (norm_nonneg _))
    rw [Real.norm_eq_abs, hF2, hF3, abs_mul, abs_mul, abs_inv, abs_of_nonneg (by positivity : 0 ≤ ‖x - c‖ ^ 2)]
    calc |w x - w c| * ((‖x - c‖ ^ 2)⁻¹ * |fderiv ℝ β x (x - c)|)
        ≤ (Kw * ‖x - c‖) * ((‖x - c‖ ^ 2)⁻¹ * ((L / ε) * ‖x - c‖)) := by gcongr
      _ = Kw * (L / ε) := by field_simp
  -- integrability
  have hF3b : ∀ x ∈ A, ‖F3 x‖ ≤ L / ε / ‖x - c‖ := by
    intro x hx
    obtain ⟨h1, h2⟩ := hrx x hx
    have hxn : 0 < ‖x - c‖ := lt_of_lt_of_le hε0 h1
    have hlin : |fderiv ℝ β x (x - c)| ≤ (L / ε) * ‖x - c‖ :=
      le_trans (by simpa using (fderiv ℝ β x).le_opNorm (x - c))
        (mul_le_mul_of_nonneg_right (hfβ x) (norm_nonneg _))
    rw [Real.norm_eq_abs, hF3, abs_mul, abs_inv, abs_of_nonneg (by positivity : 0 ≤ ‖x - c‖ ^ 2)]
    calc (‖x - c‖ ^ 2)⁻¹ * |fderiv ℝ β x (x - c)| ≤ (‖x - c‖ ^ 2)⁻¹ * ((L / ε) * ‖x - c‖) := by
          gcongr
      _ = L / ε / ‖x - c‖ := by field_simp
  have hF3b' : ∀ x ∈ A, ‖F3 x‖ ≤ L / ε / ε := fun x hx =>
    (hF3b x hx).trans (div_le_div_of_nonneg_left (by positivity) hε0 (hrx x hx).1)
  have hm1 : Measurable F1 := by
    have : Measurable fun x => gradDot β s x := by
      simp only [gradDot, pd₁, pd₂]
      exact ((measurable_fderiv_apply_const ℝ β 1).mul (measurable_fderiv_apply_const ℝ s 1)).add
        ((measurable_fderiv_apply_const ℝ β Complex.I).mul (measurable_fderiv_apply_const ℝ s Complex.I))
    exact hw.continuous.measurable.mul this
  have hm3 : Measurable F3 := by
    have : Measurable fun x : ℂ => fderiv ℝ β x (x - c) := by
      have h0 : ∀ x : ℂ, fderiv ℝ β x (x - c) = (x - c).re * fderiv ℝ β x 1 + (x - c).im * fderiv ℝ β x Complex.I :=
        fun x => fderiv_apply_eq β x (x - c)
      simp_rw [h0]
      exact ((Complex.measurable_re.comp (measurable_id.sub_const c)).mul (measurable_fderiv_apply_const ℝ β 1)).add
        ((Complex.measurable_im.comp (measurable_id.sub_const c)).mul (measurable_fderiv_apply_const ℝ β Complex.I))
    exact (by fun_prop : Measurable fun x : ℂ => (‖x - c‖ ^ 2)⁻¹).mul this
  have hm2 : Measurable F2 := (hw.continuous.measurable.sub_const _).mul hm3
  have hI1 : Integrable F1 := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := A) ?_ hF1supp
    exact Measure.integrableOn_of_bounded hAfin.ne hm1.aestronglyMeasurable (M := 2 * Mw * Ms * (L / ε))
      ((ae_restrict_iff' hAm).2 (Eventually.of_forall hF1b))
  have hI2 : Integrable F2 := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := A) ?_ hF2supp
    exact Measure.integrableOn_of_bounded hAfin.ne hm2.aestronglyMeasurable (M := Kw * (L / ε))
      ((ae_restrict_iff' hAm).2 (Eventually.of_forall hF2b))
  have hI3 : Integrable F3 := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := A) ?_ hF3supp
    exact Measure.integrableOn_of_bounded hAfin.ne hm3.aestronglyMeasurable (M := L / ε / ε)
      ((ae_restrict_iff' hAm).2 (Eventually.of_forall hF3b'))
  have hF3int : ∫ x, F3 x = -(2 * Real.pi) := integral_inv_sq_fderiv_cutBump hε0
  have hsplit : (∫ x, w x * gradDot β u x) = (∫ x, F1 x) - (∫ x, F2 x) - w c * ∫ x, F3 x := by
    have e1 : ∫ x, (F1 x - F2 x - w c * F3 x) = (∫ x, (F1 x - F2 x)) - ∫ x, w c * F3 x :=
      integral_sub (hI1.sub hI2) (hI3.const_mul _)
    rw [integral_congr_ae (Eventually.of_forall hid), e1, integral_sub hI1 hI2, integral_const_mul]
  have hb1 : |∫ x, F1 x| ≤ 8 * Real.pi * Mw * L * Ms * ε := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF1supp]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) hAfin hF1b
    rw [Real.norm_eq_abs, Measure.real] at this
    refine this.trans ?_
    calc 2 * Mw * Ms * (L / ε) * (volume A).toReal ≤ 2 * Mw * Ms * (L / ε) * (4 * Real.pi * ε ^ 2) := by
          gcongr
      _ = _ := by field_simp; ring
  have hb2 : |∫ x, F2 x| ≤ 4 * Real.pi * Kw * L * ε := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF2supp]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) hAfin hF2b
    rw [Real.norm_eq_abs, Measure.real] at this
    refine this.trans ?_
    calc Kw * (L / ε) * (volume A).toReal ≤ Kw * (L / ε) * (4 * Real.pi * ε ^ 2) := by gcongr
      _ = _ := by field_simp
  have hint_u : Integrable (fun x => w x * gradDot β u x) := by
    have : (fun x => w x * gradDot β u x) = fun x => F1 x - F2 x - w c * F3 x := funext hid
    rw [this]
    exact (hI1.sub hI2).sub (hI3.const_mul _)
  refine ⟨hint_u, ?_⟩
  rw [hsplit, hF3int]
  have : (∫ x, F1 x) - (∫ x, F2 x) - w c * -(2 * Real.pi) - 2 * Real.pi * w c =
      (∫ x, F1 x) - ∫ x, F2 x := by ring
  rw [this]
  calc |(∫ x, F1 x) - ∫ x, F2 x| ≤ |∫ x, F1 x| + |∫ x, F2 x| := abs_sub _ _
    _ ≤ _ := by linarith

end Dual

end SandierSerfaty

end
