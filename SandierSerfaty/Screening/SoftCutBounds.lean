/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.SoftCut
public import SandierSerfaty.Screening.ColumnMass
public import SandierSerfaty.Screening.PinwheelRegions

/-!
# Bounds on the soft-cut source (screening note, Lemmas 4.11(c), 4.12, 4.17)

The screening note, Lemma 4.11(c), Lemma 4.12 (ring estimates) and
Lemma 4.17 (strip estimate), with the grid counts of the screening note replaced by the local count
(`LocalCount`) integrated with Tonelli (the constants of the screening theorem are existential):

* `Hyp.norm_X_le`: on `Ā = {d - 1 ≤ δ ≤ d}`, `|X| ≤ |Φ| + 4n`;
* `Hyp.abs_g_le`: `|g| ≤ 2πm + 36n + 1_Ā |Φ|` (Lemma 4.11(c));
* `Hyp.lintegral_nD_sq_le`: `∫_S n² ≤ 2((9π/4)m)² |S| + (81/32) S_d` (replaces Lemma 4.12(a),(b));
* `Hyp.integral_abs_g_le`: `∫_T |g| ≤ (2πm + 37/2ε)|T| + 18ε(2((9π/4)m)²|T| + (81/32)S_d) + (ε/2)S_d`
  for `T ⊆ Q` (Lemma 4.17's first step, with AM–GM);
* `Hyp.cutHyp`: the hypotheses `Pinwheel.CutHyp` of the column cut (screening note, Lemma 4.18) for `g`, with
  `n_tot = N - #K`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening.Scr

namespace Data

variable {D : Data}

/-- The level sets of the depth are null. -/
theorem volume_dep_eq (s : ℝ) : volume {x | D.dep x = s} = 0 := by
  refine measure_mono_null (fun x hx => ?_) (Pinwheel.volume_junctionLines D.c (D.t / 2 - s))
  simp only [mem_ofPred_eq, dep, sqDepth] at hx
  have hm : max |(x - D.c).re| |(x - D.c).im| = D.t / 2 - s := by linarith
  simp only [Pinwheel.junctionLines, mem_union, mem_ofPred_eq]
  rcases max_choice |(x - D.c).re| |(x - D.c).im| with h | h <;> rw [h] at hm
  · rcases abs_choice (x - D.c).re with h' | h' <;> rw [h'] at hm
    · left; left; left; exact hm
    · left; left; right; linarith
  · rcases abs_choice (x - D.c).im with h' | h' <;> rw [h'] at hm
    · left; right; exact hm
    · right; linarith

theorem measurable_nD : Measurable D.nD := by
  have : D.nD = fun x => π / 16 * D.uSum x := by
    ext x; rw [uSum_eq]; field_simp
  rw [this]; exact measurable_uSum.const_mul _

/-- `|Φ|²` restricted to the ring. -/
@[expose] noncomputable def fR (D : Data) : ℂ → ℝ≥0∞ :=
  D.R.indicator (fun y => ENNReal.ofReal (‖D.Φ y‖ ^ 2))

theorem lintegral_fR : ∫⁻ y, fR D y = ∫⁻ y in D.R, ENNReal.ofReal (‖D.Φ y‖ ^ 2) :=
  lintegral_indicator measurableSet_R _

namespace Hyp

variable (h : D.Hyp)
include h

/-- A kept charge is far from `{δ ≤ d}`: `∇f_{1/4}(· - p) = 0` there. -/
theorem gradient_truncLog_K_eq_zero {p x : ℂ} (hp : p ∈ D.K) (hx : D.dep x ≤ D.d + 5) :
    gradient (truncLog (1 / 4)) (x - p) = 0 := by
  refine gradient_truncLog_of_gt (by norm_num) ?_
  have h1 := dep_le_add (D := D) p x
  have h2 := (h.mem_K.1 hp).2
  rw [norm_sub_rev]; linarith

/-- On `{δ ≤ d + 5}`, `X = Φ - ∑_{D*} W_q`. -/
theorem X_eq {x : ℂ} (hx : D.dep x ≤ D.d + 5) :
    D.X x = D.Φ x - ∑ q ∈ D.Ds, radialW (1 / 4) (x - q) := by
  rw [X, Finset.sum_eq_zero fun p hp => h.gradient_truncLog_K_eq_zero hp hx, add_zero]

theorem norm_X_le {x : ℂ} (hx : D.dep x ≤ D.d + 5) : ‖D.X x‖ ≤ ‖D.Φ x‖ + 4 * D.nD x := by
  rw [h.X_eq hx]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_radialW_le x))

/-- **Lemma 4.11(c)**: `|g| ≤ 2πm + 36n + 1_Ā |Φ|`. -/
theorem abs_g_le (x : ℂ) :
    |D.g x| ≤ 2 * π * D.m + 36 * D.nD x + D.Abar.indicator (fun y => ‖D.Φ y‖) x := by
  have hm := h.m_pos
  have hpi := Real.pi_pos
  have h0 := psi_nonneg (D := D) x
  have h1 := psi_le_one (D := D) x
  have hn := nD_nonneg (D := D) x
  have hu : D.uSum x = 16 / π * D.nD x := uSum_eq x
  have hinner : |inner ℝ (D.X x) (gradient D.psi x)| ≤
      4 * D.nD x + D.Abar.indicator (fun y => ‖D.Φ y‖) x := by
    by_cases hx : x ∈ D.Abar
    · rw [indicator_of_mem hx]
      calc |inner ℝ (D.X x) (gradient D.psi x)| ≤ ‖D.X x‖ * ‖gradient D.psi x‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖D.X x‖ * 1 := by gcongr; exact norm_gradient_psi_le x
        _ ≤ ‖D.Φ x‖ + 4 * D.nD x := by rw [mul_one]; exact h.norm_X_le (by linarith [hx.2])
        _ = _ := by ring
    · rw [indicator_of_notMem hx, gradient_psi_of_notMem hx, inner_zero_right, abs_zero]
      linarith [nD_nonneg (D := D) x]
  have hI := D.Abar.indicator_nonneg (fun y _ => norm_nonneg (D.Φ y)) x
  have hpsiu : D.psi x * D.uSum x ≤ 16 / π * D.nD x := by
    have : 0 ≤ 16 / π * D.nD x := mul_nonneg (by positivity) hn
    rw [hu]; nlinarith
  have hpsiu0 : 0 ≤ D.psi x * D.uSum x := mul_nonneg h0 (uSum_nonneg x)
  have h16 : 2 * π * (16 / π * D.nD x) = 32 * D.nD x := by field_simp; ring
  rw [g]
  calc |2 * π * D.m * (1 - D.psi x) + 2 * π * D.psi x * D.uSum x -
        inner ℝ (D.X x) (gradient D.psi x)|
      ≤ |2 * π * D.m * (1 - D.psi x)| + |2 * π * D.psi x * D.uSum x| +
          |inner ℝ (D.X x) (gradient D.psi x)| := abs_sub_le_of_le_of_le _ _ _
    _ ≤ 2 * π * D.m + 32 * D.nD x + (4 * D.nD x + D.Abar.indicator (fun y => ‖D.Φ y‖) x) := by
        gcongr
        · have hp : 0 ≤ 2 * π * D.m := by positivity
          rw [abs_of_nonneg (mul_nonneg hp (by linarith))]
          nlinarith [mul_nonneg hp h0]
        · rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) h0) (uSum_nonneg x)),
            mul_assoc, ← h16]
          exact mul_le_mul_of_nonneg_left hpsiu (by positivity)
    _ = _ := by ring
where
  abs_sub_le_of_le_of_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
    calc |a + b - c| ≤ |a + b| + |c| := abs_sub _ _
      _ ≤ |a| + |b| + |c| := by gcongr; exact abs_add_le _ _

/-- Charges counted at `x` force `x` into the band `{d - 3/2 < δ < d + 25/4}`. -/
theorem dep_mem_of_nD_ne_zero {x : ℂ} (hx : D.nD x ≠ 0) :
    D.d - 3 / 2 < D.dep x ∧ D.dep x < D.d + 25 / 4 := by
  rw [nD, Nat.cast_ne_zero, Finset.card_ne_zero] at hx
  obtain ⟨q, hq⟩ := hx
  rw [Finset.mem_filter] at hq
  have hqD := (h.mem_Ds.1 hq.1).2
  have h1 := dep_le_add (D := D) x q
  have h2 := dep_le_add (D := D) q x
  rw [norm_sub_rev] at h1
  constructor <;> linarith [hq.2]

theorem closedBall_subset_R {x : ℂ} (hx : D.nD x ≠ 0) : closedBall x (3 / 2) ⊆ D.R := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  have hb := h.dep_mem_of_nD_ne_zero hx
  have h1 := dep_le_add (D := D) x y
  have h2 := dep_le_add (D := D) y x
  rw [norm_sub_rev] at h1
  rw [mem_R_iff]; constructor <;> linarith

theorem aemeasurable_fR : AEMeasurable (fR D) := by
  rw [fR, aemeasurable_indicator_iff measurableSet_R]
  exact (ENNReal.measurable_ofReal.comp_aemeasurable
    (h.integrableOn_Φ_R.aestronglyMeasurable.norm.aemeasurable.pow_const 2))

/-- The pointwise count bound: `n(x)² ≤ 2((9π/4)m)² + (9/8π) ∫_{B̄(x, 3/2)} 1_R |Φ|²`. -/
theorem ofReal_nD_sq_le (x : ℂ) :
    ENNReal.ofReal (D.nD x ^ 2) ≤ ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) +
      ENNReal.ofReal (9 / (8 * π)) * ∫⁻ y in closedBall x (3 / 2), fR D y := by
  by_cases hx : D.nD x = 0
  · rw [hx]; simp
  have hB := h.closedBall_subset_R hx
  have hint : ∫⁻ y in closedBall x (3 / 2), fR D y =
      ∫⁻ y in closedBall x (3 / 2), ENNReal.ofReal (‖D.Φ y‖ ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_closedBall fun y hy => ?_
    rw [fR, indicator_of_mem (hB hy)]
  have hJ : ∫⁻ y in closedBall x (3 / 2), ENNReal.ofReal (‖D.Φ y‖ ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((lintegral_mono_set hB).trans h.hSd)
  rw [hint]
  have := ofReal_card_sq_le isOpen_U h.m_pos.le h.hC h.hE (hB.trans h.R_subset_U)
    (P := D.Ds.filter fun q => ‖q - x‖ < 1 / 4)
    (fun q hq => h.Ds_subset_C (Finset.mem_filter.1 hq).1) (fun q hq => (Finset.mem_filter.1 hq).2)
    hJ
  exact this

/-- **The count bound** (replaces Lemma 4.12(a),(b)): `∫_S n² ≤ 2((9π/4)m)² |S| + (81/32) S_d`. -/
theorem lintegral_nD_sq_le (S : Set ℂ) :
    ∫⁻ x in S, ENNReal.ofReal (D.nD x ^ 2) ≤
      ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) * volume S + ENNReal.ofReal (81 / 32 * D.Sd) := by
  have hpi := Real.pi_pos
  calc ∫⁻ x in S, ENNReal.ofReal (D.nD x ^ 2)
      ≤ ∫⁻ x in S, (ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) +
          ENNReal.ofReal (9 / (8 * π)) * ∫⁻ y in closedBall x (3 / 2), fR D y) :=
        lintegral_mono fun x => h.ofReal_nD_sq_le x
    _ = ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) * volume S +
          ENNReal.ofReal (9 / (8 * π)) * ∫⁻ x in S, ∫⁻ y in closedBall x (3 / 2), fR D y := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, mul_comm,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) * volume S +
          ENNReal.ofReal (9 / (8 * π)) * (volume (closedBall (0 : ℂ) (3 / 2)) * ∫⁻ y, fR D y) := by
        gcongr
        exact lintegral_setLIntegral_closedBall_le h.aemeasurable_fR S _
    _ ≤ ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) * volume S +
          ENNReal.ofReal (9 / (8 * π)) * (ENNReal.ofReal (9 * π / 4) * ENNReal.ofReal D.Sd) := by
        gcongr
        · rw [← ENNReal.ofReal_toReal (measure_closedBall_lt_top (x := (0 : ℂ)) (r := 3 / 2)).ne]
          rw [← measureReal_def, volume_closedBall_three_halves]
        · rw [lintegral_fR]; exact h.hSd
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
        ring

/-- `∫_S 1_Ā |Φ|² ≤ S_d`. -/
theorem lintegral_Abar_le (S : Set ℂ) :
    ∫⁻ x in S, ENNReal.ofReal ((D.Abar.indicator (fun y => ‖D.Φ y‖) x) ^ 2) ≤
      ENNReal.ofReal D.Sd := by
  calc ∫⁻ x in S, ENNReal.ofReal ((D.Abar.indicator (fun y => ‖D.Φ y‖) x) ^ 2)
      ≤ ∫⁻ x, D.Abar.indicator (fun y => ENNReal.ofReal (‖D.Φ y‖ ^ 2)) x := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun x => ?_)
        by_cases hx : x ∈ D.Abar
        · rw [indicator_of_mem hx, indicator_of_mem hx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
    _ = ∫⁻ x in D.Abar, ENNReal.ofReal (‖D.Φ x‖ ^ 2) := lintegral_indicator measurableSet_Abar _
    _ ≤ ∫⁻ x in D.R, ENNReal.ofReal (‖D.Φ x‖ ^ 2) := lintegral_mono_set Abar_subset_R
    _ ≤ _ := h.hSd

/-- **Strip estimate, first step** (Lemma 4.17 with AM–GM, parameter `ε > 0`): for `T ⊆ Q` of
finite measure,
`∫_T |g| ≤ (2πm + 37/2ε)|T| + 18ε(2((9π/4)m)²|T| + (81/32)S_d) + (ε/2)S_d`. -/
theorem integral_abs_g_le {T : Set ℂ} (hTQ : T ⊆ D.Q) (hTf : volume T ≠ ⊤) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x in T, |D.g x| ≤ (2 * π * D.m + 37 / (2 * ε)) * volume.real T +
      18 * ε * (2 * (9 * π / 4 * D.m) ^ 2 * volume.real T + 81 / 32 * D.Sd) + ε / 2 * D.Sd := by
  have hm := h.m_pos
  have hpi := Real.pi_pos
  have hS := h.Sd_nonneg
  set I : ℂ → ℝ := fun x => D.Abar.indicator (fun y => ‖D.Φ y‖) x
  have hI0 : ∀ x, 0 ≤ I x := fun x => D.Abar.indicator_nonneg (fun y _ => norm_nonneg (D.Φ y)) x
  -- AM–GM: `a ≤ (ε/2) a² + 1/(2ε)`
  have amgm : ∀ a : ℝ, a ≤ ε / 2 * a ^ 2 + 1 / (2 * ε) := fun a => by
    have key : ε / 2 * a ^ 2 + 1 / (2 * ε) - a = (ε * a - 1) ^ 2 / (2 * ε) := by
      field_simp; ring
    have : 0 ≤ (ε * a - 1) ^ 2 / (2 * ε) := by positivity
    linarith
  have hpt : ∀ x, |D.g x| ≤ (2 * π * D.m + 37 / (2 * ε)) + 18 * ε * D.nD x ^ 2 + ε / 2 * I x ^ 2 := by
    intro x
    have h1 := h.abs_g_le x
    have h2 := amgm (D.nD x)
    have h3 := amgm (I x)
    have : 37 / (2 * ε) = 36 * (1 / (2 * ε)) + 1 / (2 * ε) := by ring
    rw [this]
    nlinarith
  have hgT : IntegrableOn D.g T := h.integrableOn_g_Q.mono_set hTQ
  have hlhs : ∫ x in T, |D.g x| = (∫⁻ x in T, ENNReal.ofReal |D.g x|).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _)
      hgT.abs.aestronglyMeasurable]
  have hlint : ∫⁻ x in T, ENNReal.ofReal |D.g x| ≤
      ENNReal.ofReal ((2 * π * D.m + 37 / (2 * ε)) * volume.real T +
        18 * ε * (2 * (9 * π / 4 * D.m) ^ 2 * volume.real T + 81 / 32 * D.Sd) + ε / 2 * D.Sd) := by
    calc ∫⁻ x in T, ENNReal.ofReal |D.g x|
        ≤ ∫⁻ x in T, (ENNReal.ofReal (2 * π * D.m + 37 / (2 * ε)) +
            ENNReal.ofReal (18 * ε) * ENNReal.ofReal (D.nD x ^ 2) +
              ENNReal.ofReal (ε / 2) * ENNReal.ofReal (I x ^ 2)) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt x)
      _ = ENNReal.ofReal (2 * π * D.m + 37 / (2 * ε)) * volume T +
            ENNReal.ofReal (18 * ε) * (∫⁻ x in T, ENNReal.ofReal (D.nD x ^ 2)) +
              ENNReal.ofReal (ε / 2) * ∫⁻ x in T, ENNReal.ofReal (I x ^ 2) := by
          set A := ENNReal.ofReal (2 * π * D.m + 37 / (2 * ε))
          set B := ENNReal.ofReal (18 * ε)
          set C := ENNReal.ofReal (ε / 2)
          have hmeas : Measurable fun x => A + B * ENNReal.ofReal (D.nD x ^ 2) :=
            measurable_const.add ((measurable_nD.pow_const 2).ennreal_ofReal.const_mul _)
          have e1 : ∫⁻ x in T, (A + B * ENNReal.ofReal (D.nD x ^ 2) + C * ENNReal.ofReal (I x ^ 2)) =
              (∫⁻ x in T, (A + B * ENNReal.ofReal (D.nD x ^ 2))) +
                ∫⁻ x in T, C * ENNReal.ofReal (I x ^ 2) := by
            rw [lintegral_add_left hmeas]
          have e2 : ∫⁻ x in T, (A + B * ENNReal.ofReal (D.nD x ^ 2)) =
              A * volume T + B * (∫⁻ x in T, ENNReal.ofReal (D.nD x ^ 2)) := by
            rw [lintegral_add_left measurable_const, setLIntegral_const,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [e1, e2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (2 * π * D.m + 37 / (2 * ε)) * ENNReal.ofReal (volume.real T) +
            ENNReal.ofReal (18 * ε) * (ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) *
              ENNReal.ofReal (volume.real T) + ENNReal.ofReal (81 / 32 * D.Sd)) +
              ENNReal.ofReal (ε / 2) * ENNReal.ofReal D.Sd := by
          rw [measureReal_def, ENNReal.ofReal_toReal hTf]
          gcongr
          · exact h.lintegral_nD_sq_le T
          · exact h.lintegral_Abar_le T
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hlhs]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hlint)

/-! ### The hypotheses of the column cut -/

theorem offset_pos : 0 < Pinwheel.offset D.t D.d := by
  rw [Pinwheel.offset]; linarith [h.t_ge, h.d_le, h.ℓt_ge]

theorem side_ge : 3 * D.ℓ ≤ Pinwheel.side D.t D.d := by
  rw [Pinwheel.side]; linarith [h.t_ge, h.d_le, h.ℓt_ge, h.ℓ_le]

omit h in
theorem frameSet_subset_Q : Pinwheel.frameSet D.c D.t D.d ⊆ D.Q := fun _ hx => mem_Q_iff.2 hx.1

/-- `g = 0` on `{δ > d + 8}`. -/
theorem g_eq_zero_of_lt {x : ℂ} (hx : D.d + 8 < D.dep x) : D.g x = 0 := by
  have hn : D.nD x = 0 := by
    by_contra hne
    linarith [(h.dep_mem_of_nD_ne_zero hne).2]
  rw [g, psi_eq_one (by linarith), gradient_psi_of_lt (by linarith), inner_zero_right, uSum_eq, hn]
  ring

omit h in
/-- `g = 2πm` on `{δ < d - 1}`. -/
theorem g_eq_of_lt {x : ℂ} (hx : D.dep x < D.d - 1) : D.g x = 2 * π * D.m := by
  rw [g, psi_eq_zero hx.le, gradient_psi_of_lt' hx, inner_zero_right]
  ring

/-- **The column-cut hypotheses** for the soft-cut source, `n_tot = N - #K`. -/
theorem cutHyp : Pinwheel.CutHyp D.c D.t D.d D.m D.ℓ D.g ((D.N : ℤ) - D.K.card) where
  m_pos := h.m_pos
  K2 := h.K2
  K4 := h.K4
  d_ge := h.d_ge_ℓ
  offset_pos := h.offset_pos
  side_ge := h.side_ge
  integrableOn := h.integrableOn_g_Q.mono_set frameSet_subset_Q
  low := by
    intro j
    have hnull := volume_dep_eq (D := D) (D.d - 1)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxb
    have hd := Pinwheel.sqDepth_mem_of_mem_bottom h.offset_pos.le hxb
    refine g_eq_of_lt (lt_of_le_of_ne hd.2 fun heq => hx ?_)
    exact heq
  strip := by
    intro j x w hx hxw hw
    set T := (Pinwheel.rect D.c D.t D.d j).box (Icc x (x + w)) (Icc (D.d - 1) (D.d + 8))
    have hTR : T ⊆ (Pinwheel.rect D.c D.t D.d j).carrier :=
      Rect.box_mono (Icc_subset_Icc hx hxw)
        (Icc_subset_Icc (by linarith [h.d_pos]) (by simp only [Pinwheel.rect_height]; rfl))
    have hRF : (Pinwheel.rect D.c D.t D.d j).carrier ⊆ Pinwheel.frameSet D.c D.t D.d := by
      rw [← Pinwheel.iUnion_rect h.offset_pos.le]
      exact subset_iUnion (fun j => (Pinwheel.rect D.c D.t D.d j).carrier) j
    have hTQ : T ⊆ D.Q := hTR.trans (hRF.trans frameSet_subset_Q)
    have hTv : volume.real T = 9 * w := by
      rw [measureReal_def, Rect.volume_box_Icc, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by linarith [hw.1, h.K4]), ENNReal.toReal_ofReal (by norm_num)]
      ring
    have hTf : volume T ≠ ⊤ := by
      rw [Rect.volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hε : 0 < 500 / (D.m * D.ℓ) := by have := h.m_pos; have := h.ℓ_pos; positivity
    have hb := h.integral_abs_g_le hTQ hTf hε
    rw [hTv] at hb
    have hnum := h.strip_num w hw
    rw [stripBound] at hnum
    linarith
  total := by
    have hQ := h.setIntegral_g
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Q frameSet_subset_Q
      fun x hx => h.g_eq_zero_of_lt ?_] at hQ
    · rw [hQ]; push_cast; ring
    · have h1 := hx.2
      simp only [Pinwheel.frameSet, mem_ofPred_eq, not_and_or, not_le] at h1
      rcases h1 with h1 | h1
      · exact absurd (mem_Q_iff.1 hx.1) (not_le.2 h1)
      · exact h1

end Hyp

end Data

end SandierSerfaty.Screening.Scr

end
