/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.SquareCell
public import SandierSerfaty.Screening.Averaging

/-!
# The depth in a square and the good cut (screening note, §1.1 and Lemma 4.7)

From the screening note: for the square `Q = sq c t` the (signed) **depth** is
`δ(x) = t/2 - |x - c|_∞` (`SandierSerfaty.Screening.sqDepth`). It is `1`-Lipschitz for the Euclidean
norm and its super-level sets are the concentric squares (screening note (1.1), `eq:depth-sets`):

* `mem_sq_iff_le_sqDepth`: `sq c (t - 2s) = {δ ≥ s}`;
* `mem_interior_sq_iff_lt_sqDepth`: `int sq c (t - 2s) = {δ > s}`;
* `abs_sqDepth_sub_le`, `lipschitzWith_sqDepth`, `continuous_sqDepth`.

**Good cut** (screening note, Lemma 4.7, `lem:goodcut`), `exists_goodCut`: for `ℓt > 22` and a measurable
`h ≥ 0` with `∫_{ℓt/2 ≤ δ < 2ℓt} h ≤ S` there is `d ∈ [ℓt, 3ℓt/2]` such that the ring
`R_d = {d - 5 ≤ δ ≤ d + 11}` lies in `{ℓt/2 ≤ δ < 2ℓt}` and `∫_{R_d} h ≤ 32 S / ℓt` (Tonelli and the
averaging choice, Lemma 4.6). The screening note applies it to `h = |Φ|²`, `Φ = E_{1/4}`
(`exists_goodCut_field`).
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

public section

namespace SandierSerfaty.Screening

/-- The **depth** `δ(x) = t/2 - |x - c|_∞` in the square `sq c t` (screening note, §1.1). -/
@[expose] noncomputable def sqDepth (c : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  t / 2 - max |(x - c).re| |(x - c).im|

variable {c x y : ℂ} {t s : ℝ}

/-- `sq c (t - 2s) = {δ ≥ s}` (screening note (1.1)). -/
theorem mem_sq_iff_le_sqDepth : x ∈ sq c (t - 2 * s) ↔ s ≤ sqDepth c t x := by
  rw [mem_sq_iff, sqDepth, le_sub_iff_add_le, ← le_sub_iff_add_le', max_le_iff, abs_le, abs_le]
  simp only [Complex.sub_re, Complex.sub_im, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- `Q = sq c t = {δ ≥ 0}`. -/
theorem mem_sq_iff_sqDepth_nonneg : x ∈ sq c t ↔ 0 ≤ sqDepth c t x := by
  rw [← mem_sq_iff_le_sqDepth, mul_zero, sub_zero]

/-- `int sq c (t - 2s) = {δ > s}` (screening note (1.1)). -/
theorem mem_interior_sq_iff_lt_sqDepth : x ∈ interior (sq c (t - 2 * s)) ↔ s < sqDepth c t x := by
  rw [mem_interior_sq_iff, sqDepth, lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', max_lt_iff, abs_lt,
    abs_lt]
  simp only [Complex.sub_re, Complex.sub_im, mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The depth is `1`-Lipschitz for the Euclidean norm. -/
theorem abs_sqDepth_sub_le (c : ℂ) (t : ℝ) (x y : ℂ) :
    |sqDepth c t x - sqDepth c t y| ≤ ‖x - y‖ := by
  have hre : |(x - c).re - (y - c).re| ≤ ‖x - y‖ := by
    rw [← Complex.sub_re, sub_sub_sub_cancel_right]; exact Complex.abs_re_le_norm _
  have him : |(x - c).im - (y - c).im| ≤ ‖x - y‖ := by
    rw [← Complex.sub_im, sub_sub_sub_cancel_right]; exact Complex.abs_im_le_norm _
  have key : ∀ a b a' b' : ℝ, |a - a'| ≤ ‖x - y‖ → |b - b'| ≤ ‖x - y‖ →
      max |a| |b| - max |a'| |b'| ≤ ‖x - y‖ := by
    intro a b a' b' ha hb
    have h1 : |a| ≤ |a'| + ‖x - y‖ := by
      have := abs_sub_abs_le_abs_sub a a'; linarith
    have h2 : |b| ≤ |b'| + ‖x - y‖ := by
      have := abs_sub_abs_le_abs_sub b b'; linarith
    have := max_le (h1.trans (add_le_add_left (le_max_left |a'| |b'|) _))
      (h2.trans (add_le_add_left (le_max_right |a'| |b'|) _))
    linarith
  rw [sqDepth, sqDepth, abs_le]
  constructor
  · have := key _ _ _ _ hre him; linarith
  · have := key (y - c).re (y - c).im (x - c).re (x - c).im (by rwa [abs_sub_comm])
      (by rwa [abs_sub_comm])
    linarith

theorem lipschitzWith_sqDepth (c : ℂ) (t : ℝ) : LipschitzWith 1 (sqDepth c t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact abs_sqDepth_sub_le c t x y

theorem continuous_sqDepth (c : ℂ) (t : ℝ) : Continuous (sqDepth c t) :=
  (lipschitzWith_sqDepth c t).continuous

theorem measurableSet_sqDepth_Icc (c : ℂ) (t a b : ℝ) :
    MeasurableSet {x | a ≤ sqDepth c t x ∧ sqDepth c t x ≤ b} :=
  (isClosed_le continuous_const (continuous_sqDepth c t)).measurableSet.inter
    (isClosed_le (continuous_sqDepth c t) continuous_const).measurableSet

theorem measurableSet_sqDepth_Ico (c : ℂ) (t a b : ℝ) :
    MeasurableSet {x | a ≤ sqDepth c t x ∧ sqDepth c t x < b} :=
  (isClosed_le continuous_const (continuous_sqDepth c t)).measurableSet.inter
    (isOpen_lt (continuous_sqDepth c t) continuous_const).measurableSet

/-- The layer `{a ≤ δ < b}` is the difference of two concentric squares,
`sq c (t - 2a) \ sq c (t - 2b)` (the form of the hypothesis (H6) of the screening note Thm 4.1). -/
theorem sq_diff_sq_eq (c : ℂ) (t a b : ℝ) :
    sq c (t - 2 * a) \ sq c (t - 2 * b) = {x | a ≤ sqDepth c t x ∧ sqDepth c t x < b} := by
  ext x
  simp only [Set.mem_sdiff, mem_sq_iff_le_sqDepth, not_le, mem_ofPred_eq]

/-! ### The good cut (screening note, Lemma 4.7) -/

/-- The ring `R_d = {d - 5 ≤ δ ≤ d + 11}` of the good cut. -/
@[expose] def goodRing (c : ℂ) (t d : ℝ) : Set ℂ :=
  {x | d - 5 ≤ sqDepth c t x ∧ sqDepth c t x ≤ d + 11}

theorem measurableSet_goodRing (c : ℂ) (t d : ℝ) : MeasurableSet (goodRing c t d) :=
  measurableSet_sqDepth_Icc c t _ _

/-- For `ℓt > 22` and `d ∈ [ℓt, 3ℓt/2]`: `R_d ⊆ {ℓt/2 ≤ δ < 2ℓt}`. -/
theorem goodRing_subset {ℓt d : ℝ} (hℓ : 22 < ℓt) (hd : d ∈ Icc ℓt (3 / 2 * ℓt)) :
    goodRing c t d ⊆ {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt} := by
  rintro x ⟨h1, h2⟩
  exact ⟨by linarith [hd.1], by linarith [hd.2]⟩

/-- The set of `d ∈ [ℓt, 3ℓt/2]` with `x ∈ R_d` has length at most `16`, and is empty unless
`x ∈ {ℓt/2 ≤ δ < 2ℓt}`. -/
theorem volume_cut_le {ℓt : ℝ} (hℓ : 22 < ℓt) (x : ℂ) :
    volume {d | d ∈ Icc ℓt (3 / 2 * ℓt) ∧ x ∈ goodRing c t d} ≤
      {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt}.indicator (fun _ => (16 : ℝ≥0∞)) x := by
  set δ := sqDepth c t x
  have hsub : {d | d ∈ Icc ℓt (3 / 2 * ℓt) ∧ x ∈ goodRing c t d} ⊆ Icc (δ - 11) (δ + 5) := by
    rintro d ⟨-, h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  by_cases hx : x ∈ {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt}
  · rw [indicator_of_mem hx]
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Icc]
    norm_num
  · rw [indicator_of_notMem hx, nonpos_iff_eq_zero, measure_eq_zero_iff_ae_notMem]
    refine Eventually.of_forall fun d hd => hx ?_
    exact goodRing_subset hℓ hd.1 hd.2

/-- **Good cut** (screening note, Lemma 4.7), for a measurable density `h ≥ 0`: if
`∫_{ℓt/2 ≤ δ < 2ℓt} h ≤ S` and `ℓt > 22`, there is `d ∈ [ℓt, 3ℓt/2]` with
`R_d ⊆ {ℓt/2 ≤ δ < 2ℓt}` and `∫_{R_d} h ≤ 32 S / ℓt`. -/
theorem exists_goodCut {ℓt : ℝ} (hℓ : 22 < ℓt) {h : ℂ → ℝ≥0∞} (hh : AEMeasurable h) {S : ℝ≥0∞}
    (hS : ∫⁻ x in {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt}, h x ≤ S) :
    ∃ d ∈ Icc ℓt (3 / 2 * ℓt),
      goodRing c t d ⊆ {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt} ∧
        ∫⁻ x in goodRing c t d, h x ≤ 32 * S / ENNReal.ofReal ℓt := by
  set h' := hh.mk h
  have hm : Measurable h' := hh.measurable_mk
  have hring : ∀ d, ∫⁻ x in goodRing c t d, h x = ∫⁻ x in goodRing c t d, h' x := fun d =>
    lintegral_congr_ae (ae_restrict_of_ae hh.ae_eq_mk)
  set Lay := {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt}
  have hLay : MeasurableSet Lay := measurableSet_sqDepth_Ico c t _ _
  -- the joint indicator is measurable
  set P : Set (ℝ × ℂ) := {p : ℝ × ℂ | p.1 - 5 ≤ sqDepth c t p.2 ∧ sqDepth c t p.2 ≤ p.1 + 11}
  have hP : MeasurableSet P := by
    have hc := (continuous_sqDepth c t).comp (continuous_snd (X := ℝ) (Y := ℂ))
    exact (isClosed_le (continuous_fst.sub continuous_const) hc).measurableSet.inter
      (isClosed_le hc (continuous_fst.add continuous_const)).measurableSet
  set F : ℝ → ℂ → ℝ≥0∞ := fun d x => P.indicator (fun p => h' p.2) (d, x)
  have hF : Measurable (Function.uncurry F) := (hm.comp measurable_snd).indicator hP
  have hFd : ∀ d, ∫⁻ x, F d x = ∫⁻ x in goodRing c t d, h' x := by
    intro d
    rw [← lintegral_indicator (measurableSet_goodRing c t d)]
    rfl
  -- Tonelli
  set I := Icc ℓt (3 / 2 * ℓt)
  have hdset : ∀ x : ℂ, MeasurableSet {d : ℝ | x ∈ goodRing c t d} := fun x =>
    (isClosed_le (continuous_id.sub continuous_const) continuous_const).measurableSet.inter
      (isClosed_le continuous_const (continuous_id.add continuous_const)).measurableSet
  have htot : ∫⁻ d in I, ∫⁻ x in goodRing c t d, h' x ≤ 16 * S := by
    calc ∫⁻ d in I, ∫⁻ x in goodRing c t d, h' x = ∫⁻ d in I, ∫⁻ x, F d x := by
          simp_rw [hFd]
      _ = ∫⁻ x, ∫⁻ d in I, F d x := lintegral_lintegral_swap hF.aemeasurable
      _ = ∫⁻ x, h' x * volume {d | d ∈ I ∧ x ∈ goodRing c t d} := by
            refine lintegral_congr fun x => ?_
            have : (fun d => F d x) = {d | x ∈ goodRing c t d}.indicator (fun _ => h' x) := by
              ext d; rfl
            rw [this, lintegral_indicator_const (hdset x), Measure.restrict_apply (hdset x),
              Set.inter_comm]
            rfl
      _ ≤ ∫⁻ x, Lay.indicator (fun x => 16 * h' x) x := by
            refine lintegral_mono fun x => ?_
            have := volume_cut_le (c := c) (t := t) hℓ x
            by_cases hx : x ∈ Lay
            · rw [indicator_of_mem hx, mul_comm]
              rw [indicator_of_mem hx] at this
              gcongr
            · rw [indicator_of_notMem hx] at this ⊢
              rw [nonpos_iff_eq_zero.1 this, mul_zero]
        _ = 16 * ∫⁻ x in Lay, h' x := by
            rw [lintegral_indicator hLay, lintegral_const_mul _ hm]
        _ ≤ 16 * S := by
            gcongr
            rw [← lintegral_congr_ae (ae_restrict_of_ae hh.ae_eq_mk)]
            exact hS
  have hmeas : AEMeasurable (fun d => ∫⁻ x in goodRing c t d, h' x)
      (volume.restrict (Icc ℓt (3 / 2 * ℓt))) := by
    simp_rw [← hFd]
    exact hF.lintegral_prod_right'.aemeasurable
  have hlt : ℓt < 3 / 2 * ℓt := by linarith
  obtain ⟨d, hd, hdle⟩ := exists_le_of_lintegral_le hlt hmeas htot
  refine ⟨d, hd, goodRing_subset hℓ hd, ?_⟩
  rw [hring]
  refine hdle.trans (le_of_eq ?_)
  have hhalf : ENNReal.ofReal (3 / 2 * ℓt - ℓt) = ENNReal.ofReal ℓt / 2 := by
    rw [show 3 / 2 * ℓt - ℓt = ℓt / 2 by ring, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [hhalf, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl (by simp)), inv_inv]
  rw [show (32 : ℝ≥0∞) = 2 * 16 by norm_num]
  ring

/-- **Good cut** (screening note, Lemma 4.7) for `h = |Φ|²`: if `∫_{ℓt/2 ≤ δ < 2ℓt} |Φ|² ≤ S`, there is
`d ∈ [ℓt, 3ℓt/2]` with `R_d ⊆ {ℓt/2 ≤ δ < 2ℓt}` and `S_d = ∫_{R_d} |Φ|² ≤ 32 S / ℓt`. -/
theorem exists_goodCut_field {ℓt : ℝ} (hℓ : 22 < ℓt) {Φ : ℂ → ℂ} (hΦ : AEStronglyMeasurable Φ)
    {S : ℝ≥0∞}
    (hS : ∫⁻ x in {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt},
      ENNReal.ofReal (‖Φ x‖ ^ 2) ≤ S) :
    ∃ d ∈ Icc ℓt (3 / 2 * ℓt),
      goodRing c t d ⊆ {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt} ∧
        ∫⁻ x in goodRing c t d, ENNReal.ofReal (‖Φ x‖ ^ 2) ≤ 32 * S / ENNReal.ofReal ℓt :=
  exists_goodCut hℓ (ENNReal.measurable_ofReal.comp_aemeasurable
    ((hΦ.norm.aemeasurable).pow_const 2)) hS

end SandierSerfaty.Screening

end
