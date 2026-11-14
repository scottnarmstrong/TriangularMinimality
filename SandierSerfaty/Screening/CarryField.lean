/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ColumnMass
public import SandierSerfaty.Screening.FieldGluing

/-!
# The carry fields (screening note, Lemma 4.20)

The screening note, Lemma 4.20 (`lem:carry`), with a corrected condition for the
disjointness of the carry cells (`Pinwheel.disjoint_carryRect`).

For the carry cell `H^c_j = A_j ∪ A'_j` (`Pinwheel.carryRect`, a `w' × 2` rectangle with its `s`-axis
along the common segment), the source `f^c_j = κ (1_{A_j} - 1_{A'_j})`, `κ = 2πθ/w'`
(`Pinwheel.carrySrc`), and the field `V^c_j = T2_{H^c_j}[f^c_j]` (`Pinwheel.carryField`):

* `line_carrySrc`: `F₁ ≡ 0` (every segment across the common side meets `A_j` and `A'_j` in unit
  lengths with opposite values), hence `A ≡ 0` and `B(s, r) = ∫₀ʳ f^c` (Lemma 4.4(c));
* `abs_compB_carry_le`: `|B(s, r)| ≤ κ min(r, 2 - r)` (the tent profile);
* `integral_inner_carryField`: `∫ ⟪V^c_j, ∇φ⟫ = -∫ f^c_j φ` for every Lipschitz `φ`;
  `isFieldPiece_carryField`: `V^c_j` is a field piece with no charges and source `f^c_j`;
* `lintegral_norm_sq_carryField_le`: `∫ |V^c_j|² ≤ (2/3) κ² w' = 8π²θ²/(3w')`, and
  `lintegral_norm_sq_carryField_le'`: `≤ 8π²/(3ℓc)` for `θ ∈ [0, 1)`, `w' ≥ ℓc`.

The location `H^c_j ⊆ O_- ∩ {δ ≤ 3ℓc}` is `CutHyp.sqDepth_mem_of_mem_carryRect`.
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

public section

namespace SandierSerfaty.Screening

/-- `∫ |T2_H[f]|² = ∫_{[0,a]×[0,b]} (A² + B²)` (change of variables through the chart). -/
theorem lintegral_norm_sq_t2Field_eq (H : Rect) (f : ℂ → ℝ) :
    ∫⁻ x, ENNReal.ofReal (‖t2Field H f x‖ ^ 2) =
      ∫⁻ p in Icc 0 H.width ×ˢ Icc 0 H.height,
        ENNReal.ofReal (T2.compA H.height (H.src f) p.1 ^ 2 +
          T2.compB H.height (H.src f) p.1 p.2 ^ 2) := by
  rw [← H.measurePreserving_chart.lintegral_comp_emb H.measurableEmbedding_chart]
  simp only [H.t2Field_chart_eq_stdField, LinearIsometryEquiv.norm_map]
  have hind : (fun w => ENNReal.ofReal (‖T2.stdField H.width H.height (H.src f) w‖ ^ 2)) =
      (Icc 0 H.width ×ℂ Icc 0 H.height).indicator
        fun w => ENNReal.ofReal (‖T2.vec H.height (H.src f) (w.re, w.im)‖ ^ 2) := by
    ext w
    by_cases hw : w ∈ Icc 0 H.width ×ℂ Icc 0 H.height
    · simp [T2.stdField, indicator_of_mem hw]
    · simp [T2.stdField, indicator_of_notMem hw]
  rw [hind, lintegral_indicator (isClosed_Icc.reProdIm isClosed_Icc).measurableSet,
    Rect.setLIntegral_reProdIm]
  simp only [T2.norm_vec_sq]

/-- `∫₀² min(r, 2 - r)² dr = 2/3`. -/
theorem integral_tent_sq : ∫ r in (0 : ℝ)..2, min r (2 - r) ^ 2 = 2 / 3 := by
  have hc : Continuous fun r : ℝ => min r (2 - r) ^ 2 :=
    (continuous_id.min (continuous_const.sub continuous_id)).pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ r in (0 : ℝ)..1, min r (2 - r) ^ 2 = ∫ r in (0 : ℝ)..1, r ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le zero_le_one] at hr
    rw [min_eq_left (by linarith [hr.2])]
  have h2 : ∫ r in (1 : ℝ)..2, min r (2 - r) ^ 2 = ∫ r in (1 : ℝ)..2, (2 - r) ^ 2 := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le one_le_two] at hr
    rw [min_eq_right (by linarith [hr.1])]
  rw [h1, h2, intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) (2 : ℝ), integral_pow,
    integral_pow]
  norm_num

namespace Pinwheel

variable {c : ℂ} {t d : ℝ} {j : Fin 4} {θ w : ℝ}

/-- The carry source `f^c_j = κ (1_{A_j} - 1_{A'_j})`, `κ = 2πθ/w'`. -/
@[expose] noncomputable def carrySrc (c : ℂ) (t d : ℝ) (j : Fin 4) (θ w : ℝ) (x : ℂ) : ℝ :=
  2 * π * θ / w * ((carryA c t d j w).indicator 1 x - (carryA' c t d j w).indicator 1 x)

/-- The carry field `V^c_j = T2_{H^c_j}[f^c_j]`. -/
@[expose] noncomputable def carryField (c : ℂ) (t d : ℝ) (j : Fin 4) (θ w : ℝ) : ℂ → ℂ :=
  t2Field (carryRect c t d j w) (carrySrc c t d j θ w)

theorem abs_indicator_sub_le (A A' : Set ℂ) (x : ℂ) :
    |A.indicator (1 : ℂ → ℝ) x - A'.indicator 1 x| ≤ 1 := by
  by_cases h1 : x ∈ A <;> by_cases h2 : x ∈ A' <;> simp [h1, h2]

theorem abs_carrySrc_le (x : ℂ) : |carrySrc c t d j θ w x| ≤ |2 * π * θ / w| := by
  rw [carrySrc, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_indicator_sub_le _ _ x)

theorem integrable_carrySrc : Integrable (carrySrc c t d j θ w) := by
  have hA : Integrable ((carryA c t d j w).indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff measurableSet_carryA).2
      (integrableOn_const (by rw [volume_carryA]; exact ENNReal.ofReal_ne_top))
  have hA' : Integrable ((carryA' c t d j w).indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff measurableSet_carryA').2
      (integrableOn_const (by rw [volume_carryA']; exact ENNReal.ofReal_ne_top))
  exact (hA.sub hA').const_mul _

theorem carrySrc_eq_zero_of_notMem {x : ℂ} (hx : x ∉ (carryRect c t d j w).carrier) :
    carrySrc c t d j θ w x = 0 := by
  rw [carryRect_carrier, mem_union, not_or] at hx
  simp [carrySrc, indicator_of_notMem hx.1, indicator_of_notMem hx.2]

/-- `∫_{H^c_j} f^c_j = κ (|A_j| - |A'_j|) = 0`. -/
theorem integral_carrySrc : ∫ x in (carryRect c t d j w).carrier, carrySrc c t d j θ w x = 0 := by
  have hA : IntegrableOn ((carryA c t d j w).indicator (1 : ℂ → ℝ))
      (carryRect c t d j w).carrier :=
    ((integrable_indicator_iff measurableSet_carryA).2
      (integrableOn_const (by rw [volume_carryA]; exact ENNReal.ofReal_ne_top))).integrableOn
  have hA' : IntegrableOn ((carryA' c t d j w).indicator (1 : ℂ → ℝ))
      (carryRect c t d j w).carrier :=
    ((integrable_indicator_iff measurableSet_carryA').2
      (integrableOn_const (by rw [volume_carryA']; exact ENNReal.ofReal_ne_top))).integrableOn
  simp only [carrySrc]
  rw [integral_const_mul, integral_sub hA hA', integral_indicator_one measurableSet_carryA,
    integral_indicator_one measurableSet_carryA', measureReal_restrict_apply measurableSet_carryA,
    measureReal_restrict_apply measurableSet_carryA', carryRect_carrier,
    inter_eq_left.2 subset_union_left, inter_eq_left.2 subset_union_right, Measure.real,
    Measure.real, volume_carryA, volume_carryA', sub_self, mul_zero]

/-- The carry source in carry coordinates: `f^c(Ψ^c(s, r)) = κ (1_{[0,1]}(r) - 1_{[1,2]}(r))` for
`s ∈ [0, w']`. -/
theorem src_carrySrc {s r : ℝ} (hs : s ∈ Icc 0 w) :
    (carryRect c t d j w).src (carrySrc c t d j θ w) (s, r) =
      2 * π * θ / w * ((Icc (0 : ℝ) 1).indicator 1 r - (Icc (1 : ℝ) 2).indicator 1 r) := by
  have hs' : (⟨s, r⟩ : ℂ).re ∈ Icc 0 w := hs
  simp only [Rect.src, carrySrc]
  congr 2
  · by_cases hr : r ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem ((carryRect_chart_mem_carryA hs').2 hr), indicator_of_mem hr]; rfl
    · rw [indicator_of_notMem (fun h => hr ((carryRect_chart_mem_carryA hs').1 h)),
        indicator_of_notMem hr]
  · by_cases hr : r ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem ((carryRect_chart_mem_carryA' hs').2 hr), indicator_of_mem hr]; rfl
    · rw [indicator_of_notMem (fun h => hr ((carryRect_chart_mem_carryA' hs').1 h)),
        indicator_of_notMem hr]

theorem intervalIntegral_indicator_one {a b : ℝ} (hab : a ≤ b) (I : Set ℝ) (hI : MeasurableSet I) :
    ∫ r in a..b, I.indicator (1 : ℝ → ℝ) r = volume.real (I ∩ Ioc a b) := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator_one hI,
    measureReal_restrict_apply hI]

/-- **`F₁ ≡ 0`** on the carry cell. -/
theorem line_carrySrc {s : ℝ} (hs : s ∈ Icc 0 w) :
    T2.line 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) s = 0 := by
  unfold T2.line
  simp only [src_carrySrc hs]
  have hi : ∀ I : Set ℝ, MeasurableSet I →
      IntervalIntegrable (I.indicator (1 : ℝ → ℝ)) volume 0 2 := fun I hI =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_two).2
      ((integrableOn_const (C := (1 : ℝ)) (by simp)).indicator hI)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (hi _ measurableSet_Icc) (hi _ measurableSet_Icc),
    intervalIntegral_indicator_one zero_le_two _ measurableSet_Icc,
    intervalIntegral_indicator_one zero_le_two _ measurableSet_Icc]
  have e1 : Icc (0 : ℝ) 1 ∩ Ioc 0 2 = Ioc 0 1 := by
    ext r; simp only [mem_inter_iff, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, _⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1, by linarith⟩
  have e2 : Icc (1 : ℝ) 2 ∩ Ioc 0 2 = Icc 1 2 := by
    ext r; simp only [mem_inter_iff, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨h, _⟩; exact h
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by linarith, h2⟩
  rw [e1, e2, Real.volume_real_Ioc, Real.volume_real_Icc]
  norm_num

/-- The tent profile: `|B(s, r)| ≤ κ min(r, 2 - r)` on the carry cell. -/
theorem abs_compB_carry_le {s r : ℝ} (hs : s ∈ Icc 0 w) (hr : r ∈ Icc (0 : ℝ) 2) :
    |T2.compB 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) s r| ≤
      |2 * π * θ / w| * min r (2 - r) := by
  set F := (carryRect c t d j w).src (carrySrc c t d j θ w)
  have hline := line_carrySrc (c := c) (t := t) (d := d) (j := j) (θ := θ) hs
  have hbd : ∀ ρ, |F (s, ρ)| ≤ |2 * π * θ / w| := fun ρ => abs_carrySrc_le _
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun ρ => F (s, ρ)) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := |2 * π * θ / w|)).mono_fun ?_
      (Filter.Eventually.of_forall fun ρ => by
        simp only [Real.norm_eq_abs, abs_abs]; exact hbd ρ)
    have hm : Measurable (carrySrc c t d j θ w) :=
      (((measurable_one.indicator measurableSet_carryA).sub
        (measurable_one.indicator measurableSet_carryA')).const_mul _)
    exact (hm.comp ((carryRect c t d j w).continuous_chart.measurable.comp
      (T2.continuous_mk.comp (continuous_const.prodMk continuous_id)).measurable)).aestronglyMeasurable
  rw [T2.compB_eq_of_line hline, mul_min_of_nonneg _ _ (abs_nonneg _)]
  refine le_min ?_ ?_
  · calc |∫ ρ in (0 : ℝ)..r, F (s, ρ)| ≤ ∫ ρ in (0 : ℝ)..r, |F (s, ρ)| :=
          intervalIntegral.abs_integral_le_integral_abs hr.1
      _ ≤ ∫ _ρ in (0 : ℝ)..r, |2 * π * θ / w| :=
          intervalIntegral.integral_mono_on hr.1 (hint 0 r).abs intervalIntegrable_const
            fun ρ _ => hbd ρ
      _ = |2 * π * θ / w| * r := by simp [mul_comm]
  · have hsplit : ∫ ρ in (0 : ℝ)..r, F (s, ρ) = -∫ ρ in r..2, F (s, ρ) := by
      have := intervalIntegral.integral_add_adjacent_intervals (hint 0 r) (hint r 2)
      have h2 : ∫ ρ in (0 : ℝ)..2, F (s, ρ) = 0 := hline
      linarith
    rw [hsplit, abs_neg]
    calc |∫ ρ in r..2, F (s, ρ)| ≤ ∫ ρ in r..2, |F (s, ρ)| :=
          intervalIntegral.abs_integral_le_integral_abs hr.2
      _ ≤ ∫ _ρ in r..2, |2 * π * θ / w| :=
          intervalIntegral.integral_mono_on hr.2 (hint r 2).abs intervalIntegrable_const
            fun ρ _ => hbd ρ
      _ = |2 * π * θ / w| * (2 - r) := by simp [mul_comm]

/-- `A ≡ 0` on the carry cell. -/
theorem compA_carry {s : ℝ} (hs : s ∈ Icc 0 w) :
    T2.compA 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) s = 0 :=
  T2.compA_eq_zero_of_line (a := w) (fun _ hσ => line_carrySrc hσ) hs

/-- **Weak identity of the carry field** (screening note, Lemma 4.20): `∫ ⟪V^c_j, ∇φ⟫ = -∫ f^c_j φ` for every
Lipschitz `φ`. -/
theorem integral_inner_carryField (hw : 0 < w) {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (carryField c t d j θ w x) (gradient φ x) =
      -∫ x, carrySrc c t d j θ w x * φ x := by
  rw [carryField, integral_inner_t2Field _ hw (by norm_num) integrable_carrySrc.integrableOn
    integral_carrySrc hφ]
  congr 1
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [carrySrc_eq_zero_of_notMem hx, zero_mul]

/-- `V^c_j` is a field piece without charges and with source `f^c_j`. -/
theorem isFieldPiece_carryField (hw : 0 < w) :
    IsFieldPiece (carryField c t d j θ w) ∅ (carrySrc c t d j θ w) := by
  have h := isFieldPiece_t2Field (carryRect c t d j w) hw (by norm_num)
    (f := carrySrc c t d j θ w) integrable_carrySrc.integrableOn integral_carrySrc
  have e : (carryRect c t d j w).carrier.indicator (carrySrc c t d j θ w) = carrySrc c t d j θ w := by
    ext x
    by_cases hx : x ∈ (carryRect c t d j w).carrier
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, carrySrc_eq_zero_of_notMem hx]
  rw [e] at h
  exact h

/-- **Energy of the carry field** (screening note, Lemma 4.20): `∫ |V^c_j|² ≤ (2/3) κ² w' = 8π²θ²/(3w')`. -/
theorem lintegral_norm_sq_carryField_le (hw : 0 < w) :
    ∫⁻ x, ENNReal.ofReal (‖carryField c t d j θ w x‖ ^ 2) ≤
      ENNReal.ofReal (8 * π ^ 2 * θ ^ 2 / (3 * w)) := by
  set κ := 2 * π * θ / w
  rw [carryField, lintegral_norm_sq_t2Field_eq]
  simp only [carryRect_width, carryRect_height]
  have hbd : ∀ p ∈ Icc 0 w ×ˢ Icc (0 : ℝ) 2,
      ENNReal.ofReal (T2.compA 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) p.1 ^ 2 +
        T2.compB 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) p.1 p.2 ^ 2) ≤
      ENNReal.ofReal (κ ^ 2 * min p.2 (2 - p.2) ^ 2) := by
    rintro ⟨s, r⟩ ⟨hs, hr⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [compA_carry hs, zero_pow two_ne_zero, zero_add]
    have h1 := abs_compB_carry_le (c := c) (t := t) (d := d) (j := j) (θ := θ) hs hr
    have h0 : 0 ≤ min r (2 - r) := le_min hr.1 (by linarith [hr.2])
    calc T2.compB 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) s r ^ 2
        = |T2.compB 2 ((carryRect c t d j w).src (carrySrc c t d j θ w)) s r| ^ 2 := (sq_abs _).symm
      _ ≤ (|κ| * min r (2 - r)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = κ ^ 2 * min r (2 - r) ^ 2 := by rw [mul_pow, sq_abs]
  refine (setLIntegral_mono' (measurableSet_Icc.prod measurableSet_Icc) hbd).trans (le_of_eq ?_)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hc : Continuous fun r : ℝ => κ ^ 2 * min r (2 - r) ^ 2 :=
    continuous_const.mul ((continuous_id.min (continuous_const.sub continuous_id)).pow 2)
  have := lintegral_prod_mul (μ := volume.restrict (Icc 0 w)) (ν := volume.restrict (Icc (0 : ℝ) 2))
    (f := fun _ => (1 : ℝ≥0∞)) (g := fun r => ENNReal.ofReal (κ ^ 2 * min r (2 - r) ^ 2))
    aemeasurable_const (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
  simp only [one_mul] at this
  rw [this, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, sub_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc)
    (Filter.Eventually.of_forall fun r => by positivity), ← ENNReal.ofReal_mul hw.le]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_two,
    intervalIntegral.integral_const_mul, integral_tent_sq]
  simp only [κ]
  field_simp
  ring

/-- `∫ |V^c_j|² ≤ 8π²/(3ℓc)` for `θ ∈ [0, 1)` and `w' ≥ ℓc > 0`. -/
theorem lintegral_norm_sq_carryField_le' {ℓ : ℝ} (hℓ : 0 < ℓ) (hw : ℓ ≤ w) (hθ : θ ∈ Ico (0 : ℝ) 1) :
    ∫⁻ x, ENNReal.ofReal (‖carryField c t d j θ w x‖ ^ 2) ≤
      ENNReal.ofReal (8 * π ^ 2 / (3 * ℓ)) := by
  refine (lintegral_norm_sq_carryField_le (hℓ.trans_le hw)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith [hθ.1, hθ.2]
  have hπ := Real.pi_pos
  have hw0 : 0 < w := hℓ.trans_le hw
  calc 8 * π ^ 2 * θ ^ 2 / (3 * w) ≤ 8 * π ^ 2 * 1 / (3 * w) := by gcongr
    _ ≤ 8 * π ^ 2 / (3 * ℓ) := by rw [mul_one]; gcongr

end Pinwheel

end SandierSerfaty.Screening

end
