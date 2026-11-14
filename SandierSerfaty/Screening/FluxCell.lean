/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.FillerPartition
public import SandierSerfaty.Screening.FieldGluing
public import SandierSerfaty.Screening.RectangleEnergy

/-!
# Flux cells (screening note, Lemma 4.19, generic form)

The screening note, Lemma 4.19 (`lem:flux`), for an arbitrary rectangle
`H = Ψ([0, a] × [0, b])` (`Rect`, any orthogonal frame) and a bottom height `0 < ℓ ≤ b`.
The *top part* is `Ψ([0, a] × [ℓ, b])` (`Rect.fluxTop`). Given a source `F` integrable on the top, the
flux-cell source is `F` on the top and the constant `c = -(aℓ)⁻¹ ∫_top F` on the bottom strip
`Ψ([0, a] × [0, ℓ))` (`Rect.fluxSrc`, `Rect.fluxConst`), and the flux-cell field is
`V = T2_H[fluxSrc]` (`Rect.fluxField`). For a column of the pinwheel, `H = H_k = H'_k ∪ T_k`,
`ℓ = ℓc`, `F = g̃` and `c = 2π(m - μ_k)`.

* `Rect.setIntegral_fluxSrc`: `∫_H fluxSrc = 0`;
* `Rect.integral_inner_fluxField`: `∫ ⟪V, ∇φ⟫ = -∫_H fluxSrc φ` for every Lipschitz `φ`;
  `Rect.isFieldPiece_fluxField`;
* `Rect.lintegral_norm_sq_fluxField_le`: `∫ |V|² ≤ (a²/b + 4b) · 4(b - ℓ) ∫_top F²` (the proof of
  Lemma 4.19(b): `G = ℓ|c| + L`, `aℓ²c² ≤ (∫L)²/a ≤ ∫L²`, `L² ≤ (b - ℓ) ∫ F²`).

Also `ofReal_sq_intervalIntegral_le` (Cauchy–Schwarz on an interval, in `ℝ≥0∞`).
-/

open MeasureTheory Set Real Filter
open scoped ENNReal NNReal

public section

namespace SandierSerfaty.Screening

/-- **Cauchy–Schwarz on an interval**: `(∫_p^q G)² ≤ (q - p) ∫_{[p,q]} G²` (no integrability needed). -/
theorem ofReal_sq_intervalIntegral_le {p q : ℝ} (hpq : p ≤ q) (G : ℝ → ℝ) :
    ENNReal.ofReal ((∫ s in p..q, G s) ^ 2) ≤
      ENNReal.ofReal (q - p) * ∫⁻ s in Icc p q, ENNReal.ofReal (G s ^ 2) := by
  by_cases hG : IntegrableOn G (Icc p q)
  swap
  · rw [intervalIntegral.integral_undef ((intervalIntegrable_iff_integrableOn_Icc_of_le hpq).not.2 hG)]
    simp
  rcases hpq.eq_or_lt with h | h
  · subst h; simp
  have hqp : 0 < q - p := sub_pos.2 h
  by_cases hJ : ∫⁻ s in Icc p q, ENNReal.ofReal (G s ^ 2) = ⊤
  · rw [hJ, ENNReal.mul_top (by simpa using hqp)]; exact le_top
  have hG2 : IntegrableOn (fun s => G s ^ 2) (Icc p q) :=
    ⟨hG.aestronglyMeasurable.pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun s => by positivity)).2 (lt_top_iff_ne_top.2 hJ)⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hG2 (Eventually.of_forall fun s => by positivity),
    ← ENNReal.ofReal_mul hqp.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hI : ∫ s in Icc p q, G s = ∫ s in p..q, G s := by
    rw [intervalIntegral.integral_of_le hpq, integral_Icc_eq_integral_Ioc]
  set I := ∫ s in p..q, G s
  set J := ∫ s in Icc p q, G s ^ 2
  have hpt : ∀ s, 2 * (I / (q - p)) * G s ≤ G s ^ 2 + (I / (q - p)) ^ 2 := fun s => by
    linarith [sq_nonneg (G s - I / (q - p))]
  have hmono : ∫ s in Icc p q, 2 * (I / (q - p)) * G s ≤
      ∫ s in Icc p q, (G s ^ 2 + (I / (q - p)) ^ 2) :=
    setIntegral_mono_on (hG.const_mul _) (hG2.add (integrableOn_const (by simp)))
      measurableSet_Icc fun s _ => hpt s
  rw [integral_const_mul, hI, integral_add hG2 (integrableOn_const (by simp)), setIntegral_const,
    Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hqp.le, smul_eq_mul] at hmono
  have e1 : 2 * (I / (q - p)) * I = 2 * (I ^ 2 / (q - p)) := by ring
  have e2 : (q - p) * (I / (q - p)) ^ 2 = I ^ 2 / (q - p) := by field_simp
  have h3 : I ^ 2 / (q - p) ≤ J := by linarith
  calc I ^ 2 = (q - p) * (I ^ 2 / (q - p)) := by field_simp
    _ ≤ (q - p) * J := mul_le_mul_of_nonneg_left h3 hqp.le

namespace Rect

variable (H : Rect)

/-- The top part `Ψ([0, a] × [ℓ, b])` of a flux cell. -/
@[expose] def fluxTop (ℓ : ℝ) : Set ℂ := H.box (Icc 0 H.width) (Icc ℓ H.height)

/-- The compensating constant `c = -(aℓ)⁻¹ ∫_top F` of a flux cell. -/
@[expose] noncomputable def fluxConst (ℓ : ℝ) (F : ℂ → ℝ) : ℝ :=
  -(∫ x in H.fluxTop ℓ, F x) / (H.width * ℓ)

/-- The flux-cell source: the constant `c` on the bottom strip `{r < ℓ}`, `F` above. -/
@[expose] noncomputable def fluxSrc (ℓ : ℝ) (F : ℂ → ℝ) (x : ℂ) : ℝ :=
  if (H.coords x).im < ℓ then H.fluxConst ℓ F else F x

/-- The flux-cell field `V = T2_H[fluxSrc]`. -/
@[expose] noncomputable def fluxField (ℓ : ℝ) (F : ℂ → ℝ) : ℂ → ℂ := t2Field H (H.fluxSrc ℓ F)

variable {H} {ℓ : ℝ} {F : ℂ → ℝ}

theorem measurableSet_fluxTop : MeasurableSet (H.fluxTop ℓ) :=
  measurableSet_box measurableSet_Icc measurableSet_Icc

theorem fluxSrc_of_mem_fluxTop {x : ℂ} (hx : x ∈ H.fluxTop ℓ) : H.fluxSrc ℓ F x = F x := by
  simp only [fluxSrc, not_lt.2 hx.2.1, ite_false]

/-- `fluxSrc = c` a.e. on the bottom box `Ψ([0, a] × [0, ℓ])`. -/
theorem ae_fluxSrc_bottom :
    ∀ᵐ x, x ∈ H.box (Icc 0 H.width) (Icc 0 ℓ) → H.fluxSrc ℓ F x = H.fluxConst ℓ F := by
  have h0 : ∀ᵐ x, x ∉ H.box univ {ℓ} :=
    measure_eq_zero_iff_ae_notMem.1 (H.volume_box_singleton_right univ ℓ)
  filter_upwards [h0] with x hx hxb
  have hne : (H.coords x).im ≠ ℓ := fun he => hx ⟨mem_univ _, he⟩
  simp only [fluxSrc, lt_of_le_of_ne hxb.2.2 hne, ite_true]

variable (hℓ : 0 < ℓ) (hℓb : ℓ ≤ H.height) (hF : IntegrableOn F (H.fluxTop ℓ))
include hℓ hℓb hF

theorem integrableOn_fluxSrc : IntegrableOn (H.fluxSrc ℓ F) H.carrier := by
  have hS : MeasurableSet (H.box (Icc 0 H.width) (Icc 0 ℓ)) :=
    measurableSet_box measurableSet_Icc measurableSet_Icc
  have hfin : volume (H.box (Icc 0 H.width) (Icc 0 ℓ)) ≠ ⊤ := by
    rw [volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h1 : IntegrableOn (H.fluxSrc ℓ F) (H.box (Icc 0 H.width) (Icc 0 ℓ)) :=
    (integrableOn_const (C := H.fluxConst ℓ F) hfin).congr_fun_ae
      ((ae_restrict_iff' hS).2 (ae_fluxSrc_bottom.mono fun x hx hxb => (hx hxb).symm))
  have h2 : IntegrableOn (H.fluxSrc ℓ F) (H.fluxTop ℓ) :=
    hF.congr_fun (fun x hx => (fluxSrc_of_mem_fluxTop hx).symm) measurableSet_fluxTop
  have e : H.carrier = H.box (Icc 0 H.width) (Icc 0 ℓ) ∪ H.fluxTop ℓ := by
    rw [carrier_eq_box, fluxTop, ← box_union_right, Icc_union_Icc_eq_Icc hℓ.le hℓb]
  rw [e]; exact h1.union h2

/-- **Lemma 4.19(a)**: `∫_H fluxSrc = 0`. -/
theorem setIntegral_fluxSrc (ha : 0 < H.width) : ∫ x in H.carrier, H.fluxSrc ℓ F x = 0 := by
  have hint := integrableOn_fluxSrc hℓ hℓb hF
  rw [carrier_eq_box] at hint ⊢
  rw [H.setIntegral_box_add_right measurableSet_Icc hℓ.le hℓb hint]
  have hS : MeasurableSet (H.box (Icc 0 H.width) (Icc 0 ℓ)) :=
    measurableSet_box measurableSet_Icc measurableSet_Icc
  rw [setIntegral_congr_ae hS ae_fluxSrc_bottom, setIntegral_const,
    H.volume_real_box_Icc ha.le hℓ.le, smul_eq_mul,
    setIntegral_congr_fun (measurableSet_box measurableSet_Icc measurableSet_Icc)
      (fun x hx => fluxSrc_of_mem_fluxTop (H := H) hx)]
  rw [fluxConst, fluxTop]
  field_simp
  ring

/-- **Lemma 4.19(a)**: the weak identity `∫ ⟪V, ∇φ⟫ = -∫_H fluxSrc φ` for every Lipschitz `φ`. -/
theorem integral_inner_fluxField (ha : 0 < H.width) {φ : ℂ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (H.fluxField ℓ F x) (gradient φ x) =
      -∫ x in H.carrier, H.fluxSrc ℓ F x * φ x :=
  integral_inner_t2Field H ha (hℓ.trans_le hℓb) (integrableOn_fluxSrc hℓ hℓb hF)
    (setIntegral_fluxSrc hℓ hℓb hF ha) hφ

/-- The flux-cell field is a field piece without charges, with source `1_H fluxSrc`. -/
theorem isFieldPiece_fluxField (ha : 0 < H.width) :
    IsFieldPiece (H.fluxField ℓ F) ∅ (H.carrier.indicator (H.fluxSrc ℓ F)) :=
  isFieldPiece_t2Field H ha (hℓ.trans_le hℓb) (integrableOn_fluxSrc hℓ hℓb hF)
    (setIntegral_fluxSrc hℓ hℓb hF ha)

omit hF in
/-- The line integral of the flux-cell source: `G(s) ≤ ℓ |c| + ∫_ℓ^b |F(Ψ(s, r))| dr`. -/
theorem lineAbs_fluxSrc_le (s : ℝ) :
    T2.lineAbs H.height (H.src (H.fluxSrc ℓ F)) s ≤
      ℓ * |H.fluxConst ℓ F| + ∫ r in ℓ..H.height, |F (H.chart ⟨s, r⟩)| := by
  have hL0 : 0 ≤ ∫ r in ℓ..H.height, |F (H.chart ⟨s, r⟩)| :=
    intervalIntegral.integral_nonneg hℓb fun r _ => abs_nonneg _
  have hc0 : 0 ≤ ℓ * |H.fluxConst ℓ F| := mul_nonneg hℓ.le (abs_nonneg _)
  unfold T2.lineAbs
  by_cases hi : IntervalIntegrable (fun r => |H.src (H.fluxSrc ℓ F) (s, r)|) volume 0 H.height
  swap
  · rw [intervalIntegral.integral_undef hi]; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.mono_set (by
      rw [uIcc_of_le hℓ.le, uIcc_of_le (hℓ.le.trans hℓb)]; exact Icc_subset_Icc le_rfl hℓb))
    (hi.mono_set (by
      rw [uIcc_of_le hℓb, uIcc_of_le (hℓ.le.trans hℓb)]; exact Icc_subset_Icc hℓ.le le_rfl))]
  have e1 : ∫ r in (0 : ℝ)..ℓ, |H.src (H.fluxSrc ℓ F) (s, r)| = ℓ * |H.fluxConst ℓ F| := by
    have : ∀ᵐ r, r ∈ uIoc (0 : ℝ) ℓ → |H.src (H.fluxSrc ℓ F) (s, r)| = |H.fluxConst ℓ F| := by
      have hne : ∀ᵐ r : ℝ, r ≠ ℓ := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hne] with r hr hrI
      rw [uIoc_of_le hℓ.le] at hrI
      simp only [src, fluxSrc, coords_chart, lt_of_le_of_ne hrI.2 hr, ite_true]
    rw [intervalIntegral.integral_congr_ae this, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero]
  have e2 : ∫ r in ℓ..H.height, |H.src (H.fluxSrc ℓ F) (s, r)| =
      ∫ r in ℓ..H.height, |F (H.chart ⟨s, r⟩)| := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hℓb] at hr
    simp only [src, fluxSrc, coords_chart, not_lt.2 hr.1, ite_false]
  rw [e1, e2]

/-- **Lemma 4.19(b)**, energy of a flux cell:
`∫ |V|² ≤ (a²/b + 4b) · 4(b - ℓ) · ∫_top F²`. -/
theorem lintegral_norm_sq_fluxField_le (ha : 0 < H.width) :
    ∫⁻ x, ENNReal.ofReal (‖H.fluxField ℓ F x‖ ^ 2) ≤
      ENNReal.ofReal ((H.width ^ 2 / H.height + 4 * H.height) * (4 * (H.height - ℓ))) *
        ∫⁻ x in H.fluxTop ℓ, ENNReal.ofReal (F x ^ 2) := by
  set a := H.width
  set b := H.height
  have hb : 0 < b := hℓ.trans_le hℓb
  set c := H.fluxConst ℓ F
  set L : ℝ → ℝ := fun s => ∫ r in ℓ..b, |F (H.chart ⟨s, r⟩)| with hLdef
  set J := ∫⁻ x in H.fluxTop ℓ, ENNReal.ofReal (F x ^ 2)
  -- the top in coordinates
  have hF' : IntegrableOn (fun p : ℝ × ℝ => F (H.chart ⟨p.1, p.2⟩)) (Icc 0 a ×ˢ Icc ℓ b) :=
    (H.integrableOn_box_iff F _ _).1 hF
  have hJ : J = ∫⁻ s in Icc 0 a, ∫⁻ r in Icc ℓ b, ENNReal.ofReal (F (H.chart ⟨s, r⟩) ^ 2) := by
    simp only [J, fluxTop]
    rw [setLIntegral_box, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
      ← Measure.prod_restrict]
    refine lintegral_prod _ ?_
    rw [Measure.prod_restrict]
    exact (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)).comp_aemeasurable
      hF'.aestronglyMeasurable.aemeasurable
  -- Cauchy–Schwarz on each vertical segment of the top
  have hLsq : ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) ≤ ENNReal.ofReal (b - ℓ) * J := by
    rw [hJ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc fun s _ => ?_
    refine (ofReal_sq_intervalIntegral_le hℓb _).trans_eq ?_
    simp only [sq_abs]
  -- the constant: `a (ℓc)² ≤ ∫_{[0,a]} L²`
  have hLint : IntegrableOn L (Icc 0 a) :=
    H.integrableOn_line_box (F := fun x => |F x|) hℓb hF.abs
  have htop : |∫ x in H.fluxTop ℓ, F x| ≤ ∫ s in (0 : ℝ)..a, L s := by
    rw [fluxTop, H.setIntegral_box_Icc ha.le hℓb hF]
    refine (intervalIntegral.abs_integral_le_integral_abs ha.le).trans ?_
    refine intervalIntegral.integral_mono_on ha.le
      (T2.intervalIntegrable_of_Icc (H.integrableOn_line_box hℓb hF).abs ⟨le_rfl, ha.le⟩
        ⟨ha.le, le_rfl⟩)
      (T2.intervalIntegrable_of_Icc hLint ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩) fun s _ => ?_
    exact intervalIntegral.abs_integral_le_integral_abs hℓb
  have hconst : ENNReal.ofReal (a * (ℓ * |c|) ^ 2) ≤ ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) := by
    have hcs := ofReal_sq_intervalIntegral_le ha.le L
    rw [sub_zero] at hcs
    have hc : |c| = |∫ x in H.fluxTop ℓ, F x| / (a * ℓ) := by
      simp only [c, fluxConst, abs_div, abs_neg, abs_mul, abs_of_pos (show 0 < H.width from ha),
        abs_of_pos hℓ]
      rfl
    have e : a * (ℓ * |c|) ^ 2 = (∫ x in H.fluxTop ℓ, F x) ^ 2 / a := by
      rw [hc, show ℓ * (|∫ x in H.fluxTop ℓ, F x| / (a * ℓ)) = |∫ x in H.fluxTop ℓ, F x| / a by
        field_simp, div_pow, sq_abs]
      field_simp
    have hsq : (∫ x in H.fluxTop ℓ, F x) ^ 2 ≤ (∫ s in (0 : ℝ)..a, L s) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) htop 2
    calc ENNReal.ofReal (a * (ℓ * |c|) ^ 2)
        ≤ ENNReal.ofReal (a⁻¹ * (∫ s in (0 : ℝ)..a, L s) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [e, div_eq_inv_mul]; gcongr
      _ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal ((∫ s in (0 : ℝ)..a, L s) ^ 2) :=
          ENNReal.ofReal_mul (inv_nonneg.2 ha.le)
      _ ≤ ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2)) := by
          gcongr
      _ = ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), inv_mul_cancel₀ ha.ne',
            ENNReal.ofReal_one, one_mul]
  -- pointwise: `G² ≤ 2(ℓ|c|)² + 2 L²`
  have hpt : ∀ s, ENNReal.ofReal (T2.lineAbs b (H.src (H.fluxSrc ℓ F)) s ^ 2) ≤
      ENNReal.ofReal (2 * (ℓ * |c|) ^ 2) + 2 * ENNReal.ofReal (L s ^ 2) := by
    intro s
    have h1 := lineAbs_fluxSrc_le (F := F) hℓ hℓb s
    have h0 := T2.lineAbs_nonneg hb.le (H.src (H.fluxSrc ℓ F)) s
    have hL0 : 0 ≤ L s := intervalIntegral.integral_nonneg hℓb fun r _ => abs_nonneg _
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : T2.lineAbs b (H.src (H.fluxSrc ℓ F)) s ^ 2 ≤ (ℓ * |c| + L s) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    linarith [sq_nonneg (ℓ * |c| - L s)]
  have hG : ∫⁻ s in Icc 0 a, ENNReal.ofReal (T2.lineAbs b (H.src (H.fluxSrc ℓ F)) s ^ 2) ≤
      ENNReal.ofReal (4 * (b - ℓ)) * J := by
    calc _ ≤ ∫⁻ s in Icc 0 a, (ENNReal.ofReal (2 * (ℓ * |c|) ^ 2) + 2 * ENNReal.ofReal (L s ^ 2)) :=
          lintegral_mono fun s => hpt s
      _ = ENNReal.ofReal (2 * (ℓ * |c|) ^ 2) * ENNReal.ofReal a +
            2 * ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, Real.volume_Icc, sub_zero,
            lintegral_const_mul' _ _ (by simp)]
      _ = 2 * ENNReal.ofReal (a * (ℓ * |c|) ^ 2) +
            2 * ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 2; ring
      _ ≤ 2 * (∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2)) +
            2 * ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hconst (by positivity)) le_rfl
      _ = 4 * ∫⁻ s in Icc 0 a, ENNReal.ofReal (L s ^ 2) := by ring
      _ ≤ 4 * (ENNReal.ofReal (b - ℓ) * J) := by gcongr
      _ = ENNReal.ofReal (4 * (b - ℓ)) * J := by
          rw [← mul_assoc, ENNReal.ofReal_mul (by norm_num)]; simp
  refine (lintegral_norm_sq_t2Field_le' H ha hb (integrableOn_fluxSrc hℓ hℓb hF)).trans ?_
  calc ENNReal.ofReal (a ^ 2 / b + 4 * b) *
        ∫⁻ s in Icc 0 a, ENNReal.ofReal (T2.lineAbs b (H.src (H.fluxSrc ℓ F)) s ^ 2)
      ≤ ENNReal.ofReal (a ^ 2 / b + 4 * b) * (ENNReal.ofReal (4 * (b - ℓ)) * J) := by gcongr
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end Rect

end SandierSerfaty.Screening

end
