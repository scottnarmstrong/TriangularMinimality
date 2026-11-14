/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.RectangleCore
public import Mathlib.Analysis.Complex.Basic

/-!
# The rectangle solver T2 in coordinates: the field and its energy (screening note, Lemma 4.4(a))

The screening note, Lemma 4.4 (`lem:T2`)(a), in the coordinates `(s, r)` of
`[0, a] × [0, b]`, with `A`, `B`, `G` as in `SandierSerfaty.Screening.RectangleCore`.

* `T2.vec b g (s, r) = A(s) + i B(s, r)`, the field in coordinates;
* `T2.integrableOn_vec`: it is integrable on the rectangle (`|A| ≤ b⁻¹ ∫ G`, `|B| ≤ 2G`);
* `T2.lintegral_sq_le`: `∫_R (A² + B²) ≤ (a/b)(∫₀ᵃ G)² + 4b ∫₀ᵃ G²`;
* `T2.ofReal_sq_integral_le`: Cauchy–Schwarz, `(∫₀ᵃ G)² ≤ a ∫₀ᵃ G²`;
* `T2.lintegral_sq_le'`: `∫_R (A² + B²) ≤ (a²/b + 4b) ∫₀ᵃ G²`.

The integrals of squares are lower Lebesgue integrals, so no `L²` hypothesis on `g` is needed.
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty.Screening.T2

/-- The T2 field in coordinates: `A(s) + i B(s, r)`. -/
@[expose] noncomputable def vec (b : ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  ⟨compA b g p.1, compB b g p.1 p.2⟩

variable {a b : ℝ} {g : ℝ × ℝ → ℝ}

theorem norm_vec_sq (b : ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    ‖vec b g p‖ ^ 2 = compA b g p.1 ^ 2 + compB b g p.1 p.2 ^ 2 := by
  rw [Complex.sq_norm, vec, Complex.normSq_mk]; ring

theorem norm_vec_le (b : ℝ) (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    ‖vec b g p‖ ≤ |compA b g p.1| + |compB b g p.1 p.2| := by
  rw [vec, Complex.mk_eq_add_mul_I]
  refine (norm_add_le _ _).trans ?_
  simp

theorem aestronglyMeasurable_vec (ha : 0 ≤ a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    AEStronglyMeasurable (vec b g) (volume.restrict (Icc 0 a ×ˢ Icc 0 b)) := by
  have hA : AEStronglyMeasurable (fun p : ℝ × ℝ => compA b g p.1)
      (volume.restrict (Icc 0 a ×ˢ Icc 0 b)) :=
    ((continuousOn_compA ha hb.le hg).comp continuousOn_fst fun p hp => hp.1).aestronglyMeasurable
      (measurableSet_Icc.prod measurableSet_Icc)
  have hB := aestronglyMeasurable_compB hb hg
  have h := (Complex.continuous_ofReal.comp_aestronglyMeasurable hA).add
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hB).mul_const Complex.I)
  refine h.congr (Eventually.of_forall fun p => ?_)
  simp only [Pi.add_apply, vec, Complex.mk_eq_add_mul_I]

/-- The T2 field is integrable on the rectangle. -/
theorem integrableOn_vec (ha : 0 ≤ a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    IntegrableOn (vec b g) (Icc 0 a ×ˢ Icc 0 b) := by
  set c := b⁻¹ * ∫ σ in (0 : ℝ)..a, lineAbs b g σ
  have hG := integrableOn_lineAbs hb.le hg
  have hbd : Integrable (fun p : ℝ × ℝ => (c + 2 * lineAbs b g p.1) * 1)
      ((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))) :=
    ((integrable_const c).add (hG.const_mul 2)).mul_prod (integrable_const (1 : ℝ))
  have hsec := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc (0 : ℝ) a))
    (ν := volume.restrict (Icc (0 : ℝ) b))).ae (ae_integrableOn_section hg)
  have hmem : ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))),
      p ∈ Icc 0 a ×ˢ Icc 0 b := by
    rw [← restrict_rect]; exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  have hm := aestronglyMeasurable_vec ha hb hg
  rw [restrict_rect] at hm
  rw [IntegrableOn, restrict_rect]
  refine hbd.mono' hm ?_
  filter_upwards [hsec, hmem] with p hp hpR
  rw [mul_one]
  exact (norm_vec_le b g p).trans (add_le_add (abs_compA_le ha hb hg hpR.1) (abs_compB_le hb hp hpR.2))

/-- **Energy bound of T2** (screening note, Lemma 4.4(a), first form):
`∫_R (A² + B²) ≤ (a/b) (∫₀ᵃ G)² + 4b ∫₀ᵃ G²` (lower Lebesgue integrals on the right for `G²`). -/
theorem lintegral_sq_le (ha : 0 ≤ a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    ∫⁻ p in Icc 0 a ×ˢ Icc 0 b, ENNReal.ofReal (compA b g p.1 ^ 2 + compB b g p.1 p.2 ^ 2) ≤
      ENNReal.ofReal (a / b * (∫ s in (0 : ℝ)..a, lineAbs b g s) ^ 2) +
        ENNReal.ofReal (4 * b) * ∫⁻ s in Icc 0 a, ENNReal.ofReal (lineAbs b g s ^ 2) := by
  set I := ∫ s in (0 : ℝ)..a, lineAbs b g s
  set c := (b⁻¹ * I) ^ 2 with hc
  rw [restrict_rect]
  refine (lintegral_prod_le _).trans ?_
  have hpt : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) a)),
      ∫⁻ r in Icc 0 b, ENNReal.ofReal (compA b g s ^ 2 + compB b g s r ^ 2) ≤
        ENNReal.ofReal (c * b) + ENNReal.ofReal (4 * b) * ENNReal.ofReal (lineAbs b g s ^ 2) := by
    filter_upwards [ae_integrableOn_section hg, ae_restrict_mem measurableSet_Icc] with s hs hsa
    have hbound : ∀ r ∈ Icc 0 b, ENNReal.ofReal (compA b g s ^ 2 + compB b g s r ^ 2) ≤
        ENNReal.ofReal (c + 4 * lineAbs b g s ^ 2) := by
      intro r hr
      refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
      · rw [hc]; exact sq_le_sq' (abs_le.1 (abs_compA_le ha hb hg hsa)).1
          (abs_le.1 (abs_compA_le ha hb hg hsa)).2
      · have h2 := abs_compB_le hb hs hr
        have : compB b g s r ^ 2 ≤ (2 * lineAbs b g s) ^ 2 :=
          sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
        linarith
    calc ∫⁻ r in Icc 0 b, ENNReal.ofReal (compA b g s ^ 2 + compB b g s r ^ 2)
        ≤ ∫⁻ _r in Icc 0 b, ENNReal.ofReal (c + 4 * lineAbs b g s ^ 2) :=
          setLIntegral_mono measurable_const hbound
      _ = ENNReal.ofReal (c * b) + ENNReal.ofReal (4 * b) * ENNReal.ofReal (lineAbs b g s ^ 2) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          congr 1; ring
  refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
  rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [hc]
  field_simp

/-- **Cauchy–Schwarz on `[0, a]`**: `(∫₀ᵃ G)² ≤ a ∫₀ᵃ G²` for `G` integrable. -/
theorem ofReal_sq_integral_le (ha : 0 < a) {G : ℝ → ℝ} (hG : IntegrableOn G (Icc 0 a)) :
    ENNReal.ofReal ((∫ s in (0 : ℝ)..a, G s) ^ 2) ≤
      ENNReal.ofReal a * ∫⁻ s in Icc 0 a, ENNReal.ofReal (G s ^ 2) := by
  by_cases hJ : ∫⁻ s in Icc 0 a, ENNReal.ofReal (G s ^ 2) = ⊤
  · rw [hJ, ENNReal.mul_top (by simpa using ha)]; exact le_top
  have hG2 : IntegrableOn (fun s => G s ^ 2) (Icc 0 a) :=
    ⟨hG.aestronglyMeasurable.pow 2, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun s => by positivity)).2 (lt_top_iff_ne_top.2 hJ)⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hG2 (Eventually.of_forall fun s => by positivity),
    ← ENNReal.ofReal_mul ha.le]
  refine ENNReal.ofReal_le_ofReal ?_
  set I := ∫ s in (0 : ℝ)..a, G s
  set J := ∫ s in Icc 0 a, G s ^ 2
  -- `2 c G ≤ G² + c²` pointwise, with `c = I / a`
  have hpt : ∀ s, 2 * (I / a) * G s ≤ G s ^ 2 + (I / a) ^ 2 := fun s => by
    nlinarith [sq_nonneg (G s - I / a)]
  have hmono : ∫ s in Icc 0 a, 2 * (I / a) * G s ≤ ∫ s in Icc 0 a, (G s ^ 2 + (I / a) ^ 2) :=
    setIntegral_mono_on (hG.const_mul _) (hG2.add (integrableOn_const (by simp)))
      measurableSet_Icc fun s _ => hpt s
  rw [integral_const_mul, integral_add hG2 (integrableOn_const (by simp)), setIntegral_const,
    ← intervalIntegral_eq_Icc ha.le, Measure.real, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal ha.le, smul_eq_mul] at hmono
  have e1 : 2 * (I / a) * I = 2 * (I ^ 2 / a) := by ring
  have e2 : a * (I / a) ^ 2 = I ^ 2 / a := by field_simp
  have h3 : I ^ 2 / a ≤ J := by linarith
  calc I ^ 2 = a * (I ^ 2 / a) := by field_simp
    _ ≤ a * J := mul_le_mul_of_nonneg_left h3 ha.le

/-- **Energy bound of T2** (screening note, Lemma 4.4(a), second form):
`∫_R (A² + B²) ≤ (a²/b + 4b) ∫₀ᵃ G²`. -/
theorem lintegral_sq_le' (ha : 0 < a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    ∫⁻ p in Icc 0 a ×ˢ Icc 0 b, ENNReal.ofReal (compA b g p.1 ^ 2 + compB b g p.1 p.2 ^ 2) ≤
      ENNReal.ofReal (a ^ 2 / b + 4 * b) * ∫⁻ s in Icc 0 a, ENNReal.ofReal (lineAbs b g s ^ 2) := by
  refine (lintegral_sq_le ha.le hb hg).trans ?_
  have hCS := ofReal_sq_integral_le ha (integrableOn_lineAbs hb.le hg)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
  refine add_le_add ?_ le_rfl
  rw [ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (a / b) * ENNReal.ofReal ((∫ s in (0 : ℝ)..a, lineAbs b g s) ^ 2)
      ≤ ENNReal.ofReal (a / b) *
          (ENNReal.ofReal a * ∫⁻ s in Icc 0 a, ENNReal.ofReal (lineAbs b g s ^ 2)) := by
        gcongr
    _ = ENNReal.ofReal (a ^ 2 / b) * ∫⁻ s in Icc 0 a, ENNReal.ofReal (lineAbs b g s ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end SandierSerfaty.Screening.T2

end
