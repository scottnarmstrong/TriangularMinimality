/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The rectangle solver T2 in coordinates (screening note, Lemma 4.4, core)

The screening note, Lemma 4.4 (`lem:T2`), in the coordinates `(s, r)` of the
rectangle `[0, a] × [0, b] ⊆ ℝ × ℝ`. For a source `g ∈ L¹([0, a] × [0, b])` put

* `F₁(s) = ∫₀ᵇ g(s, r) dr` (`T2.line`), `G(s) = ∫₀ᵇ |g(s, r)| dr` (`T2.lineAbs`);
* `A(s) = b⁻¹ ∫₀ˢ F₁` (`T2.compA`), `B(s, r) = ∫₀ʳ (g(s, ρ) - F₁(s)/b) dρ` (`T2.compB`).

Main results:

* `T2.integral_primitive_mul`: `∫₀ᵃ (∫₀ˢ F) G(s) ds = ∫₀ᵃ F(σ) (∫_σ^a G) dσ` (Fubini on a triangle);
* the bounds of Lemma 4.4(a): `T2.abs_compA_le`, `T2.abs_compB_le`, the end value
  `T2.compB_height`;
* `T2.aestronglyMeasurable_compB`: `B` is a.e. strongly measurable on the rectangle (through a strongly
  measurable representative of `g`);
* `T2.integral_core`: the weak identity of Lemma 4.4(b) for `C¹` test functions, in partial-derivative
  form: `∫_R (A ∂ₛψ + B ∂ᵣψ) = -∫_R g ψ` when `∫_R g = 0`. The proof is Fubini plus the fundamental
  theorem of calculus applied to `ψ` only, as in the screening note.

The energy bounds are in `SandierSerfaty.Screening.RectangleEnergy`, the field in `ℂ` on a rectangle
with an arbitrary orthogonal frame in `SandierSerfaty.Screening.RectangleSolver`.
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty.Screening.T2

/-- `F₁(s) = ∫₀ᵇ g(s, r) dr`. -/
@[expose] noncomputable def line (b : ℝ) (g : ℝ × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..b, g (s, r)

/-- `G(s) = ∫₀ᵇ |g(s, r)| dr`. -/
@[expose] noncomputable def lineAbs (b : ℝ) (g : ℝ × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..b, |g (s, r)|

/-- `A(s) = b⁻¹ ∫₀ˢ F₁`. -/
@[expose] noncomputable def compA (b : ℝ) (g : ℝ × ℝ → ℝ) (s : ℝ) : ℝ :=
  b⁻¹ * ∫ σ in (0 : ℝ)..s, line b g σ

/-- `B(s, r) = ∫₀ʳ (g(s, ρ) - F₁(s)/b) dρ`. -/
@[expose] noncomputable def compB (b : ℝ) (g : ℝ × ℝ → ℝ) (s r : ℝ) : ℝ :=
  ∫ ρ in (0 : ℝ)..r, (g (s, ρ) - line b g s / b)

/-! ### Interval integrals as set integrals -/

theorem intervalIntegral_eq_Icc {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..a, f x = ∫ x in Icc 0 a, f x := by
  rw [intervalIntegral.integral_of_le ha, integral_Icc_eq_integral_Ioc]

theorem intervalIntegrable_of_Icc {a : ℝ} {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 a)) {c d : ℝ}
    (hc : c ∈ Icc 0 a) (hd : d ∈ Icc 0 a) : IntervalIntegrable f volume c d :=
  (hf.mono_set (uIcc_subset_Icc hc hd)).intervalIntegrable

/-! ### Fubini on a triangle -/

theorem setIntegral_Icc_indicator_Iic {a s : ℝ} (h0 : 0 ≤ s) (hs : s ≤ a) (f : ℝ → ℝ) :
    ∫ σ in Icc 0 a, (Iic s).indicator f σ = ∫ σ in (0 : ℝ)..s, f σ := by
  rw [setIntegral_indicator measurableSet_Iic, intervalIntegral_eq_Icc h0]
  have : Icc 0 a ∩ Iic s = Icc 0 s := by
    ext σ; simp only [mem_inter_iff, mem_Icc, mem_Iic]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hs⟩, h.2⟩⟩
  rw [this]

theorem setIntegral_Icc_indicator_Ici {a σ : ℝ} (h0 : 0 ≤ σ) (hσ : σ ≤ a) (f : ℝ → ℝ) :
    ∫ s in Icc 0 a, (Ici σ).indicator f s = ∫ s in σ..a, f s := by
  rw [setIntegral_indicator measurableSet_Ici, intervalIntegral.integral_of_le hσ,
    ← integral_Icc_eq_integral_Ioc]
  have : Icc 0 a ∩ Ici σ = Icc σ a := by
    ext s; simp only [mem_inter_iff, mem_Icc, mem_Ici]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h0.trans h.1, h.2⟩, h.1⟩⟩
  rw [this]

/-- **Fubini on a triangle**: `∫₀ᵃ (∫₀ˢ F) G(s) ds = ∫₀ᵃ F(σ) (∫_σ^a G) dσ`. -/
theorem integral_primitive_mul {a : ℝ} (ha : 0 ≤ a) {F G : ℝ → ℝ} (hF : IntegrableOn F (Icc 0 a))
    (hG : IntegrableOn G (Icc 0 a)) :
    ∫ s in (0 : ℝ)..a, (∫ σ in (0 : ℝ)..s, F σ) * G s =
      ∫ σ in (0 : ℝ)..a, F σ * ∫ s in σ..a, G s := by
  set μ := volume.restrict (Icc (0 : ℝ) a)
  set H : ℝ → ℝ → ℝ := fun s σ => if σ ≤ s then F σ * G s else 0 with hH
  have hint : Integrable (Function.uncurry H) (μ.prod μ) := by
    have h1 : Integrable (fun z : ℝ × ℝ => G z.1 * F z.2) (μ.prod μ) := hG.mul_prod hF
    have h2 := h1.indicator (measurableSet_le measurable_snd measurable_fst)
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, hH, indicator, mem_ofPred_eq]
    split_ifs <;> ring
  have hswap := integral_integral_swap hint
  have hL : ∫ s, ∫ σ, H s σ ∂μ ∂μ = ∫ s in (0 : ℝ)..a, (∫ σ in (0 : ℝ)..s, F σ) * G s := by
    rw [intervalIntegral_eq_Icc ha]
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have : (fun σ => H s σ) = (Iic s).indicator fun σ => F σ * G s := by
      ext σ; simp [hH, indicator]
    simp only [this]
    rw [setIntegral_Icc_indicator_Iic hs.1 hs.2, intervalIntegral.integral_mul_const]
  have hR : ∫ σ, ∫ s, H s σ ∂μ ∂μ = ∫ σ in (0 : ℝ)..a, F σ * ∫ s in σ..a, G s := by
    rw [intervalIntegral_eq_Icc ha]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have : (fun s => H s σ) = (Ici σ).indicator fun s => F σ * G s := by
      ext s; simp [hH, indicator]
    simp only [this]
    rw [setIntegral_Icc_indicator_Ici hσ.1 hσ.2, intervalIntegral.integral_const_mul]
  rw [← hL, ← hR, hswap]

/-! ### Fubini facts for the source -/

section Source

variable {a b : ℝ} {g : ℝ × ℝ → ℝ}

theorem restrict_rect (a b : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Icc 0 a ×ˢ Icc 0 b) =
      (volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b)) := by
  rw [Measure.prod_restrict]; rfl

theorem integrable_prod_of_integrableOn (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    Integrable g ((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))) := by
  rw [← restrict_rect]; exact hg

theorem line_eq (hb : 0 ≤ b) (g : ℝ × ℝ → ℝ) (s : ℝ) :
    line b g s = ∫ r, g (s, r) ∂(volume.restrict (Icc (0 : ℝ) b)) :=
  intervalIntegral_eq_Icc hb _

theorem lineAbs_eq (hb : 0 ≤ b) (g : ℝ × ℝ → ℝ) (s : ℝ) :
    lineAbs b g s = ∫ r, ‖g (s, r)‖ ∂(volume.restrict (Icc (0 : ℝ) b)) :=
  intervalIntegral_eq_Icc hb _

theorem lineAbs_nonneg (hb : 0 ≤ b) (g : ℝ × ℝ → ℝ) (s : ℝ) : 0 ≤ lineAbs b g s :=
  intervalIntegral.integral_nonneg hb fun _ _ => abs_nonneg _

theorem abs_line_le (hb : 0 ≤ b) (g : ℝ × ℝ → ℝ) (s : ℝ) : |line b g s| ≤ lineAbs b g s :=
  intervalIntegral.abs_integral_le_integral_abs hb

/-- For a.e. `s ∈ [0, a]` the section `g(s, ·)` is integrable on `[0, b]`. -/
theorem ae_integrableOn_section (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) a)), IntegrableOn (fun r => g (s, r)) (Icc 0 b) :=
  (integrable_prod_of_integrableOn hg).prod_right_ae

theorem integrableOn_line (hb : 0 ≤ b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    IntegrableOn (line b g) (Icc 0 a) := by
  have h := (integrable_prod_of_integrableOn hg).integral_prod_left
  exact h.congr (Eventually.of_forall fun s => (line_eq hb g s).symm)

theorem integrableOn_lineAbs (hb : 0 ≤ b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    IntegrableOn (lineAbs b g) (Icc 0 a) := by
  have h := (integrable_prod_of_integrableOn hg).integral_norm_prod_left
  exact h.congr (Eventually.of_forall fun s => (lineAbs_eq hb g s).symm)

theorem integral_line (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    ∫ s in (0 : ℝ)..a, line b g s = ∫ p in Icc 0 a ×ˢ Icc 0 b, g p := by
  rw [intervalIntegral_eq_Icc ha, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod _ hg]
  exact setIntegral_congr_fun measurableSet_Icc fun s _ => line_eq hb g s

end Source

/-! ### The components: end values and bounds (Lemma 4.4(a)) -/

section Bounds

variable {a b : ℝ} {g : ℝ × ℝ → ℝ}

/-- `B(s, b) = 0` for every `s` (zero flux through the far side). -/
theorem compB_height (hb : b ≠ 0) (g : ℝ × ℝ → ℝ) (s : ℝ) : compB b g s b = 0 := by
  unfold compB
  by_cases hi : IntervalIntegrable (fun r => g (s, r)) volume 0 b
  · rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, sub_zero]
    unfold line
    field_simp
    ring
  · refine intervalIntegral.integral_undef fun h => hi ?_
    simpa using h.add (intervalIntegrable_const (c := line b g s / b))

theorem abs_compA_le (ha : 0 ≤ a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) {s : ℝ}
    (hs : s ∈ Icc 0 a) : |compA b g s| ≤ b⁻¹ * ∫ σ in (0 : ℝ)..a, lineAbs b g σ := by
  have hF := integrableOn_line hb.le hg
  have hG := integrableOn_lineAbs hb.le hg
  rw [compA, abs_mul, abs_of_pos (inv_pos.2 hb)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hb).le
  calc |∫ σ in (0 : ℝ)..s, line b g σ| ≤ ∫ σ in (0 : ℝ)..s, |line b g σ| :=
        intervalIntegral.abs_integral_le_integral_abs hs.1
    _ ≤ ∫ σ in (0 : ℝ)..s, lineAbs b g σ :=
        intervalIntegral.integral_mono_on hs.1
          (intervalIntegrable_of_Icc hF.abs ⟨le_rfl, ha⟩ hs)
          (intervalIntegrable_of_Icc hG ⟨le_rfl, ha⟩ hs) fun σ _ => abs_line_le hb.le g σ
    _ ≤ ∫ σ in (0 : ℝ)..a, lineAbs b g σ :=
        intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
          (Eventually.of_forall fun σ => lineAbs_nonneg hb.le g σ)
          (intervalIntegrable_of_Icc hG ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩)

/-- `|B(s, r)| ≤ 2 G(s)` when the section `g(s, ·)` is integrable on `[0, b]`. -/
theorem abs_compB_le (hb : 0 < b) {s : ℝ} (hs : IntegrableOn (fun r => g (s, r)) (Icc 0 b)) {r : ℝ}
    (hr : r ∈ Icc 0 b) : |compB b g s r| ≤ 2 * lineAbs b g s := by
  have hi : IntervalIntegrable (fun ρ => g (s, ρ)) volume 0 r :=
    intervalIntegrable_of_Icc hs ⟨le_rfl, hb.le⟩ hr
  rw [compB, intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have h1 : |∫ ρ in (0 : ℝ)..r, g (s, ρ)| ≤ lineAbs b g s :=
    (intervalIntegral.abs_integral_le_integral_abs hr.1).trans
      (intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
        (Eventually.of_forall fun _ => abs_nonneg _)
        (intervalIntegrable_of_Icc hs.abs ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩))
  have h2 : |r * (line b g s / b)| ≤ lineAbs b g s := by
    rw [abs_mul, abs_div, abs_of_nonneg hr.1, abs_of_pos hb]
    calc r * (|line b g s| / b) ≤ b * (|line b g s| / b) :=
          mul_le_mul_of_nonneg_right hr.2 (by positivity)
      _ = |line b g s| := by field_simp
      _ ≤ lineAbs b g s := abs_line_le hb.le g s
  calc |(∫ ρ in (0 : ℝ)..r, g (s, ρ)) - r * (line b g s / b)|
      ≤ |∫ ρ in (0 : ℝ)..r, g (s, ρ)| + |r * (line b g s / b)| := abs_sub _ _
    _ ≤ 2 * lineAbs b g s := by linarith

theorem continuousOn_compA (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    ContinuousOn (compA b g) (Icc 0 a) := by
  have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := a)
    (by rw [uIcc_of_le ha]; exact integrableOn_line hb hg)
  rw [uIcc_of_le ha] at h
  exact continuousOn_const.mul h

end Bounds

/-! ### Lemma 4.4(c) -/

theorem compA_eq_zero_of_line {a b : ℝ} {g : ℝ × ℝ → ℝ} (h : ∀ s ∈ Icc 0 a, line b g s = 0) {s : ℝ}
    (hs : s ∈ Icc 0 a) : compA b g s = 0 := by
  rw [compA, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun σ hσ => ?_]
  · simp
  · rw [uIcc_of_le hs.1] at hσ
    exact h σ ⟨hσ.1, hσ.2.trans hs.2⟩

theorem compB_eq_of_line {b : ℝ} {g : ℝ × ℝ → ℝ} {s : ℝ} (h : line b g s = 0) (r : ℝ) :
    compB b g s r = ∫ ρ in (0 : ℝ)..r, g (s, ρ) := by
  simp [compB, h]

/-! ### Measurability of `B` -/

theorem stronglyMeasurable_line {b : ℝ} (hb : 0 ≤ b) {g : ℝ × ℝ → ℝ} (hg : StronglyMeasurable g) :
    StronglyMeasurable (line b g) := by
  have h := StronglyMeasurable.integral_prod_right (ν := volume.restrict (Icc (0 : ℝ) b))
    (f := fun s r => g (s, r)) hg
  convert h using 1
  ext s
  exact line_eq hb g s

/-- `(s, r) ↦ ∫_{(0, r]} k(s, ·)` is strongly measurable for strongly measurable `k`. -/
theorem stronglyMeasurable_primitive {k : ℝ × ℝ → ℝ} (hk : StronglyMeasurable k) :
    StronglyMeasurable fun p : ℝ × ℝ => ∫ ρ in Ioc 0 p.2, k (p.1, ρ) := by
  set S : Set ((ℝ × ℝ) × ℝ) := {q | q.2 ∈ Ioc 0 q.1.2}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)
  have hK : StronglyMeasurable (S.indicator fun q => k (q.1.1, q.2)) :=
    (hk.comp_measurable (measurable_fst.fst.prodMk measurable_snd)).indicator hS
  have h := StronglyMeasurable.integral_prod_right (ν := volume)
    (f := fun p ρ => S.indicator (fun q => k (q.1.1, q.2)) (p, ρ)) hK
  convert h using 1
  ext p
  rw [← integral_indicator measurableSet_Ioc]
  rfl

/-- `B` is a.e. strongly measurable on the rectangle. The proof passes through a strongly measurable
representative of `g`: for a.e. `s` the two sections agree a.e., hence so do the two `B`'s. -/
theorem aestronglyMeasurable_compB {a b : ℝ} (hb : 0 < b) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => compB b g p.1 p.2)
      (volume.restrict (Icc 0 a ×ˢ Icc 0 b)) := by
  have hm := (integrable_prod_of_integrableOn hg).aestronglyMeasurable
  set g' := hm.mk g
  have hg' : StronglyMeasurable g' := hm.stronglyMeasurable_mk
  have hae := Measure.ae_ae_of_ae_prod hm.ae_eq_mk
  have hmeas : StronglyMeasurable fun p : ℝ × ℝ =>
      ∫ ρ in Ioc 0 p.2, (g' (p.1, ρ) - line b g' p.1 / b) :=
    stronglyMeasurable_primitive (k := fun q => g' q - line b g' q.1 / b)
      (hg'.sub ((((stronglyMeasurable_line hb.le hg').measurable.comp measurable_fst).div_const
        b).stronglyMeasurable))
  refine ⟨_, hmeas, ?_⟩
  rw [restrict_rect]
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Icc (0 : ℝ) a)) (ν := volume.restrict (Icc (0 : ℝ) b))).ae hae
  have hmem : ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))),
      p ∈ Icc 0 a ×ˢ Icc 0 b := by
    rw [← restrict_rect]; exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [hfst, hmem] with p hp hpm
  have hae' : ∀ᵐ r, r ∈ Icc 0 b → g (p.1, r) = g' (p.1, r) :=
    (ae_restrict_iff' measurableSet_Icc).1 hp
  have hline : line b g p.1 = line b g' p.1 :=
    intervalIntegral.integral_congr_ae (hae'.mono fun r hr hr' => hr
      (Ioc_subset_Icc_self (by rwa [uIoc_of_le hb.le] at hr')))
  simp only [compB, hline]
  rw [intervalIntegral.integral_of_le hpm.2.1]
  refine setIntegral_congr_ae measurableSet_Ioc (hae'.mono fun r hr hr' => ?_)
  rw [hr ⟨hr'.1.le, hr'.2.trans hpm.2.2⟩]

/-! ### The weak identity for `C¹` test functions (Lemma 4.4(b), smooth case) -/

section Core

variable {a b : ℝ} {g : ℝ × ℝ → ℝ} {ψ ψs ψr : ℝ × ℝ → ℝ}

/-- The `A`-term: `∫₀ᵃ A ∂ₛψ(·, r) = -b⁻¹ ∫₀ᵃ F₁ ψ(·, r)` for every `r`. -/
theorem integral_compA_mul (ha : 0 < a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b))
    (h0 : ∫ p in Icc 0 a ×ˢ Icc 0 b, g p = 0) (hψ : Continuous ψ) (hψs : Continuous ψs)
    (hds : ∀ s r, HasDerivAt (fun s => ψ (s, r)) (ψs (s, r)) s) (r : ℝ) :
    ∫ s in Icc 0 a, compA b g s * ψs (s, r) = -(b⁻¹ * ∫ s in Icc 0 a, line b g s * ψ (s, r)) := by
  have hF := integrableOn_line hb.le hg
  have hc : Continuous fun s => ψ (s, r) := hψ.comp (continuous_id.prodMk continuous_const)
  have hcs : Continuous fun s => ψs (s, r) := hψs.comp (continuous_id.prodMk continuous_const)
  have hFTC : ∀ σ, ∫ s in σ..a, ψs (s, r) = ψ (a, r) - ψ (σ, r) := fun σ =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hds s r) (hcs.intervalIntegrable _ _)
  have hi1 : IntervalIntegrable (fun σ => line b g σ * ψ (a, r)) volume 0 a :=
    intervalIntegrable_of_Icc (hF.mul_const _) ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩
  have hi2 : IntervalIntegrable (fun σ => line b g σ * ψ (σ, r)) volume 0 a :=
    intervalIntegrable_of_Icc (hF.mul_continuousOn hc.continuousOn isCompact_Icc)
      ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩
  rw [← intervalIntegral_eq_Icc ha.le, ← intervalIntegral_eq_Icc ha.le]
  simp only [compA, mul_assoc]
  rw [intervalIntegral.integral_const_mul,
    integral_primitive_mul ha.le hF (hcs.integrableOn_Icc), ← mul_neg]
  congr 1
  simp only [hFTC, mul_sub]
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_mul_const,
    integral_line ha.le hb.le hg, h0]
  ring

/-- The `B`-term: `∫₀ᵇ B(s, ·) ∂ᵣψ(s, ·) = -∫₀ᵇ g(s, ·) ψ(s, ·) + b⁻¹ ∫₀ᵇ F₁(s) ψ(s, ·)` when
`g(s, ·)` is integrable. -/
theorem integral_compB_mul (hb : 0 < b) {s : ℝ} (hs : IntegrableOn (fun r => g (s, r)) (Icc 0 b))
    (hψ : Continuous ψ) (hψr : Continuous ψr)
    (hdr : ∀ s r, HasDerivAt (fun r => ψ (s, r)) (ψr (s, r)) r) :
    ∫ r in Icc 0 b, compB b g s r * ψr (s, r) =
      -(∫ r in Icc 0 b, g (s, r) * ψ (s, r)) + b⁻¹ * ∫ r in Icc 0 b, line b g s * ψ (s, r) := by
  set h : ℝ → ℝ := fun ρ => g (s, ρ) - line b g s / b with hh
  have hhi : IntegrableOn h (Icc 0 b) := hs.sub (integrableOn_const (by simp))
  have hc : Continuous fun r => ψ (s, r) := hψ.comp (continuous_const.prodMk continuous_id)
  have hcr : Continuous fun r => ψr (s, r) := hψr.comp (continuous_const.prodMk continuous_id)
  have hFTC : ∀ ρ, ∫ r in ρ..b, ψr (s, r) = ψ (s, b) - ψ (s, ρ) := fun ρ =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hdr s r) (hcr.intervalIntegrable _ _)
  have hint0 : ∫ ρ in (0 : ℝ)..b, h ρ = 0 := compB_height hb.ne' g s
  have hi1 : IntegrableOn (fun ρ => h ρ * ψ (s, b)) (Icc 0 b) := hhi.mul_const _
  have hi2 : IntegrableOn (fun ρ => h ρ * ψ (s, ρ)) (Icc 0 b) :=
    hhi.mul_continuousOn hc.continuousOn isCompact_Icc
  have hi3 : IntegrableOn (fun ρ => g (s, ρ) * ψ (s, ρ)) (Icc 0 b) :=
    hs.mul_continuousOn hc.continuousOn isCompact_Icc
  have hi4 : IntegrableOn (fun ρ => line b g s / b * ψ (s, ρ)) (Icc 0 b) :=
    (hc.integrableOn_Icc).const_mul _
  rw [← intervalIntegral_eq_Icc hb.le]
  simp only [compB]
  rw [integral_primitive_mul hb.le hhi hcr.integrableOn_Icc]
  simp only [hFTC, mul_sub]
  rw [intervalIntegral.integral_sub (intervalIntegrable_of_Icc hi1 ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩)
      (intervalIntegrable_of_Icc hi2 ⟨le_rfl, hb.le⟩ ⟨hb.le, le_rfl⟩),
    intervalIntegral.integral_mul_const, hint0, zero_mul,
    zero_sub, intervalIntegral_eq_Icc hb.le]
  simp only [hh, sub_mul]
  rw [integral_sub hi3 hi4]
  have : ∫ ρ in Icc 0 b, line b g s / b * ψ (s, ρ) = b⁻¹ * ∫ r in Icc 0 b, line b g s * ψ (s, r) := by
    rw [← integral_const_mul]; congr 1; ext ρ; ring
  rw [this]
  ring

/-- **The weak identity of T2 for `C¹` test functions** (screening note, Lemma 4.4(b), smooth case, in
coordinates): if `∫_R g = 0` then `∫_R (A ∂ₛψ + B ∂ᵣψ) = -∫_R g ψ`. -/
theorem integral_core (ha : 0 < a) (hb : 0 < b) (hg : IntegrableOn g (Icc 0 a ×ˢ Icc 0 b))
    (h0 : ∫ p in Icc 0 a ×ˢ Icc 0 b, g p = 0) (hψ : Continuous ψ) (hψs : Continuous ψs)
    (hψr : Continuous ψr) (hds : ∀ s r, HasDerivAt (fun s => ψ (s, r)) (ψs (s, r)) s)
    (hdr : ∀ s r, HasDerivAt (fun r => ψ (s, r)) (ψr (s, r)) r) :
    ∫ p in Icc 0 a ×ˢ Icc 0 b, (compA b g p.1 * ψs p + compB b g p.1 p.2 * ψr p) =
      -∫ p in Icc 0 a ×ˢ Icc 0 b, g p * ψ p := by
  set R := Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) b with hR
  have hRc : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hvol : (volume : Measure (ℝ × ℝ)).restrict R =
      (volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b)) := restrict_rect a b
  obtain ⟨C, hC⟩ := hRc.exists_bound_of_continuousOn hψ.continuousOn
  obtain ⟨Cr, hCr⟩ := hRc.exists_bound_of_continuousOn hψr.continuousOn
  have hF := integrableOn_line hb.le hg
  have hG := integrableOn_lineAbs hb.le hg
  have hsec := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc (0 : ℝ) a))
    (ν := volume.restrict (Icc (0 : ℝ) b))).ae (ae_integrableOn_section hg)
  have hmemR : ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))),
      p ∈ R := by
    rw [← hvol]; exact ae_restrict_mem hRm
  -- integrability
  have I1 : IntegrableOn (fun p : ℝ × ℝ => compA b g p.1 * ψs p) R :=
    (((continuousOn_compA ha.le hb.le hg).comp continuousOn_fst fun p hp => hp.1).mul
      hψs.continuousOn).integrableOn_compact hRc
  have I2 : IntegrableOn (fun p : ℝ × ℝ => compB b g p.1 p.2 * ψr p) R := by
    have hbd : Integrable (fun p : ℝ × ℝ => 2 * lineAbs b g p.1 * Cr)
        ((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))) :=
      (hG.const_mul 2).mul_prod (integrable_const Cr)
    have hBm := aestronglyMeasurable_compB hb hg
    rw [hvol] at hBm
    rw [IntegrableOn, hvol]
    refine hbd.mono' (hBm.mul hψr.aestronglyMeasurable) ?_
    filter_upwards [hsec, hmemR] with p hp hpR
    rw [norm_mul]
    exact mul_le_mul (by rw [Real.norm_eq_abs]; exact abs_compB_le hb hp hpR.2) (hCr p hpR)
      (norm_nonneg _) (mul_nonneg zero_le_two (lineAbs_nonneg hb.le g _))
  have I3 : IntegrableOn (fun p => g p * ψ p) R := hg.mul_continuousOn hψ.continuousOn hRc
  have I4 : IntegrableOn (fun p : ℝ × ℝ => line b g p.1 * ψ p) R := by
    have hbd : Integrable (fun p : ℝ × ℝ => ‖line b g p.1‖ * C)
        ((volume.restrict (Icc (0 : ℝ) a)).prod (volume.restrict (Icc (0 : ℝ) b))) :=
      hF.norm.mul_prod (integrable_const C)
    rw [IntegrableOn, hvol]
    refine hbd.mono' (hF.aestronglyMeasurable.comp_fst.mul hψ.aestronglyMeasurable) ?_
    filter_upwards [hmemR] with p hpR
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC p hpR) (norm_nonneg _)
  rw [IntegrableOn, hvol] at I1 I2 I3 I4
  -- the A-term
  have T1 : ∫ p in R, compA b g p.1 * ψs p = -(b⁻¹ * ∫ p in R, line b g p.1 * ψ p) := by
    rw [hvol, integral_prod_symm _ I1, integral_prod_symm _ I4, ← integral_const_mul,
      ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun r =>
      integral_compA_mul ha hb hg h0 hψ hψs hds r)
  -- the B-term
  have T2 : ∫ p in R, compB b g p.1 p.2 * ψr p =
      -(∫ p in R, g p * ψ p) + b⁻¹ * ∫ p in R, line b g p.1 * ψ p := by
    rw [hvol, integral_prod _ I2, integral_prod _ I3, integral_prod _ I4]
    dsimp only
    have h1 : Integrable (fun x => -∫ y in Icc 0 b, g (x, y) * ψ (x, y))
        (volume.restrict (Icc 0 a)) := I3.integral_prod_left.neg
    have h2 : Integrable (fun x => b⁻¹ * ∫ y in Icc 0 b, line b g x * ψ (x, y))
        (volume.restrict (Icc 0 a)) := I4.integral_prod_left.const_mul _
    rw [← integral_neg, ← integral_const_mul, ← integral_add h1 h2]
    refine integral_congr_ae ?_
    filter_upwards [ae_integrableOn_section hg] with s hs
    exact integral_compB_mul hb hs hψ hψr hdr
  rw [hvol, integral_add I1 I2, ← hvol, T1, T2]
  ring

end Core

end SandierSerfaty.Screening.T2

end
