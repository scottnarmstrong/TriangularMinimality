/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.PunctureLimit
public import SandierSerfaty.Whole.TruncCompare
public import SandierSerfaty.Screening.CubeCutoff
public import SandierSerfaty.Analysis.PolarAnnulus

/-!
# A uniform Cauchy estimate for the puncture functionals on a separated set of charges

**Theorem** (`abs_punctureReal_sub_le`). Let `Λ` be a locally finite set with `|p - q| ≥ 1` for
distinct `p, q ∈ Λ`, `E` a measurable field with `|E - κ(· - p)| ≤ M` on `B(p, ¼) ∖ {p}` for every
`p ∈ Λ` and `E` bounded on each `Ω_ε = ℂ ∖ ⋃_{p ∈ Λ} B(p, ε)`, and `χ` continuous, `0 ≤ χ ≤ 1`,
`L`-Lipschitz, vanishing off `K_R = □_{2R}`. Then for `0 < η' < η ≤ ¼` the functionals `P_{η'}(χ)`, `P_η(χ)`
are real numbers and
```
|P_{η'}(χ) - P_η(χ)| ≤ #(Λ ∩ □_{2R+1}) (π (L + 2M) η + (π/2) M² η²).
```
Indeed `P_{η'} - P_η = ∑_p ½ ∫_{B(p,η) ∖ B(p,η')} (χ |E|² - χ(p) |x - p|⁻²)` (using
`∫_{B(p,η) ∖ B(p,η')} |x - p|⁻² = 2π log (η/η')`), and the integrand has modulus at most
`(L + 2M)|x - p|⁻¹ + M²`. This is the uniformity in `R` needed for the periodic average of the triangular field.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Whole

open Screening

/-- `∫_{ε ≤ ‖x‖ < ρ} ‖x‖⁻¹ = 2π (ρ - ε)`. -/
theorem integral_inv_norm_annulus {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) :
    ∫ x in {x : ℂ | ε ≤ ‖x‖ ∧ ‖x‖ < ρ}, ‖x‖⁻¹ = 2 * Real.pi * (ρ - ε) := by
  have hkey : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 * ‖(p.1 : ℂ) * Torus.dir p.2‖⁻¹ = 1 := by
    intro p hp
    rw [Torus.norm_ofReal_mul_dir, abs_of_pos hp]
    field_simp
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.1 * ‖(p.1 : ℂ) * Torus.dir p.2‖⁻¹)
      (Icc ε ρ ×ˢ Icc (-Real.pi) Real.pi) :=
    continuousOn_const.congr fun p hp => hkey p (lt_of_lt_of_le hε hp.1.1)
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖(p.1 : ℂ) * Torus.dir p.2‖⁻¹)
      (Ico ε ρ ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ico_subset_Icc_self Ioo_subset_Icc_self)
  have := Torus.integral_polar_radial (f := fun x : ℂ => ‖x‖⁻¹) measurableSet_Ico
    (fun r hr => lt_of_lt_of_le hε hr.1) hint
  have hin : ∀ θ : ℝ, ∫ r in Ico ε ρ, r * ‖(r : ℂ) * Torus.dir θ‖⁻¹ = ρ - ε := by
    intro θ
    rw [setIntegral_congr_fun measurableSet_Ico (fun r hr => hkey (r, θ) (lt_of_lt_of_le hε hr.1)),
      setIntegral_const, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul, mul_one]
  exact this.trans ((setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hin θ)).trans
    (Torus.integral_const_Ioo_pi _))

/-- `∫_{B(p, b) ∖ B(p, a)} ‖x - p‖⁻¹ = 2π (b - a)`. -/
theorem integral_inv_norm_annulus_center (p : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ x in ball p b \ ball p a, ‖x - p‖⁻¹ = 2 * Real.pi * (b - a) := by
  have hpre : ball p b \ ball p a =
      (fun x : ℂ => x - p) ⁻¹' {x : ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b} := by
    ext x
    simp only [Set.mem_sdiff, mem_ball, dist_eq_norm, not_lt, mem_preimage, mem_ofPred_eq]
    tauto
  rw [hpre]
  have hmp : MeasurePreserving (fun x : ℂ => x - p) volume volume := measurePreserving_sub_right _ p
  have := hmp.setIntegral_preimage_emb (Homeomorph.subRight p).measurableEmbedding
    (fun y : ℂ => ‖y‖⁻¹) {x : ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b}
  rw [this]
  exact integral_inv_norm_annulus ha hab

/-- A measurable function bounded on a set of finite measure is integrable there. -/
theorem integrableOn_of_le {f : ℂ → ℝ} {s : Set ℂ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤)
    (hf : AEStronglyMeasurable f volume) {C : ℝ} (hC : ∀ x ∈ s, |f x| ≤ C) : IntegrableOn f s :=
  Measure.integrableOn_of_bounded (M := C) hμ hf
    ((ae_restrict_iff' hs).2 (Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx))

/-- The real puncture expression `½ ∫_{Ω_η} χ |E|² + π log η ∑_{p ∈ Λ} χ(p)`. -/
@[expose] noncomputable def punctureReal (Λ : Set ℂ) (E : ℂ → ℂ) (χ : ℂ → ℝ) (η : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x in punctured Λ η, χ x * ‖E x‖ ^ 2) + Real.pi * Real.log η * ∑ᶠ p ∈ Λ, χ p

/-- **The uniform Cauchy estimate** for `P_η(χ)` on a `1`-separated set of charges. -/
theorem abs_punctureReal_sub_le {Λ : Set ℂ} (hC : ∀ R : ℝ, (Λ ∩ closedBall 0 R).Finite)
    (hsep : ∀ p ∈ Λ, ∀ q ∈ Λ, p ≠ q → 1 ≤ ‖p - q‖) {E : ℂ → ℂ}
    (hEm : AEStronglyMeasurable E volume) {M : ℝ} (hM : 0 ≤ M)
    (hnear : ∀ p ∈ Λ, ∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < 1 / 4 → ‖E x - kernel (x - p)‖ ≤ M)
    (hfar : ∀ ε > 0, ∃ C : ℝ, ∀ x ∈ punctured Λ ε, ‖E x‖ ≤ C)
    {χ : ℂ → ℝ} (hχc : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {L : ℝ}
    (hχL : ∀ x y, |χ x - χ y| ≤ L * ‖x - y‖) {R : ℝ} (hχs : ∀ x ∉ cube (2 * R), χ x = 0)
    {η' η : ℝ} (hη' : 0 < η') (hηη : η' < η) (hη : η ≤ 1 / 4) :
    punctureFunctional Λ E χ η' = punctureReal Λ E χ η' ∧
      punctureFunctional Λ E χ η = punctureReal Λ E χ η ∧
      |punctureReal Λ E χ η' - punctureReal Λ E χ η| ≤ (Λ ∩ cube (2 * R + 1)).ncard *
        (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) := by
  have hη0 : 0 < η := hη'.trans hηη
  have hfinS : (Λ ∩ cube (2 * R + 1)).Finite := finite_inter_cube hC (2 * R + 1)
  set S := hfinS.toFinset with hSdef
  have hSmem : ∀ p, p ∈ S ↔ p ∈ Λ ∧ p ∈ cube (2 * R + 1) := fun p => by
    rw [hSdef, Set.Finite.mem_toFinset, mem_inter_iff]
  set f : ℂ → ℝ := fun x => χ x * ‖E x‖ ^ 2 with hfdef
  have hfm : AEStronglyMeasurable f volume :=
    hχc.aestronglyMeasurable.mul (hEm.norm.pow 2)
  -- integrability on `Ω_ε`
  have hcubefin : volume (cube (2 * R)) ≠ ⊤ := (isCompact_cube (2 * R)).measure_lt_top.ne
  have hint : ∀ ε > 0, IntegrableOn f (punctured Λ ε) := by
    intro ε hε
    obtain ⟨Cε, hCε⟩ := hfar ε hε
    have h1 : IntegrableOn f (punctured Λ ε ∩ cube (2 * R)) :=
      integrableOn_of_le ((measurableSet_punctured Λ ε).inter (isCompact_cube _).measurableSet)
        (ne_top_of_le_ne_top hcubefin (measure_mono inter_subset_right)) hfm (C := Cε ^ 2)
        fun x hx => by
          rw [hfdef, abs_mul, abs_of_nonneg (hχ0 x), abs_of_nonneg (sq_nonneg _)]
          have := hCε x hx.1
          have h2 : ‖E x‖ ^ 2 ≤ Cε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
          nlinarith [hχ1 x, hχ0 x, sq_nonneg ‖E x‖]
    refine h1.of_forall_sdiff_eq_zero (measurableSet_punctured Λ ε) fun x hx => ?_
    have : x ∉ cube (2 * R) := fun h => hx.2 ⟨hx.1, h⟩
    simp [hfdef, hχs x this]
  -- the sums over `Λ`
  have hsum : ∑ᶠ p ∈ Λ, χ p = ∑ p ∈ S, χ p :=
    Screening.finsum_mem_eq_finsetSum (fun p hp => ((hSmem p).1 hp).1) fun p hpΛ hp =>
      hχs p fun h => hp ((hSmem p).2 ⟨hpΛ, Torus.cube_mono (by linarith) h⟩)
  -- uniqueness of the near charge
  have huniq : ∀ x : ℂ, ∀ p ∈ Λ, ∀ q ∈ Λ, ‖x - p‖ < 1 / 4 → ‖x - q‖ < 3 / 4 → p = q := by
    intro x p hp q hq hxp hxq
    by_contra hpq
    have h1 := hsep p hp q hq hpq
    have h2 : ‖p - q‖ ≤ ‖x - p‖ + ‖x - q‖ := by
      have := norm_sub_le (x - q) (x - p)
      rw [show x - q - (x - p) = p - q by ring] at this
      linarith
    linarith
  -- the decomposition of `Ω_{η'}`
  set A : ℂ → Set ℂ := fun p => ball p η \ ball p η' with hAdef
  have hdec : ∀ x, (punctured Λ η').indicator f x =
      (punctured Λ η).indicator f x + ∑ p ∈ S, (A p).indicator f x := by
    intro x
    by_cases hxη : x ∈ punctured Λ η
    · have hx' : x ∈ punctured Λ η' := mem_punctured.2 fun p hp =>
        hηη.le.trans ((mem_punctured.1 hxη) p hp)
      rw [indicator_of_mem hx', indicator_of_mem hxη, Finset.sum_eq_zero fun p hp => ?_, add_zero]
      refine indicator_of_notMem (fun h => ?_) _
      have := (mem_punctured.1 hxη) p ((hSmem p).1 hp).1
      have h2 := h.1
      rw [mem_ball, dist_eq_norm] at h2
      linarith
    · rw [indicator_of_notMem hxη, zero_add]
      have hq : ∃ q ∈ Λ, ‖x - q‖ < η := by
        by_contra hno
        push Not at hno
        exact hxη (mem_punctured.2 hno)
      obtain ⟨q, hqΛ, hxq⟩ := hq
      by_cases hχx : χ x = 0
      · simp [hfdef, hχx, indicator]
      · have hxK : x ∈ cube (2 * R) := by_contra fun h => hχx (hχs x h)
        have hqS : q ∈ S := (hSmem q).2 ⟨hqΛ, by
          rw [mem_cube_iff_cubeNorm] at hxK ⊢
          have := (abs_le.1 (abs_cubeNorm_sub_le q x)).2
          rw [norm_sub_rev] at this
          linarith⟩
        rw [Finset.sum_eq_single q (fun p hp hpq => indicator_of_notMem (fun h => by
            have h2 := h.1
            rw [mem_ball, dist_eq_norm] at h2
            exact hpq (huniq x q hqΛ p ((hSmem p).1 hp).1 (by linarith) (by linarith)).symm) _)
          (fun h => absurd hqS h)]
        have hiff : x ∈ punctured Λ η' ↔ x ∈ A q := by
          rw [mem_punctured]
          constructor
          · intro h
            exact ⟨by rw [mem_ball, dist_eq_norm]; exact hxq, by
              rw [mem_ball, dist_eq_norm, not_lt]; exact h q hqΛ⟩
          · rintro ⟨_, h2⟩ p hp
            rw [mem_ball, dist_eq_norm, not_lt] at h2
            by_cases hpq : p = q
            · rw [hpq]; exact h2
            · by_contra h3
              push Not at h3
              exact hpq (huniq x p hp q hqΛ (by linarith) (by linarith))
        by_cases hA : x ∈ A q
        · rw [indicator_of_mem (hiff.2 hA), indicator_of_mem hA]
        · rw [indicator_of_notMem (fun h => hA (hiff.1 h)), indicator_of_notMem hA]
  -- integrability of the annulus terms
  have hAm : ∀ p, MeasurableSet (A p) := fun p => measurableSet_ball.diff measurableSet_ball
  have hAfin : ∀ p, volume (A p) ≠ ⊤ := fun p =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hAbd : ∀ p ∈ S, ∀ x ∈ A p, ‖E x‖ ≤ M + η'⁻¹ ∧ 0 < ‖x - p‖ ∧ ‖x - p‖ < 1 / 4 ∧
      η' ≤ ‖x - p‖ := by
    intro p hp x hx
    have h1 := hx.1
    have h2 := hx.2
    rw [mem_ball, dist_eq_norm] at h1 h2
    rw [not_lt] at h2
    have hpos : 0 < ‖x - p‖ := lt_of_lt_of_le hη' h2
    have hlt : ‖x - p‖ < 1 / 4 := lt_of_lt_of_le h1 hη
    have h3 := hnear p ((hSmem p).1 hp).1 x hpos hlt
    have h4 : ‖kernel (x - p)‖ ≤ η'⁻¹ := by rw [norm_kernel]; exact inv_anti₀ hη' h2
    refine ⟨?_, hpos, hlt, h2⟩
    calc ‖E x‖ = ‖(E x - kernel (x - p)) + kernel (x - p)‖ := by rw [sub_add_cancel]
      _ ≤ ‖E x - kernel (x - p)‖ + ‖kernel (x - p)‖ := norm_add_le _ _
      _ ≤ M + η'⁻¹ := add_le_add h3 h4
  have hfA : ∀ p ∈ S, IntegrableOn f (A p) := fun p hp =>
    integrableOn_of_le (hAm p) (hAfin p) hfm (C := (M + η'⁻¹) ^ 2) fun x hx => by
      obtain ⟨hE, -⟩ := hAbd p hp x hx
      rw [hfdef, abs_mul, abs_of_nonneg (hχ0 x), abs_of_nonneg (sq_nonneg _)]
      have h2 : ‖E x‖ ^ 2 ≤ (M + η'⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE 2
      nlinarith [hχ1 x, hχ0 x, sq_nonneg ‖E x‖]
  have hkA : ∀ p, IntegrableOn (fun x => (‖x - p‖ ^ 2)⁻¹) (A p) := fun p =>
    (integrable_indicator_iff (hAm p)).1 (integrable_annulus_term p hη')
  have hinvA : ∀ p, IntegrableOn (fun x => ‖x - p‖⁻¹) (A p) := fun p =>
    integrableOn_of_le (hAm p) (hAfin p)
      ((measurable_norm.comp (measurable_id.sub_const p)).inv.aestronglyMeasurable)
      (C := η'⁻¹) fun x hx => by
        have h2 := hx.2
        rw [mem_ball, dist_eq_norm, not_lt] at h2
        rw [abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
        exact inv_anti₀ hη' h2
  -- the integral identity
  have hident : (∫ x in punctured Λ η', f x) =
      (∫ x in punctured Λ η, f x) + ∑ p ∈ S, ∫ x in A p, f x := by
    rw [← integral_indicator (measurableSet_punctured Λ η'),
      ← integral_indicator (measurableSet_punctured Λ η)]
    simp_rw [hdec]
    rw [integral_add ((integrable_indicator_iff (measurableSet_punctured Λ η)).2 (hint η hη0))
      (integrable_finsetSum S fun p hp => (integrable_indicator_iff (hAm p)).2 (hfA p hp)),
      integral_finsetSum S fun p hp => (integrable_indicator_iff (hAm p)).2 (hfA p hp)]
    congr 1
    exact Finset.sum_congr rfl fun p _ => integral_indicator (hAm p)
  -- the bound on each annulus
  have hL0 : 0 ≤ L := by
    have h := hχL 1 0
    rw [sub_zero, norm_one, mul_one] at h
    exact (abs_nonneg _).trans h
  have hper : ∀ p ∈ S, |(1 / 2 : ℝ) * (∫ x in A p, f x) - Real.pi * Real.log (η / η') * χ p| ≤
      Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2 := by
    intro p hp
    have hlog : ∫ x in A p, (‖x - p‖ ^ 2)⁻¹ = 2 * Real.pi * Real.log (η / η') :=
      Sphere.integral_inv_sq_annulus_center p hη' hηη
    have hinv : ∫ x in A p, ‖x - p‖⁻¹ = 2 * Real.pi * (η - η') :=
      integral_inv_norm_annulus_center p hη' hηη
    have hvol : volume.real (A p) ≤ Real.pi * η ^ 2 := by
      rw [Measure.real, ← ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * η ^ 2),
        ← volume_ball_eq_ofReal p hη0.le]
      exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono sdiff_subset)
    have hpt : ∀ x ∈ A p, ‖f x - χ p * (‖x - p‖ ^ 2)⁻¹‖ ≤ (L + 2 * M) * ‖x - p‖⁻¹ + M ^ 2 := by
      intro x hx
      obtain ⟨_, hpos, hlt, _⟩ := hAbd p hp x hx
      have hEκ := hnear p ((hSmem p).1 hp).1 x hpos hlt
      have hsq := abs_norm_add_sq_sub_le (k := kernel (x - p)) hEκ
      rw [add_sub_cancel, norm_kernel, inv_pow] at hsq
      have h1 : |(χ x - χ p) * (‖x - p‖ ^ 2)⁻¹| ≤ L * ‖x - p‖⁻¹ := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (‖x - p‖ ^ 2)⁻¹)]
        calc |χ x - χ p| * (‖x - p‖ ^ 2)⁻¹ ≤ L * ‖x - p‖ * (‖x - p‖ ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right (hχL x p) (by positivity)
          _ = L * ‖x - p‖⁻¹ := by field_simp
      have h2 : |χ x * (‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹)| ≤ 2 * M * ‖x - p‖⁻¹ + M ^ 2 := by
        rw [abs_mul, abs_of_nonneg (hχ0 x)]
        calc χ x * |‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹| ≤ 1 * |‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹| :=
              mul_le_mul_of_nonneg_right (hχ1 x) (abs_nonneg _)
          _ ≤ 2 * M * ‖x - p‖⁻¹ + M ^ 2 := by rw [one_mul]; exact hsq
      have e : f x - χ p * (‖x - p‖ ^ 2)⁻¹ =
          (χ x - χ p) * (‖x - p‖ ^ 2)⁻¹ + χ x * (‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹) := by
        simp only [hfdef]; ring
      rw [Real.norm_eq_abs, e]
      calc _ ≤ |(χ x - χ p) * (‖x - p‖ ^ 2)⁻¹| + |χ x * (‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹)| :=
            abs_add_le _ _
        _ ≤ (L + 2 * M) * ‖x - p‖⁻¹ + M ^ 2 := by linarith
    have hbd := norm_integral_le_of_norm_le (μ := volume.restrict (A p))
      (((hinvA p).const_mul (L + 2 * M)).add (integrableOn_const (hAfin p)))
      ((ae_restrict_iff' (hAm p)).2 (Eventually.of_forall hpt))
    simp only [Pi.add_apply] at hbd
    rw [integral_sub (hfA p hp) ((hkA p).const_mul (χ p)), integral_const_mul, hlog,
      integral_add ((hinvA p).const_mul (L + 2 * M)) (integrableOn_const (hAfin p)),
      integral_const_mul, hinv, setIntegral_const, smul_eq_mul, Real.norm_eq_abs] at hbd
    have e2 : (1 / 2 : ℝ) * (∫ x in A p, f x) - Real.pi * Real.log (η / η') * χ p =
        (1 / 2 : ℝ) * ((∫ x in A p, f x) - χ p * (2 * Real.pi * Real.log (η / η'))) := by ring
    rw [e2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hLM : 0 ≤ L + 2 * M := by linarith
    have h3 : (L + 2 * M) * (2 * Real.pi * (η - η')) ≤ (L + 2 * M) * (2 * Real.pi * η) :=
      mul_le_mul_of_nonneg_left (by nlinarith [Real.pi_pos]) hLM
    have h4 : volume.real (A p) * M ^ 2 ≤ Real.pi * η ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_right hvol (sq_nonneg M)
    linarith
  refine ⟨punctureFunctional_eq_coe (hint η' hη'), punctureFunctional_eq_coe (hint η hη0), ?_⟩
  simp only [punctureReal]
  rw [hsum, hident]
  have hlogdiff : Real.log η' = Real.log η - Real.log (η / η') := by
    rw [Real.log_div hη0.ne' hη'.ne']; ring
  have hexp : (1 / 2 : ℝ) * ((∫ x in punctured Λ η, f x) + ∑ p ∈ S, ∫ x in A p, f x) +
      Real.pi * Real.log η' * ∑ p ∈ S, χ p -
      ((1 / 2 : ℝ) * (∫ x in punctured Λ η, f x) + Real.pi * Real.log η * ∑ p ∈ S, χ p) =
      ∑ p ∈ S, ((1 / 2 : ℝ) * (∫ x in A p, f x) - Real.pi * Real.log (η / η') * χ p) := by
    rw [hlogdiff, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  rw [hexp]
  calc _ ≤ ∑ p ∈ S, |(1 / 2 : ℝ) * (∫ x in A p, f x) - Real.pi * Real.log (η / η') * χ p| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) :=
        Finset.sum_le_sum hper
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hfinS]

end Whole

end SandierSerfaty

end
