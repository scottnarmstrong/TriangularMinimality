/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.DiscrepancyAux
public import SandierSerfaty.Sphere.Lower.TruncPotential

/-!
# The discrepancy lemma (sphere note, Lemma 6.7)

For the blown-up potential `H` with `1`-separated points `z_i = s_n x_i` and a square `Q = a₀ + [0,t]²`, `t ≥ 2`
(`Lower.exists_discrepancy`):
`|p - ∫_Q m| ≤ C ((1 + m₊) t + √t (∫_{Q^{1/2} ∖ Q¹} |∇H_{1/4}|²)^{1/2})`, `p = #{i | z_i ∈ Q}`.

The sphere note's flux identity through `∂Q^s` (a divergence theorem on a square) is replaced by testing the distributional
equation of `H_{1/4}` against the smooth cutoff `χ` of `Lower.exists_cutoff` (`χ = 1` on `Q¹`, `supp χ ⊆ Q^{1/2}`).
-/

open MeasureTheory Set Filter Topology Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem blowupDens_nonneg (n : ℕ) (x : ℂ) : 0 ≤ blowupDens n x := by
  rw [blowupDens_eq_dN]; exact div_nonneg mPlus_pos.le (by have := dN_pos (blowupScale n) x; positivity)

theorem blowupDens_le (n : ℕ) (x : ℂ) : blowupDens n x ≤ mPlus := by
  rw [blowupDens_eq_dN]
  have h1 := one_le_dN (blowupScale n) x
  rw [div_le_iff₀ (by positivity)]
  have h2 : 1 ≤ dN (blowupScale n) x ^ 2 := one_le_pow₀ h1
  linarith [mul_nonneg mPlus_pos.le (sub_nonneg.2 h2)]

theorem measurable_blowupDens (n : ℕ) : Measurable (blowupDens n) := (contDiff_blowupDens n).continuous.measurable

/-- One of the per-point comparisons: `|1_{z ∈ Q} - ⨍_{∂B(z,1/4)} χ| ≤ 1_{z ∈ Q ∖ Q^{5/4}}`. -/
theorem abs_ind_sub_circleAverage_le {a₀ : ℂ} {t : ℝ} {χ : ℂ → ℝ} (hχc : Continuous χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hsupp : tsupport χ ⊆ interior (sqShrink a₀ t (1 / 2)))
    (h1 : ∀ x ∈ sqShrink a₀ t 1, χ x = 1) (z : ℂ) :
    |(if z ∈ sqAt a₀ t then (1 : ℝ) else 0) - Real.circleAverage χ z (1 / 4)| ≤
      if z ∈ sqAt a₀ t \ sqShrink a₀ t (5 / 4) then 1 else 0 := by
  classical
  have hsph : ∀ w ∈ Metric.sphere z |(1 / 4 : ℝ)|, |w.re - z.re| ≤ 1 / 4 ∧ |w.im - z.im| ≤ 1 / 4 := by
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hw
    have e1 : w.re - z.re = (w - z).re := by simp
    have e2 : w.im - z.im = (w - z).im := by simp
    rw [e1, e2]
    exact ⟨(Complex.abs_re_le_norm _).trans hw.le, (Complex.abs_im_le_norm _).trans hw.le⟩
  by_cases hin : z ∈ sqShrink a₀ t (5 / 4)
  · have hQ : z ∈ sqAt a₀ t := sqShrink_subset_sqAt a₀ t (by norm_num) hin
    have hca : Real.circleAverage χ z (1 / 4) = 1 := by
      refine Real.circleAverage_const_on_circle fun w hw => h1 w ?_
      obtain ⟨hr, hi⟩ := hsph w hw
      rw [abs_le] at hr hi
      rw [mem_sqShrink] at hin ⊢
      obtain ⟨c1, c2, c3, c4⟩ := hin
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hA : ¬ (z ∈ sqAt a₀ t \ sqShrink a₀ t (5 / 4)) := fun h => h.2 hin
    simp only [hQ, hA, hca, ↓reduceIte]
    simp
  · by_cases hQ : z ∈ sqAt a₀ t
    · have hca0 : 0 ≤ Real.circleAverage χ z (1 / 4) :=
        Real.circleAverage_nonneg_of_nonneg fun w _ => (h01 w).1
      have hca1 : Real.circleAverage χ z (1 / 4) ≤ 1 :=
        Real.circleAverage_mono_on_of_le_circle
          (ContinuousOn.circleIntegrable' hχc.continuousOn) fun w _ => (h01 w).2
      have hA : z ∈ sqAt a₀ t \ sqShrink a₀ t (5 / 4) := ⟨hQ, hin⟩
      simp only [hQ, hA, ↓reduceIte]
      rw [abs_le]
      constructor <;> linarith
    · have hca : Real.circleAverage χ z (1 / 4) = 0 := by
        refine Real.circleAverage_const_on_circle fun w hw => ?_
        by_contra hne
        have hw' : w ∈ sqShrink a₀ t (1 / 2) :=
          interior_subset (hsupp (subset_tsupport _ (Function.mem_support.2 hne)))
        obtain ⟨hr, hi⟩ := hsph w hw
        rw [abs_le] at hr hi
        rw [mem_sqShrink] at hw'
        apply hQ
        rw [mem_sqAt]
        obtain ⟨c1, c2, c3, c4⟩ := hw'
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      have hA : ¬ (z ∈ sqAt a₀ t \ sqShrink a₀ t (5 / 4)) := fun h => hQ h.1
      simp only [hQ, hA, hca, ↓reduceIte]
      simp

/-- `|p - ∑ᵢ ⨍_{∂B(zᵢ,1/4)} χ| ≤ 12 t`. -/
theorem abs_card_sub_sum_circleAverage_le {n : ℕ} (X : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {a₀ : ℂ} {t : ℝ} (ht : 2 ≤ t)
    {χ : ℂ → ℝ} (hχc : Continuous χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : tsupport χ ⊆ interior (sqShrink a₀ t (1 / 2))) (h1 : ∀ x ∈ sqShrink a₀ t 1, χ x = 1) :
    |((Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt a₀ t).card : ℝ) -
        ∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)| ≤ 12 * t := by
  classical
  set z : Fin n → ℂ := fun i => blowupScale n • X i with hz
  have hinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have := hsep i j hne
    simp only [hz] at hij
    rw [hij, sub_self, norm_zero] at this
    linarith
  have hcard : ((Finset.univ.filter fun i => z i ∈ sqAt a₀ t).card : ℝ) =
      ∑ i, (if z i ∈ sqAt a₀ t then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
  rw [hcard, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ i, |(if z i ∈ sqAt a₀ t then (1 : ℝ) else 0) - Real.circleAverage χ (z i) (1 / 4)| ≤
      if z i ∈ sqAt a₀ t \ sqShrink a₀ t (5 / 4) then 1 else 0 :=
    fun i => abs_ind_sub_circleAverage_le hχc h01 hsupp h1 (z i)
  refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
  rw [Finset.sum_boole]
  -- count the points in the boundary layer
  set A := sqAt a₀ t \ sqShrink a₀ t (5 / 4)
  set S : Finset ℂ := Finset.univ.image z
  have hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖ := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    exact hsep i j (fun h => hpq (by rw [h]))
  have hc : (Finset.univ.filter fun i => z i ∈ A).card = (S.filter (· ∈ A)).card := by
    rw [← Finset.card_image_of_injective _ hinj]
    congr 1
    ext p
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hi⟩; exact ⟨i, hi, rfl⟩
  rw [hc]
  have h2 := card_filter_mul_le_volume hS A
  have h3 := h2.trans (volume_boundary_nbhd a₀ ht)
  have h4 : ((S.filter (· ∈ A)).card : ℝ) * (Real.pi / 4) ≤ 9 * t := by
    have h5 : ENNReal.ofReal (((S.filter (· ∈ A)).card : ℝ) * (Real.pi / 4)) ≤ ENNReal.ofReal (9 * t) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      convert h3
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h5
  have hpi := Real.pi_gt_three
  have hc0 : (0 : ℝ) ≤ (S.filter (· ∈ A)).card := Nat.cast_nonneg _
  nlinarith

theorem measurable_blowupDens_mul {n : ℕ} {χ : ℂ → ℝ} (hχc : Continuous χ) :
    Measurable fun x => blowupDens n x * χ x := (measurable_blowupDens n).mul hχc.measurable

theorem notMem_sqAt_of_supp {a₀ : ℂ} {t : ℝ} {χ : ℂ → ℝ}
    (hsupp : tsupport χ ⊆ interior (sqShrink a₀ t (1 / 2))) {x : ℂ} (hx : x ∉ sqAt a₀ t) : χ x = 0 := by
  by_contra hne
  exact hx (sqShrink_subset_sqAt a₀ t (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (interior_subset (hsupp (subset_tsupport _ (Function.mem_support.2 hne)))))

/-- `|∫_Q m - ∫ m χ| ≤ 4 m₊ t`. -/
theorem abs_integral_sqAt_sub_le {n : ℕ} {a₀ : ℂ} {t : ℝ} (ht : 2 ≤ t) {χ : ℂ → ℝ} (hχc : Continuous χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hsupp : tsupport χ ⊆ interior (sqShrink a₀ t (1 / 2)))
    (h1 : ∀ x ∈ sqShrink a₀ t 1, χ x = 1) :
    |(∫ x in sqAt a₀ t, blowupDens n x) - ∫ x, blowupDens n x * χ x| ≤ 4 * mPlus * t := by
  have hm := measurable_blowupDens n
  have hQ := measurableSet_sqAt a₀ t
  have hmχ : ∀ x, 0 ≤ blowupDens n x * χ x ∧ blowupDens n x * χ x ≤ mPlus := by
    intro x
    have a1 := blowupDens_le n x
    have a2 := blowupDens_nonneg n x
    have a3 := h01 x
    exact ⟨mul_nonneg a2 a3.1, by linarith [mul_le_mul a1 a3.2 a3.1 mPlus_pos.le]⟩
  have hI1 : IntegrableOn (blowupDens n) (sqAt a₀ t) :=
    integrableOn_sqAt hm (blowupDens_nonneg n) (blowupDens_le n) a₀ t
  have hI2 : IntegrableOn (fun x => blowupDens n x * χ x) (sqAt a₀ t) :=
    integrableOn_sqAt (measurable_blowupDens_mul hχc) (fun x => (hmχ x).1) (fun x => (hmχ x).2) a₀ t
  have hout : ∀ x, x ∉ sqAt a₀ t → blowupDens n x * χ x = 0 := fun x hx => by
    rw [notMem_sqAt_of_supp hsupp hx, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, ← integral_sub hI1 hI2]
  have hf : ∀ x, blowupDens n x - blowupDens n x * χ x = blowupDens n x * (1 - χ x) := fun x => by ring
  simp only [hf]
  have hfnn : ∀ x, 0 ≤ blowupDens n x * (1 - χ x) := fun x =>
    mul_nonneg (blowupDens_nonneg n x) (by linarith [(h01 x).2])
  have hfle : ∀ x, blowupDens n x * (1 - χ x) ≤ mPlus := fun x => by
    have a1 := blowupDens_le n x
    have a2 := blowupDens_nonneg n x
    have a3 := h01 x
    linarith [mul_le_mul a1 (show 1 - χ x ≤ 1 by linarith [a3.1]) (by linarith [a3.2]) mPlus_pos.le]
  have hfm : Measurable fun x => blowupDens n x * (1 - χ x) :=
    hm.mul (measurable_const.sub hχc.measurable)
  rw [abs_of_nonneg (setIntegral_nonneg hQ fun x _ => hfnn x)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ (Set.sdiff_subset (t := sqShrink a₀ t 1))]
  · have hfin : volume (sqAt a₀ t \ sqShrink a₀ t 1) ≠ ⊤ :=
      ne_top_of_le_ne_top (volume_sqAt_ne_top a₀ t) (measure_mono Set.sdiff_subset)
    have hint : IntegrableOn (fun x => blowupDens n x * (1 - χ x)) (sqAt a₀ t \ sqShrink a₀ t 1) :=
      Measure.integrableOn_of_bounded (M := mPlus) hfin hfm.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hfnn x)]; exact hfle x)
    have := setIntegral_mono_on (μ := volume) (s := sqAt a₀ t \ sqShrink a₀ t 1) hint
      (integrableOn_const hfin (C := mPlus)) (hQ.diff (measurableSet_sqShrink _ _ _)) (fun x _ => hfle x)
    rw [setIntegral_const, smul_eq_mul] at this
    have h4 := volume_real_layer' a₀ ht
    calc _ ≤ volume.real (sqAt a₀ t \ sqShrink a₀ t 1) * mPlus := this
      _ ≤ 4 * t * mPlus := by gcongr; exact mPlus_pos.le
      _ = 4 * mPlus * t := by ring
  · intro x hx
    have hx1 : x ∈ sqShrink a₀ t 1 := by
      by_contra h; exact hx.2 ⟨hx.1, h⟩
    simp only [h1 x hx1]; ring

theorem abs_fderiv_apply_le {u : ℂ → ℝ} (x : ℂ) {v : ℂ} (hv : v = 1 ∨ v = Complex.I) :
    |fderiv ℝ u x v| ≤ ‖gradC u x‖ := by
  rcases hv with rfl | rfl
  · rw [← gradC_re]; exact Complex.abs_re_le_norm _
  · rw [← gradC_im]; exact Complex.abs_im_le_norm _

theorem measurableSet_layer (a₀ : ℂ) (t : ℝ) :
    MeasurableSet (sqShrink a₀ t (1 / 2) \ sqShrink a₀ t 1) :=
  (measurableSet_sqShrink _ _ _).diff (measurableSet_sqShrink _ _ _)

theorem volume_layer_ne_top (a₀ : ℂ) (t : ℝ) :
    volume (sqShrink a₀ t (1 / 2) \ sqShrink a₀ t 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_sqAt_ne_top _ _) (measure_mono Set.sdiff_subset)

/-- **Lemma 6.7 (discrepancy).**  For an absolute constant `C`, the number `p` of points `z_i = s_n x_i` (`1`-separated)
in a square `Q = a₀ + [0,t]²`, `t ≥ 2`, satisfies
`|p - ∫_Q m| ≤ C ((1 + m₊) t + √t (∫_{Q^{1/2} ∖ Q¹} |∇H_{1/4}|²)^{1/2})`, `H_{1/4} = truncPot X (1/4)`. -/
theorem exists_discrepancy : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (_ : 0 < n) (X : Fin n → ℂ),
    (∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) → ∀ (a₀ : ℂ) {t : ℝ}, 2 ≤ t →
    |((Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt a₀ t).card : ℝ) -
        ∫ x in sqAt a₀ t, blowupDens n x| ≤
      C * ((1 + mPlus) * t + Real.sqrt t *
        Real.sqrt (∫ x in sqShrink a₀ t (1 / 2) \ sqShrink a₀ t 1, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2)) := by
  obtain ⟨C₀, hC₀, hχ⟩ := exists_cutoff
  refine ⟨12 + 2 * C₀, by positivity, ?_⟩
  intro n hn X hsep a₀ t ht
  obtain ⟨χ, hχs, hχc, h01, hsupp, h1, hder, hlip⟩ := hχ a₀ t
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  -- the weak equation of `H_{1/4}` tested against `χ`
  have hlap := integral_truncPot_mul_lap hn X hχs hχc hη
  have hibp := integral_truncPot_mul_lap_eq X hχs hχc hη
  set H := truncPot X (1 / 4) with hH
  set g := gradC H with hg
  set L := sqShrink a₀ t (1 / 2) \ sqShrink a₀ t 1 with hL
  have hLm : MeasurableSet L := measurableSet_layer a₀ t
  have hχcont : Continuous χ := hχs.continuous
  -- `g ∈ L²(L)`
  have hQc : IsCompact (sqShrink a₀ t (1 / 2)) := isCompact_sqAt _ _
  have hgQ : MemLp g 2 (volume.restrict (sqShrink a₀ t (1 / 2))) :=
    (hasWeakGradientOn_of_locallyLipschitz (locallyLipschitz_truncPot X hη) hQc).2.1
  have : IsFiniteMeasure (volume.restrict L) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (volume_layer_ne_top a₀ t)⟩
  have hgL : MemLp g 2 (volume.restrict L) :=
    hgQ.mono_measure (Measure.restrict_mono Set.sdiff_subset le_rfl)
  have hgn : MemLp (fun x => ‖g x‖) 2 (volume.restrict L) := hgL.norm
  have hgint : Integrable (fun x => ‖g x‖) (volume.restrict L) := hgn.integrable (by norm_num)
  -- the integrands `∂_v H ∂_v χ`
  have hzero : ∀ x, x ∉ L → ∀ v : ℂ, fderiv ℝ H x v * fderiv ℝ χ x v = 0 := by
    intro x hx v
    have : fderiv ℝ χ x = 0 := by
      by_contra hne; exact hx (hder x hne)
    rw [this]; simp
  have hbd : ∀ x, ∀ v : ℂ, (v = 1 ∨ v = Complex.I) → ‖fderiv ℝ H x v * fderiv ℝ χ x v‖ ≤ C₀ * ‖g x‖ := by
    intro x v hv
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have a1 := abs_fderiv_apply_le (u := H) x hv
    have a2 := hlip x v
    have hv1 : ‖v‖ = 1 := by rcases hv with rfl | rfl <;> simp
    rw [hv1, mul_one] at a2
    calc |fderiv ℝ H x v| * |fderiv ℝ χ x v| ≤ ‖g x‖ * C₀ := mul_le_mul a1 a2 (abs_nonneg _) (norm_nonneg _)
      _ = C₀ * ‖g x‖ := by ring
  have hmeasA : ∀ v : ℂ, Measurable fun x => fderiv ℝ H x v * fderiv ℝ χ x v := fun v =>
    (measurable_fderiv_apply_const ℝ H v).mul (measurable_fderiv_apply_const ℝ χ v)
  have hAint : ∀ v : ℂ, (v = 1 ∨ v = Complex.I) →
      Integrable (fun x => fderiv ℝ H x v * fderiv ℝ χ x v) := by
    intro v hv
    have hAL : IntegrableOn (fun x => fderiv ℝ H x v * fderiv ℝ χ x v) L :=
      Integrable.mono' (hgint.const_mul C₀) (hmeasA v).aestronglyMeasurable
        ((ae_restrict_iff' hLm).2 (Eventually.of_forall fun x _ => hbd x v hv))
    refine (integrableOn_iff_integrable_of_support_subset (s := L) ?_).1 hAL
    intro x hx
    by_contra hxL
    exact hx (hzero x hxL v)
  have hAbd : ∀ v : ℂ, (v = 1 ∨ v = Complex.I) →
      |∫ x, fderiv ℝ H x v * fderiv ℝ χ x v| ≤ C₀ * ∫ x in L, ‖g x‖ := by
    intro v hv
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := L) (fun x hx => hzero x hx v),
      ← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hgint.const_mul C₀)
      ((ae_restrict_iff' hLm).2 (Eventually.of_forall fun x _ => hbd x v hv))
  -- Cauchy–Schwarz on the layer
  have hCS := integral_le_sqrt_mul_sqrt (μ := volume.restrict L) (g := fun x => ‖g x‖)
    (fun x => norm_nonneg _) hgn
  have hvolL : (volume.restrict L).real univ ≤ 2 * t := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact volume_real_layer a₀ ht
  have hsq : Real.sqrt ((volume.restrict L).real univ) ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt hvolL
  set G := ∫ x in L, ‖g x‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hLm fun x _ => by positivity
  have hsl : ∫ x in L, ‖g x‖ ≤ Real.sqrt (2 * t) * Real.sqrt G := by
    refine hCS.trans ?_
    gcongr
  -- the flux identity
  have hflux : 2 * Real.pi * ((∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)) -
      ∫ x, blowupDens n x * χ x) = (∫ x, fderiv ℝ H x 1 * fderiv ℝ χ x 1) +
        ∫ x, fderiv ℝ H x Complex.I * fderiv ℝ χ x Complex.I := by
    linarith
  have hflux_bd : |(∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)) -
      ∫ x, blowupDens n x * χ x| ≤ C₀ * (Real.sqrt 2 * (Real.sqrt t * Real.sqrt G)) := by
    have hpi := Real.pi_pos
    have h2 : |2 * Real.pi * ((∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)) -
        ∫ x, blowupDens n x * χ x)| ≤ 2 * (C₀ * (Real.sqrt (2 * t) * Real.sqrt G)) := by
      rw [hflux]
      refine (abs_add_le _ _).trans ?_
      have a1 := hAbd 1 (Or.inl rfl)
      have a2 := hAbd Complex.I (Or.inr rfl)
      have : C₀ * ∫ x in L, ‖g x‖ ≤ C₀ * (Real.sqrt (2 * t) * Real.sqrt G) := by gcongr
      linarith
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h2
    have h3 : 2 * Real.pi * |(∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)) -
        ∫ x, blowupDens n x * χ x| ≤ 2 * (C₀ * (Real.sqrt 2 * (Real.sqrt t * Real.sqrt G))) := by
      rw [Real.sqrt_mul (by norm_num)] at h2
      linarith
    have hs2 : Real.sqrt 2 ≤ Real.pi := by
      have : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      linarith [Real.pi_gt_three]
    have hnn : 0 ≤ C₀ * (Real.sqrt 2 * (Real.sqrt t * Real.sqrt G)) := by positivity
    -- `2π |·| ≤ 2 · (C₀ √2 …)` hence `|·| ≤ (√2/π) …`
    have h4 : |(∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)) -
        ∫ x, blowupDens n x * χ x| ≤ (C₀ * (Real.sqrt 2 * (Real.sqrt t * Real.sqrt G))) / Real.pi := by
      rw [le_div_iff₀ hpi]; linarith
    exact h4.trans (div_le_self hnn (by linarith [Real.pi_gt_three]))
  have hcount := abs_card_sub_sum_circleAverage_le X hsep ht hχcont h01 hsupp h1
  have hmass := abs_integral_sqAt_sub_le (n := n) ht hχcont h01 hsupp h1
  -- assemble
  set p : ℝ := ((Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt a₀ t).card : ℝ)
  set S := ∑ i, Real.circleAverage χ (blowupScale n • X i) (1 / 4)
  set M := ∫ x, blowupDens n x * χ x
  set MQ := ∫ x in sqAt a₀ t, blowupDens n x
  have htri : |p - MQ| ≤ |p - S| + |S - M| + |MQ - M| := by
    have : p - MQ = (p - S) + (S - M) - (MQ - M) := by ring
    rw [this]
    calc _ ≤ |(p - S) + (S - M)| + |MQ - M| := abs_sub _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  have hs0 : 0 ≤ Real.sqrt t * Real.sqrt G := by positivity
  have ht0 : 0 ≤ t := by linarith
  have hmp := mPlus_pos
  have hs2' : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hflux2 : |S - M| ≤ C₀ * (2 * (Real.sqrt t * Real.sqrt G)) := by
    refine hflux_bd.trans ?_
    have hq : 0 ≤ C₀ * (Real.sqrt t * Real.sqrt G) := by positivity
    linarith [mul_le_mul_of_nonneg_left hs2' hq]
  calc |p - MQ| ≤ 12 * t + C₀ * (2 * (Real.sqrt t * Real.sqrt G)) + 4 * mPlus * t := by
        linarith
    _ ≤ _ := by linarith [mul_nonneg hC₀ hs0, mul_nonneg ht0 hmp.le, mul_nonneg hC₀ ht0,
          mul_nonneg (mul_nonneg hC₀ ht0) hmp.le]

end Lower

end Sphere

end SandierSerfaty

end
