/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.WeylMollifier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weyl's lemma for a locally integrable function on all of `ℂ` (uniform interior radius)

The mollification `mollify r u` is smooth, independent of the scale at points whose disk of radius
`r` lies in the harmonicity set (`Weyl.mollify_eq_mollify`), self-adjoint (`Weyl.integral_mollify_mul`)
and converges to the identity on test functions; so the distribution `u` coincides with the smooth
function `mollify r u` on the interior set `V`, and the latter is classically harmonic there
(`Weyl.exists_contDiff_ae_eq_of_isWeaklyHarmonicOn`).
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- **Self-adjointness of the mollification** (Fubini for the even kernel). -/
theorem integral_mollify_mul {δ : ℝ} (hδ : 0 < δ) {u ψ : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, mollify δ u x * ψ x = ∫ y, u y * mollify δ ψ y := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_rho hδ).exists_bound_of_continuous (contDiff_rho δ).continuous
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport ψ) from hψc).isBounded.subset_closedBall (0 : ℂ)
  have hbound : ∀ x y : ℂ, ‖u y * rho δ (y - x) * ψ x‖ ≤
      C * ‖ψ x‖ * (closedBall (0 : ℂ) (R + δ)).indicator (fun w => ‖u w‖) y := by
    intro x y
    by_cases hy : y ∈ closedBall (0 : ℂ) (R + δ)
    · rw [Set.indicator_of_mem hy, norm_mul, norm_mul]
      calc ‖u y‖ * ‖rho δ (y - x)‖ * ‖ψ x‖ ≤ ‖u y‖ * C * ‖ψ x‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hC (y - x)) (norm_nonneg _)) (norm_nonneg _)
        _ = C * ‖ψ x‖ * ‖u y‖ := by ring
    · rcases eq_or_ne (ψ x) 0 with hx0 | hx0
      · rw [Set.indicator_of_notMem hy, hx0]; simp
      · have hxR : ‖x‖ ≤ R := by
          have hmem := hR (subset_tsupport ψ hx0)
          rwa [mem_closedBall, dist_zero_right] at hmem
        have hyR : R + δ < ‖y‖ := by
          rwa [mem_closedBall, dist_zero_right, not_le] at hy
        have hd : δ ≤ ‖y - x‖ := by
          have := norm_sub_norm_le y x
          linarith
        rw [Set.indicator_of_notMem hy, rho_eq_zero hδ hd]
        simp
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y : ℂ => u y * rho δ (y - x) * ψ x)
      (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun z : ℂ × ℂ => u z.2) (volume.prod volume) :=
      hu.aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun z : ℂ × ℂ => rho δ (z.2 - z.1)) (volume.prod volume) :=
      ((contDiff_rho δ).continuous.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun z : ℂ × ℂ => ψ z.1) (volume.prod volume) :=
      (hψ.comp continuous_fst).aestronglyMeasurable
    exact (h1.mul h2).mul h3
  have hInt : Integrable (Function.uncurry fun x y : ℂ => u y * rho δ (y - x) * ψ x)
      (volume.prod volume) := by
    refine Integrable.mono' ?_ hmeas (Filter.Eventually.of_forall fun z => hbound z.1 z.2)
    exact Integrable.mul_prod ((hψ.integrable_of_hasCompactSupport hψc).norm.const_mul C)
      (IntegrableOn.integrable_indicator
        ((hu.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) (R + δ))).norm)
        measurableSet_closedBall)
  have hswap := integral_integral_swap (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) hInt
  have hpt1 : ∀ x : ℂ, mollify δ u x * ψ x = ∫ y, u y * rho δ (y - x) * ψ x := by
    intro x
    simp only [mollify]
    rw [integral_mul_const]
  have hpt2 : ∀ y : ℂ, (∫ x, u y * rho δ (y - x) * ψ x) = u y * mollify δ ψ y := by
    intro y
    simp only [mollify]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u y * rho δ (y - x) * ψ x = u y * (ψ x * rho δ (x - y))
    rw [rho_sub_comm δ y x]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1), hswap,
    integral_congr_ae (Filter.Eventually.of_forall hpt2)]

/-- **Concentration of the mollification.** -/
theorem abs_mollify_sub_le {δ : ℝ} (hδ : 0 < δ) {ψ : ℂ → ℝ} (hψ : Continuous ψ) {y : ℂ} {η : ℝ}
    (hosc : ∀ x ∈ closedBall y δ, |ψ x - ψ y| ≤ η) : |mollify δ ψ y - ψ y| ≤ η := by
  have hI1 := integrable_mul_rho_sub hδ hψ.locallyIntegrable y
  have hI2 : Integrable (fun x : ℂ => rho δ (x - y)) :=
    (integrable_rho hδ).comp_sub_right y
  have hrw : mollify δ ψ y - ψ y = ∫ x, (ψ x - ψ y) * rho δ (x - y) := by
    have : ∫ x, (ψ x - ψ y) * rho δ (x - y) =
        (∫ x, ψ x * rho δ (x - y)) - ψ y * ∫ x, rho δ (x - y) := by
      simp_rw [sub_mul]
      rw [integral_sub hI1 (hI2.const_mul _), integral_const_mul]
    rw [this, integral_rho_sub hδ y, mul_one]
    rfl
  rw [hrw]
  have hbd : ∀ x : ℂ, ‖(ψ x - ψ y) * rho δ (x - y)‖ ≤ η * rho δ (x - y) := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (rho_nonneg δ _)]
    by_cases hx : δ ≤ ‖x - y‖
    · rw [rho_eq_zero hδ hx]; simp
    · refine mul_le_mul_of_nonneg_right (hosc x ?_) (rho_nonneg δ _)
      rw [mem_closedBall, dist_eq_norm]; linarith [not_le.mp hx]
  have := norm_integral_le_of_norm_le (hI2.const_mul η) (Filter.Eventually.of_forall hbd)
  rw [integral_const_mul, integral_rho_sub hδ y, mul_one] at this
  simpa using this

/-- Outside a slight enlargement of its support the mollification vanishes. -/
theorem mollify_eq_zero_of_notMem {δ R : ℝ} (hδ : 0 < δ) {ψ : ℂ → ℝ}
    (hR : tsupport ψ ⊆ closedBall (0 : ℂ) R) {y : ℂ} (hy : y ∉ closedBall (0 : ℂ) (R + δ)) :
    mollify δ ψ y = 0 := by
  have hz : ∀ x : ℂ, ψ x * rho δ (x - y) = 0 := by
    intro x
    rcases eq_or_ne (ψ x) 0 with hx0 | hx0
    · rw [hx0, zero_mul]
    · have hxR : ‖x‖ ≤ R := by
        have hmem := hR (subset_tsupport ψ hx0)
        rwa [mem_closedBall, dist_zero_right] at hmem
      have hyR : R + δ < ‖y‖ := by
        rwa [mem_closedBall, dist_zero_right, not_le] at hy
      have hd : δ ≤ ‖x - y‖ := by
        rw [norm_sub_rev]
        have := norm_sub_norm_le y x
        linarith
      rw [rho_eq_zero hδ hd, mul_zero]
  simp only [mollify, hz]
  simp

theorem hasCompactSupport_mollify {δ R : ℝ} (hδ : 0 < δ) {ψ : ℂ → ℝ}
    (hR : tsupport ψ ⊆ closedBall (0 : ℂ) R) : HasCompactSupport (mollify δ ψ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + δ))
    fun _ hy => mollify_eq_zero_of_notMem hδ hR hy

private theorem eq_of_forall_pos_abs_sub_le {A B T : ℝ} (hT : 0 ≤ T)
    (h : ∀ η : ℝ, 0 < η → |A - B| ≤ η * T) : A = B := by
  by_contra hne
  have hpos : 0 < |A - B| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hη : 0 < |A - B| / (2 * (T + 1)) := by positivity
  have h2 := h _ hη
  have hlt : |A - B| / (2 * (T + 1)) * T < |A - B| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem continuous_lap {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (Δ f) := by
  have : Δ f = fun x => pd 1 (pd 1 f) x + pd Complex.I (pd Complex.I f) x :=
    funext fun x => lap_eq_pd hf.contDiffAt
  rw [this]
  have h1 : ∀ v : ℂ, Continuous (pd v (pd v f)) := fun v =>
    (contDiff_pd (m := 0) (contDiff_pd (m := 1) hf (by norm_num) v) (by norm_num) v).continuous
  exact (h1 1).add (h1 Complex.I)

/-- **Interior Weyl lemma, uniform radius.** If `u` is locally integrable and weakly harmonic on `U`,
and `V` is open with a closed disk of radius `r` around each of its points inside `U`, then `u`
agrees almost everywhere on `V` with a smooth function with vanishing Laplacian on `V`. -/
theorem exists_contDiff_ae_eq_of_isWeaklyHarmonicOn {U V : Set ℂ} (hV : IsOpen V) {r : ℝ}
    (hr : 0 < r) (hsub : ∀ x ∈ V, closedBall x r ⊆ U) {u : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hw : IsWeaklyHarmonicOn U u) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧ (∀ᵐ x ∂volume, x ∈ V → v x = u x) ∧ ∀ x ∈ V, Δ v x = 0 := by
  have hVU : V ⊆ U := fun x hx => hsub x hx (mem_closedBall_self hr.le)
  have hvsmooth : ContDiff ℝ ∞ (mollify r u) := contDiff_mollify hr hu
  have hvcont : Continuous (mollify r u) := hvsmooth.continuous
  have hvloc : LocallyIntegrable (mollify r u) volume := hvcont.locallyIntegrable
  have hconst : ∀ x ∈ V, ∀ δ : ℝ, 0 < δ → δ ≤ r → mollify δ u x = mollify r u x := by
    intro x hx δ hδ hδr
    refine mollify_eq_mollify hu hw hδ hr ?_
    rw [max_eq_right hδr]
    exact hsub x hx
  have hpair : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ x, ψ x • (u x - mollify r u x) = 0 := by
    intro ψ hψs hψc hψV
    have hψcont : Continuous ψ := hψs.continuous
    obtain ⟨R, hR⟩ := (show IsCompact (tsupport ψ) from hψc).isBounded.subset_closedBall (0 : ℂ)
    have huc : UniformContinuous ψ :=
      hψcont.uniformContinuous_of_tendsto_cocompact (HasCompactSupport.is_zero_at_infty hψc)
    have hTint : IntegrableOn (fun y : ℂ => ‖u y‖) (closedBall (0 : ℂ) (R + r)) volume :=
      (hu.integrableOn_isCompact (isCompact_closedBall (0 : ℂ) (R + r))).norm
    have hTnn : (0 : ℝ) ≤ ∫ y in closedBall (0 : ℂ) (R + r), ‖u y‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have hIψ : Integrable (fun y : ℂ => u y * ψ y) volume := by
      simpa using hu.integrable_smul_right_of_hasCompactSupport hψcont hψc
    have hIv : Integrable (fun y : ℂ => mollify r u y * ψ y) volume := by
      simpa using hvloc.integrable_smul_right_of_hasCompactSupport hψcont hψc
    have hmain : (∫ x, mollify r u x * ψ x) = ∫ y, u y * ψ y := by
      refine eq_of_forall_pos_abs_sub_le hTnn ?_
      intro η hη
      obtain ⟨ρ, hρ, hρψ⟩ := Metric.uniformContinuous_iff.mp huc η hη
      have hδ : (0 : ℝ) < min r (ρ / 2) := lt_min hr (by linarith)
      have hδr : min r (ρ / 2) ≤ r := min_le_left _ _
      have hδρ : min r (ρ / 2) < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hstep1 : (∫ x, mollify r u x * ψ x) = ∫ x, mollify (min r (ρ / 2)) u x * ψ x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show mollify r u x * ψ x = mollify (min r (ρ / 2)) u x * ψ x
        rcases eq_or_ne (ψ x) 0 with h0 | h0
        · rw [h0, mul_zero, mul_zero]
        · rw [hconst x (hψV (subset_tsupport ψ h0)) _ hδ hδr]
      have hstep2 := integral_mollify_mul hδ hu hψcont hψc
      have hΨc : Continuous (mollify (min r (ρ / 2)) ψ) :=
        (contDiff_mollify hδ hψcont.locallyIntegrable).continuous
      have hΨcs : HasCompactSupport (mollify (min r (ρ / 2)) ψ) :=
        hasCompactSupport_mollify hδ hR
      have hIΨ : Integrable (fun y : ℂ => u y * mollify (min r (ρ / 2)) ψ y) volume := by
        simpa using hu.integrable_smul_right_of_hasCompactSupport hΨc hΨcs
      have hdiff : (∫ y, u y * mollify (min r (ρ / 2)) ψ y) - ∫ y, u y * ψ y
          = ∫ y, u y * (mollify (min r (ρ / 2)) ψ y - ψ y) := by
        rw [← integral_sub hIΨ hIψ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
      have hbnd : ∀ y : ℂ, ‖u y * (mollify (min r (ρ / 2)) ψ y - ψ y)‖ ≤
          η * (closedBall (0 : ℂ) (R + r)).indicator (fun w => ‖u w‖) y := by
        intro y
        by_cases hy : y ∈ closedBall (0 : ℂ) (R + r)
        · rw [Set.indicator_of_mem hy, norm_mul]
          have hosc : ∀ x ∈ closedBall y (min r (ρ / 2)), |ψ x - ψ y| ≤ η := by
            intro x hx
            have hdist : dist x y < ρ := lt_of_le_of_lt (mem_closedBall.mp hx) hδρ
            have hlt := hρψ hdist
            rw [Real.dist_eq] at hlt
            exact hlt.le
          calc ‖u y‖ * ‖mollify (min r (ρ / 2)) ψ y - ψ y‖ ≤ ‖u y‖ * η :=
                mul_le_mul_of_nonneg_left
                  (by rw [Real.norm_eq_abs]; exact abs_mollify_sub_le hδ hψcont hosc)
                  (norm_nonneg _)
            _ = η * ‖u y‖ := by ring
        · have hy' : y ∉ closedBall (0 : ℂ) (R + min r (ρ / 2)) := fun hmem =>
            hy (closedBall_subset_closedBall (by linarith) hmem)
          have h1 : mollify (min r (ρ / 2)) ψ y = 0 := mollify_eq_zero_of_notMem hδ hR hy'
          have h2 : ψ y = 0 := by
            by_contra hne
            exact hy (closedBall_subset_closedBall (by linarith) (hR (subset_tsupport ψ hne)))
          rw [Set.indicator_of_notMem hy, h1, h2, sub_zero, mul_zero, norm_zero, mul_zero]
      have hbndInt : Integrable (fun y : ℂ =>
          η * (closedBall (0 : ℂ) (R + r)).indicator (fun w => ‖u w‖) y) volume :=
        (IntegrableOn.integrable_indicator hTint measurableSet_closedBall).const_mul η
      have hnorm := norm_integral_le_of_norm_le hbndInt (Filter.Eventually.of_forall hbnd)
      have hTeq : (∫ y, η * (closedBall (0 : ℂ) (R + r)).indicator (fun w => ‖u w‖) y)
          = η * ∫ y in closedBall (0 : ℂ) (R + r), ‖u y‖ := by
        rw [integral_const_mul, integral_indicator measurableSet_closedBall]
      calc |(∫ x, mollify r u x * ψ x) - ∫ y, u y * ψ y|
          = |∫ y, u y * (mollify (min r (ρ / 2)) ψ y - ψ y)| := by
            rw [hstep1, hstep2, hdiff]
        _ ≤ η * ∫ y in closedBall (0 : ℂ) (R + r), ‖u y‖ := by
            rw [← Real.norm_eq_abs]
            exact hnorm.trans (le_of_eq hTeq)
    have hsplit : ∫ x, ψ x • (u x - mollify r u x) =
        (∫ x, u x * ψ x) - ∫ x, mollify r u x * ψ x := by
      rw [← integral_sub hIψ hIv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    rw [hsplit, hmain]
    ring
  have hae : ∀ᵐ x ∂volume, x ∈ V → u x - mollify r u x = 0 :=
    IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hV
      ((hu.sub hvloc).locallyIntegrableOn V) hpair
  refine ⟨mollify r u, hvsmooth, ?_, ?_⟩
  · filter_upwards [hae] with x hx hxV
    have hx0 := hx hxV
    linarith
  · -- the Laplacian of the smooth representative vanishes on `V`
    have hv2 : ContDiff ℝ 2 (mollify r u) := hvsmooth.of_le (by norm_num)
    have hlap : ∀ᵐ x ∂volume, x ∈ V → Δ (mollify r u) x = 0 := by
      refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hV
        ((continuous_lap hv2).locallyIntegrable.locallyIntegrableOn V) ?_
      intro ψ hψs hψc hψV
      have hψ2 : ContDiff ℝ 2 ψ := hψs.of_le (by norm_num)
      have hK : IsCompact (tsupport ψ) := hψc
      have hg := integral_mul_lap_eq (u := mollify r u) (W := univ) hK (subset_univ _) isOpen_univ
        hv2.contDiffOn hψ2 (fun x hx => image_eq_zero_of_notMem_tsupport hx)
      have h1 : ∫ x, ψ x • Δ (mollify r u) x = ∫ x, mollify r u x * Δ ψ x := by
        rw [hg]; refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [smul_eq_mul]; ring
      rw [h1, ← setIntegral_mul_lap_eq_integral (mollify r u) (hψV)]
      have h2 : ∫ x in V, mollify r u x * Δ ψ x = ∫ x in V, u x * Δ ψ x := by
        refine setIntegral_congr_ae hV.measurableSet ?_
        filter_upwards [hae] with y hy hyV
        have h3 : mollify r u y = u y := by linarith [hy hyV]
        rw [h3]
      rw [h2, setIntegral_mul_lap_eq_integral u hψV, ← setIntegral_mul_lap_eq_integral u
        (hψV.trans hVU)]
      exact hw ψ hψs hψc (hψV.trans hVU)
    intro x hx
    have heq := Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℂ)) (U := V)
      (f := Δ (mollify r u)) (g := fun _ => 0)
      ((ae_restrict_iff' hV.measurableSet).2 hlap) hV (continuous_lap hv2).continuousOn
      continuousOn_const
    exact heq hx

end SandierSerfaty.Weyl

end
