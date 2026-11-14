/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.Periodic
public import SandierSerfaty.Dual.PolarInt
public import SandierSerfaty.Torus.PairEnergyIdentity

/-!
# The renormalized sector integral

For the sector `S = voronoiSector P p q` with site `p`, angle `θ = α + β`, define
`sectorRenInt η = ∫_{S ∩ {‖z - p‖ > η}} |∇H|²` (`H = gluedH`). Then
`sectorRenInt η + θ log η` converges as `η ↓ 0` (`tendsto_sectorRenInt`), which is the finiteness of
`(dual:sector-ren)` (paper `dual:sector-ren`): `|∇H|² - ‖z - p‖⁻²` is bounded
on `S` (`abs_gradSq_sub_inv_sq_le`), and the integral of `‖z - p‖⁻²` over the annular part of the
sector is exactly `θ log (η/η')` (`integral_inv_sq_voronoiSector_annulus`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis

variable {ι : Type*} {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ} {p q z : ℂ}

theorem gradSq_eq_norm_fderiv_sq (u : ℂ → ℝ) (x : ℂ) : gradSq u x = ‖fderiv ℝ u x‖ ^ 2 := by
  rw [← Torus.norm_gradient_eq, norm_gradient_sq]; rfl

theorem exists_deriv_B_bound (hR : R.IsAdmissible d₀) (R₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc 0 R₁, |deriv R.B r + 1 / r| ≤ C * r := by
  obtain ⟨C₁, ρ, hρ, hCρ⟩ := hR.origin
  have hC₁ : 0 ≤ C₁ := by
    have := (hCρ (ρ / 2) ⟨by positivity, by linarith⟩).2
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [abs_nonneg (deriv R.B (ρ / 2) + 1 / (ρ / 2)), mul_pos (neg_pos.2 hneg) (by positivity : 0 < ρ / 2)]
  have hcont : ContinuousOn (fun r => deriv R.B r + 1 / r) (Icc ρ R₁) := by
    have h1 := hR.contDiffOn_B.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
    refine (h1.mono fun r hr => lt_of_lt_of_le hρ hr.1).add ?_
    exact continuousOn_const.div continuousOn_id fun r hr => (lt_of_lt_of_le hρ hr.1).ne'
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc.exists_bound_of_continuousOn hcont)
  refine ⟨max C₁ (max 0 C₂ / ρ), le_max_of_le_left hC₁, fun r hr => ?_⟩
  by_cases hrρ : r < ρ
  · exact ((hCρ r ⟨hr.1, hrρ⟩).2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr.1.le)
  · rw [not_lt] at hrρ
    have h1 := hC₂ r ⟨hrρ, hr.2⟩
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc C₂ ≤ max 0 C₂ := le_max_right _ _
      _ = (max 0 C₂ / ρ) * ρ := by field_simp
      _ ≤ (max 0 C₂ / ρ) * r := mul_le_mul_of_nonneg_left hrρ (by positivity)
      _ ≤ max C₁ (max 0 C₂ / ρ) * r :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hr.1.le

theorem eventuallyEq_gluedH_Hsec (hS : SepSites P d₀) (h : IsVoronoiNeighbor P p q)
    (hz : z ∈ voronoiSector P p q) : gluedH R P =ᶠ[𝓝 z] Hsec R p q := by
  filter_upwards [(isOpen_voronoiSector h).mem_nhds hz] with y hy
  exact gluedH_eq_Hsec hS h hy

/-- **`|∇H|² = ‖z - p‖⁻² + O(1)` on a sector**, uniformly in the sector. -/
theorem abs_gradSq_sub_inv_sq_le (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) :
    ∃ Cb : ℝ, ∀ p q, IsVoronoiNeighbor P p q → ∀ z ∈ voronoiSector P p q,
      |gradSq (gluedH R P) z - (‖z - p‖ ^ 2)⁻¹| ≤ Cb := by
  obtain ⟨R₁, T₀, M, hR₁, hT, hdT, hM⟩ := exists_bnd hR hS
  obtain ⟨CB, hCB0, hCB⟩ := exists_deriv_B_bound hR R₁
  have hd := hS.pos
  set Ks : ℝ := (2 + 1 / d₀) * (max 1 (Real.toNNReal (1 / d₀)) : NNReal) with hKs
  have hKs0 : 0 ≤ Ks := by positivity
  set SM : ℝ := ∑' i, M i with hSM
  have hSM0 : 0 ≤ SM := tsum_nonneg fun i => hM.nonneg hd hdT.le i
  set C₄ : ℝ := CB + Ks * (R₁ ^ 4 / d₀ ^ 5) * SM with hC₄
  refine ⟨2 * C₄ + C₄ ^ 2 * R₁ ^ 2, fun p q h z hz => ?_⟩
  have hzp := ne_of_mem_voronoiSector h hz
  set r := ‖z - p‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzp)
  have hrR : r ≤ R₁ := by
    have := hR₁ p h.1 (voronoiSector_subset_voronoiCell hS.isVoronoiSiteSet h hz)
    rw [mem_closedBall, dist_eq_norm] at this; exact this
  have hR₁0 : 0 ≤ R₁ := hr0.le.trans hrR
  have hC₄0 : 0 ≤ C₄ := by positivity
  -- the derivative
  have hfd : fderiv ℝ (gluedH R P) z = fderiv ℝ (Hsec R p q) z :=
    (eventuallyEq_gluedH_Hsec hS h hz).fderiv_eq
  rw [gradSq_eq_norm_fderiv_sq, hfd]
  set A := fderiv ℝ (Hsec R p q) z with hA
  set v := innerSL ℝ ((1 / r ^ 2 : ℝ) • (z - p)) with hv
  have hvn : ‖v‖ = 1 / r := by
    rw [hv, innerSL_apply_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), ← hr]
    field_simp
  have he := norm_fderiv_Hsec_add_le hR hS h hR₁ hT hM hz
  rw [← hA, ← hv] at he
  set e := ‖A + v‖ with he_def
  have he1 : e ≤ C₄ * r := by
    refine he.trans ?_
    have h1 := hCB r ⟨hr0, hrR⟩
    have h2 : Ks * ((r / d₀) ^ 5 * SM) ≤ Ks * (R₁ ^ 4 / d₀ ^ 5) * SM * r := by
      have : (r / d₀) ^ 5 = r * (r ^ 4 / d₀ ^ 5) := by rw [div_pow]; ring
      have h3 : r ^ 4 ≤ R₁ ^ 4 := pow_le_pow_left₀ hr0.le hrR 4
      rw [this]
      have : r * (r ^ 4 / d₀ ^ 5) ≤ r * (R₁ ^ 4 / d₀ ^ 5) := by gcongr
      linarith [mul_le_mul_of_nonneg_left this (mul_nonneg hKs0 hSM0)]
    have h4 : (2 + 1 / d₀) * (max 1 (Real.toNNReal (1 / d₀)) : NNReal) * ((r / d₀) ^ 5 * SM)
        = Ks * ((r / d₀) ^ 5 * SM) := by rw [hKs]
    rw [h4]
    calc _ ≤ CB * r + Ks * (R₁ ^ 4 / d₀ ^ 5) * SM * r := add_le_add h1 h2
      _ = C₄ * r := by rw [hC₄]; ring
  have habs : |‖A‖ - ‖v‖| ≤ e := by
    have := abs_norm_sub_norm_le A (-v)
    rw [norm_neg, sub_neg_eq_add] at this
    exact this
  have hA_le : ‖A‖ ≤ ‖v‖ + e := by
    have := le_of_abs_le habs
    linarith [(abs_le.1 habs).2]
  have he0 : 0 ≤ e := norm_nonneg _
  have hb : ‖v‖ ^ 2 = (r ^ 2)⁻¹ := by rw [hvn]; field_simp
  rw [← hb]
  have key : |‖A‖ ^ 2 - ‖v‖ ^ 2| ≤ e * (2 * ‖v‖ + e) := by
    have : ‖A‖ ^ 2 - ‖v‖ ^ 2 = (‖A‖ - ‖v‖) * (‖A‖ + ‖v‖) := by ring
    rw [this, abs_mul]
    have h5 : |‖A‖ + ‖v‖| = ‖A‖ + ‖v‖ := abs_of_nonneg (by positivity)
    rw [h5]
    exact mul_le_mul habs (by linarith) (by positivity) he0
  refine key.trans ?_
  have h6 : e * (2 * ‖v‖ + e) = 2 * (e * ‖v‖) + e ^ 2 := by ring
  rw [h6]
  have h7 : e * ‖v‖ ≤ C₄ := by
    rw [hvn]
    calc e * (1 / r) ≤ (C₄ * r) * (1 / r) := by gcongr
      _ = C₄ := by field_simp
  have h8 : e ^ 2 ≤ C₄ ^ 2 * R₁ ^ 2 := by
    calc e ^ 2 ≤ (C₄ * r) ^ 2 := pow_le_pow_left₀ he0 he1 2
      _ = C₄ ^ 2 * r ^ 2 := by ring
      _ ≤ C₄ ^ 2 * R₁ ^ 2 := by gcongr
  linarith

theorem tendsto_setIntegral_inter_norm_gt {S : Set ℂ} (hS : MeasurableSet S) {f : ℂ → ℝ}
    (hf : IntegrableOn f S) (c : ℂ) (hSc : c ∉ S) :
    Tendsto (fun η : ℝ => ∫ z in S ∩ {z | η < ‖z - c‖}, f z) (𝓝[>] 0) (𝓝 (∫ z in S, f z)) := by
  have hmeas : ∀ η : ℝ, MeasurableSet {z : ℂ | η < ‖z - c‖} := fun η =>
    measurableSet_lt measurable_const (by fun_prop)
  have : ∀ η : ℝ, ∫ z in S ∩ {z | η < ‖z - c‖}, f z =
      ∫ z in S, {z : ℂ | η < ‖z - c‖}.indicator f z := fun η =>
    (setIntegral_indicator (hmeas η)).symm
  simp_rw [this]
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖f z‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun η => (hf.1.indicator (hmeas η))
  · exact Eventually.of_forall fun η => Eventually.of_forall fun z => by
      by_cases hz : z ∈ {z : ℂ | η < ‖z - c‖}
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz]; simp
  · filter_upwards [ae_restrict_mem hS] with z hz
    have hzc : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hSc (h ▸ hz))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hzc] with η hη
    rw [indicator_of_mem (show z ∈ {z : ℂ | η < ‖z - c‖} from hη.2)]

theorem voronoiSector_inter_annulus (h : IsVoronoiNeighbor P p q) {η' η : ℝ}
    (hη : η < pairHalfDist p q) :
    voronoiSector P p q ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η} =
      (fun ζ => p + pairAxis p q * ζ) ''
        {ζ : ℂ | ζ ≠ 0 ∧ -sectorAlpha P p q < Complex.arg ζ ∧ Complex.arg ζ < sectorBeta P p q ∧
          η' < ‖ζ‖ ∧ ‖ζ‖ ≤ η} := by
  have hu := norm_pairAxis h.ne
  have hpolar := modelSector_eq_polar (d := pairHalfDist p q) (abs_sectorAlpha_lt P p q)
    (abs_sectorBeta_lt P p q)
  ext z
  constructor
  · rintro ⟨⟨ζ, hζ, rfl⟩, hz⟩
    have hn : ‖p + pairAxis p q * ζ - p‖ = ‖ζ‖ := by rw [add_sub_cancel_left, norm_mul, hu, one_mul]
    rw [mem_ofPred_eq, hn] at hz
    have := hζ
    rw [hpolar] at this
    exact ⟨ζ, ⟨this.1, this.2.1, this.2.2.1, hz.1, hz.2⟩, rfl⟩
  · rintro ⟨ζ, ⟨h0, h1, h2, h3, h4⟩, rfl⟩
    have hn : ‖p + pairAxis p q * ζ - p‖ = ‖ζ‖ := by rw [add_sub_cancel_left, norm_mul, hu, one_mul]
    refine ⟨⟨ζ, ?_, rfl⟩, ?_⟩
    · rw [hpolar]
      refine ⟨h0, h1, h2, ?_⟩
      have : ‖ζ‖ * Real.cos (Complex.arg ζ) ≤ ‖ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one _) (norm_nonneg _)
      linarith
    · rw [mem_ofPred_eq, hn]; exact ⟨h3, h4⟩

theorem integral_inv_sq_voronoiSector_annulus (h : IsVoronoiNeighbor P p q) (hS : IsVoronoiSiteSet P)
    {η' η : ℝ} (h0 : 0 < η') (h1 : η' ≤ η) (hη : η < pairHalfDist p q) :
    ∫ z in voronoiSector P p q ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η}, (‖z - p‖ ^ 2)⁻¹ =
      (sectorAlpha P p q + sectorBeta P p q) * Real.log (η / η') := by
  have hu := norm_pairAxis h.ne
  rw [voronoiSector_inter_annulus h hη, integral_comp_affine_image hu p]
  have : ∀ ζ : ℂ, (‖p + pairAxis p q * ζ - p‖ ^ 2)⁻¹ = (‖ζ‖ ^ 2)⁻¹ := fun ζ => by
    rw [add_sub_cancel_left, norm_mul, hu, one_mul]
  simp_rw [this]
  have hα := abs_lt.1 (abs_sectorAlpha_lt P p q)
  have hβ := abs_lt.1 (abs_sectorBeta_lt P p q)
  have hpos := sectorAlpha_add_sectorBeta_pos hS h
  have := integral_inv_sq_arg_annulus (a := -sectorAlpha P p q) (b := sectorBeta P p q) (η' := η')
    (η := η) (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h0 h1
  rw [this]; ring

theorem pairHalfDist_ge (hS : SepSites P d₀) (h : IsVoronoiNeighbor P p q) :
    d₀ ≤ pairHalfDist p q := by
  have := hS.sep p h.1 q h.2.1 h.ne
  unfold pairHalfDist
  rw [norm_sub_rev]; linarith

/-- **Finiteness of the renormalized sector integral** (`(dual:sector-ren)`):
`∫_{S ∩ {r > η}} |∇H|² + θ(S) log η` has a limit as `η ↓ 0`. -/
theorem tendsto_sectorRenInt (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) :
    ∃ L : ℝ, Tendsto (fun η : ℝ =>
      (∫ z in voronoiSector P p q ∩ {z | η < ‖z - p‖}, gradSq (gluedH R P) z) +
        (sectorAlpha P p q + sectorBeta P p q) * Real.log η) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨R₁, T₀, M, hR₁, hT, hdT, hM⟩ := exists_bnd hR hS
  obtain ⟨Cb, hCb⟩ := abs_gradSq_sub_inv_sq_le hR hS
  set Sx := voronoiSector P p q with hSx
  set d := pairHalfDist p q with hd
  set θ := sectorAlpha P p q + sectorBeta P p q with hθ
  have hdd : d₀ ≤ d := pairHalfDist_ge hS h
  have hSm : MeasurableSet Sx := measurableSet_voronoiSector h
  have hSsub : Sx ⊆ closedBall p R₁ := fun z hz =>
    hR₁ p h.1 (voronoiSector_subset_voronoiCell hS.isVoronoiSiteSet h hz)
  have hSfin : volume Sx < ⊤ := (measure_mono hSsub).trans_lt measure_closedBall_lt_top
  have hpS : p ∉ Sx := fun hp => ne_of_mem_voronoiSector h hp rfl
  set f : ℂ → ℝ := fun z => gradSq (gluedH R P) z - (‖z - p‖ ^ 2)⁻¹ with hf
  have hfm : Measurable f := (Torus.measurable_gradSq _).sub (by fun_prop)
  have hfint : IntegrableOn f Sx := by
    refine Measure.integrableOn_of_bounded hSfin.ne hfm.aestronglyMeasurable (M := Cb) ?_
    filter_upwards [ae_restrict_mem hSm] with z hz
    rw [Real.norm_eq_abs]; exact hCb p q h z hz
  -- the radial part
  set Q : ℝ → ℝ := fun η => ∫ z in Sx ∩ {z | η < ‖z - p‖}, (‖z - p‖ ^ 2)⁻¹ with hQ
  have hQint : ∀ η > 0, IntegrableOn (fun z : ℂ => (‖z - p‖ ^ 2)⁻¹) (Sx ∩ {z | η < ‖z - p‖}) := by
    intro η hη
    refine Measure.integrableOn_of_bounded ((measure_mono inter_subset_left).trans_lt hSfin).ne
      (by fun_prop : Measurable fun z : ℂ => (‖z - p‖ ^ 2)⁻¹).aestronglyMeasurable ?_ (M := (η ^ 2)⁻¹)
    refine (ae_restrict_iff' (hSm.inter (measurableSet_lt measurable_const (by fun_prop)))).2
      (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : η ^ 2 ≤ ‖z - p‖ ^ 2 := pow_le_pow_left₀ hη.le hz.2.le 2
    exact inv_anti₀ (by positivity) this
  have hQdiff : ∀ η' η : ℝ, 0 < η' → η' ≤ η → η < d →
      Q η' + θ * Real.log η' = Q η + θ * Real.log η := by
    intro η' η h0 h1 hη
    have hunion : Sx ∩ {z | η' < ‖z - p‖} =
        (Sx ∩ {z | η < ‖z - p‖}) ∪ (Sx ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η}) := by
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨hz, hz'⟩
        by_cases hzη : η < ‖z - p‖
        · exact Or.inl ⟨hz, hzη⟩
        · exact Or.inr ⟨hz, hz', not_lt.1 hzη⟩
      · rintro (⟨hz, hz'⟩ | ⟨hz, hz', -⟩)
        · exact ⟨hz, lt_of_le_of_lt h1 hz'⟩
        · exact ⟨hz, hz'⟩
    have hdisj : Disjoint (Sx ∩ {z | η < ‖z - p‖}) (Sx ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η}) := by
      refine Set.disjoint_left.2 fun z hz1 hz2 => ?_
      exact absurd hz2.2.2 (not_le.2 hz1.2)
    have hnm : Measurable fun z : ℂ => ‖z - p‖ := by fun_prop
    have hm2 : MeasurableSet (Sx ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η}) :=
      hSm.inter ((measurableSet_lt measurable_const hnm).inter
        (measurableSet_le hnm measurable_const))
    have hint2 : IntegrableOn (fun z : ℂ => (‖z - p‖ ^ 2)⁻¹)
        (Sx ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η}) :=
      (hQint η' h0).mono_set (fun z hz => ⟨hz.1, hz.2.1⟩)
    have hQ' : Q η' = Q η + ∫ z in Sx ∩ {z | η' < ‖z - p‖ ∧ ‖z - p‖ ≤ η}, (‖z - p‖ ^ 2)⁻¹ := by
      simp only [hQ]
      rw [hunion, setIntegral_union hdisj hm2 (hQint η (h0.trans_le h1)) hint2]
    have hann := integral_inv_sq_voronoiSector_annulus h hS.isVoronoiSiteSet h0 h1 hη
    rw [hQ', hann, Real.log_div (by linarith) h0.ne', hθ]
    ring
  -- constancy of Q + θ log on (0, d)
  set c₀ : ℝ := Q (d / 2) + θ * Real.log (d / 2) with hc₀
  have hdpos : 0 < d := lt_of_lt_of_le hS.pos hdd
  have hconst : ∀ η, 0 < η → η < d → Q η + θ * Real.log η = c₀ := by
    intro η h0 hη
    rcases le_total η (d / 2) with hle | hle
    · exact hQdiff η (d / 2) h0 hle (by linarith)
    · exact (hQdiff (d / 2) η (by positivity) hle hη).symm
  -- limit
  refine ⟨(∫ z in Sx, f z) + c₀, ?_⟩
  have hlim := tendsto_setIntegral_inter_norm_gt hSm hfint p hpS
  have hlim' := hlim.add_const c₀
  refine hlim'.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hdpos] with η hη
  have hsplit : ∫ z in Sx ∩ {z | η < ‖z - p‖}, gradSq (gluedH R P) z =
      (∫ z in Sx ∩ {z | η < ‖z - p‖}, f z) + Q η := by
    rw [← integral_add (hfint.mono_set inter_subset_left) (hQint η hη.1)]
    refine setIntegral_congr_fun₀ ?_ fun z _ => by simp [hf]
    exact (hSm.inter (measurableSet_lt measurable_const (by fun_prop))).nullMeasurableSet
  rw [hsplit]
  have := hconst η hη.1 hη.2
  linarith

end Dual

end SandierSerfaty

end
