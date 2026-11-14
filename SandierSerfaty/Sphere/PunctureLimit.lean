/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.PunctureLocal
public import SandierSerfaty.Analysis.PolarAnnulus

/-!
# The puncture limit exists (sphere note, Lemma 2.4)

For `H` admissible on `(G, P)` and `ε` as in `PunctureAdmissible.exists_good`, the function
`Q = |∇H|² - ∑_{p ∈ P} 1_{B(p, ε)} |· - p|⁻²` is integrable on `G`
(`Sphere.integrableOn_remainder`), and for radii `0 < ρ p < ε`
```
truncMulti G P H ρ = ½ ∫_{G ∖ ⋃ B(p, ρ p)} Q + π |P| log ε
```
(`Sphere.truncMulti_eq`). Dominated convergence gives
`Sphere.PunctureAdmissible.exists_tendsto_truncMulti`: there is `W` such that
`truncMulti G P H (ρ η) → W` along every family of radii with `ρ η p ↓ 0` for each `p ∈ P`
(independent radii at the different punctures). Taking `ρ η p = η` gives Lemma 2.4:
`Sphere.PunctureAdmissible.exists_tendsto_punctureTrunc`.
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

/-- The truncated energy with a separate radius at each puncture. -/
@[expose] noncomputable def truncMulti (G : Set ℂ) (P : Finset ℂ) (H : ℂ → ℝ) (ρ : ℂ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x in G \ ⋃ p ∈ P, ball p (ρ p), ‖gradient H x‖ ^ 2) +
    Real.pi * ∑ p ∈ P, Real.log (ρ p)

theorem punctureTrunc_eq_truncMulti (G : Set ℂ) (P : Finset ℂ) (H : ℂ → ℝ) (η : ℝ) :
    punctureTrunc G P H η = truncMulti G P H (fun _ => η) := by
  simp only [punctureTrunc, truncMulti, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A measurable function bounded by `C / ‖y - p‖` near `p` is integrable on the ball. -/
theorem integrableOn_ball_of_le_inv {f : ℂ → ℝ} {p : ℂ} {r C : ℝ} (hmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ y ∈ ball p r, y ≠ p → ‖f y‖ ≤ C / ‖y - p‖) :
    IntegrableOn f (ball p r) := by
  have hmp : MeasurePreserving (fun y : ℂ => p + y) volume volume :=
    measurePreserving_add_left volume p
  have hf : IntegrableOn (fun y => f (p + y)) (ball 0 r) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := C) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex]) ?_
      (hmeas.comp_measurePreserving hmp)
    filter_upwards [ae_restrict_of_ae ((Set.countable_singleton (0 : ℂ)).ae_notMem volume),
      ae_restrict_mem measurableSet_ball] with y hy0 hyb
    have hy0' : y ≠ 0 := hy0
    have hyb' : p + y ∈ ball p r := by simpa [mem_ball, dist_eq_norm] using hyb
    have := hbound (p + y) hyb' (by simpa using hy0')
    rw [Real.rpow_neg_one]
    simpa [div_eq_mul_inv] using this
  have hpre : (fun y : ℂ => p + y) ⁻¹' ball p r = ball 0 r := by
    ext y; simp [mem_ball, dist_eq_norm]
  exact (hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft p)
    (f := f) (s := ball p r)).1 (by rw [hpre]; exact hf)

/-- `∫_{B(p, b) ∖ B(p, a)} ‖x - p‖⁻² = 2π log (b / a)`. -/
theorem integral_inv_sq_annulus_center (p : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∫ x in ball p b \ ball p a, (‖x - p‖ ^ 2)⁻¹ = 2 * Real.pi * Real.log (b / a) := by
  have hpre : ball p b \ ball p a =
      (fun x : ℂ => x - p) ⁻¹' {x : ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b} := by
    ext x
    simp only [Set.mem_sdiff, mem_ball, dist_eq_norm, not_lt, mem_preimage, mem_ofPred_eq]
    tauto
  rw [hpre]
  have hmp : MeasurePreserving (fun x : ℂ => x - p) volume volume := measurePreserving_sub_right _ p
  have := hmp.setIntegral_preimage_emb (Homeomorph.subRight p).measurableEmbedding
    (fun y : ℂ => (‖y‖ ^ 2)⁻¹) {x : ℂ | a ≤ ‖x‖ ∧ ‖x‖ < b}
  rw [this]
  exact Torus.integral_inv_sq_annulus ha hab

/-- The remainder `Q = |∇H|² - ∑_p 1_{B(p, ε)} |· - p|⁻²`. -/
@[expose] noncomputable def remainder (P : Finset ℂ) (ε : ℝ) (H : ℂ → ℝ) (x : ℂ) : ℝ :=
  ‖gradient H x‖ ^ 2 - ∑ p ∈ P, (ball p ε).indicator (fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) x

theorem measurable_indicator_term (p : ℂ) (ε : ℝ) :
    Measurable ((ball p ε).indicator fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) :=
  (((measurable_norm.comp (measurable_id.sub_const p)).pow_const 2).inv).indicator measurableSet_ball

theorem aestronglyMeasurable_remainder (P : Finset ℂ) (ε : ℝ) (H : ℂ → ℝ) :
    AEStronglyMeasurable (remainder P ε H) volume := by
  unfold remainder
  refine AEStronglyMeasurable.sub ((aestronglyMeasurable_gradient H).norm.pow 2) ?_
  exact (Finset.measurable_sum P fun p _ => measurable_indicator_term p ε).aestronglyMeasurable

theorem remainder_eq_of_notMem {P : Finset ℂ} {ε : ℝ} {H : ℂ → ℝ} {x : ℂ}
    (hx : x ∉ ⋃ p ∈ P, ball p ε) : remainder P ε H x = ‖gradient H x‖ ^ 2 := by
  unfold remainder
  rw [Finset.sum_eq_zero fun p hp => ?_, sub_zero]
  exact indicator_of_notMem (fun h => hx (mem_biUnion hp h)) _

theorem remainder_eq_of_mem {P : Finset ℂ} {ε : ℝ} {H : ℂ → ℝ} {p x : ℂ} (hp : p ∈ P)
    (hdisj : ∀ q ∈ P, p ≠ q → 2 * ε ≤ ‖p - q‖) (hx : x ∈ ball p ε) :
    remainder P ε H x = ‖gradient H x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹ := by
  unfold remainder
  rw [Finset.sum_eq_single p (fun q hq hqp => ?_) (fun h => absurd hp h), indicator_of_mem hx]
  refine indicator_of_notMem (fun hxq => ?_) _
  have h1 := hdisj q hq (Ne.symm hqp)
  have h2 : ‖p - q‖ ≤ ‖p - x‖ + ‖x - q‖ := by
    simpa using norm_add_le (p - x) (x - q)
  rw [mem_ball, dist_eq_norm] at hx hxq
  rw [norm_sub_rev] at hx
  linarith

theorem integrableOn_remainder {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hsub : ∀ p ∈ P, ball p ε ⊆ G) (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * ε ≤ ‖p - q‖)
    (hbd : ∀ p ∈ P, ∀ x ∈ ball p ε, x ≠ p →
      |‖gradient H x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹| ≤ C + C / ‖x - p‖) :
    IntegrableOn (remainder P ε H) G := by
  have hU : (⋃ p ∈ P, ball p ε) ⊆ G := iUnion₂_subset hsub
  rw [← sdiff_union_of_subset hU]
  refine IntegrableOn.union ?_ ?_
  · refine (hH.finite_energy ε hε).congr_fun (fun x hx => (remainder_eq_of_notMem hx.2).symm) ?_
    exact hH.isOpen.measurableSet.diff (Finset.measurableSet_biUnion _ fun p _ => measurableSet_ball)
  · rw [integrableOn_finset_iUnion]
    intro p hp
    refine integrableOn_ball_of_le_inv (C := C * ε + C) (aestronglyMeasurable_remainder P ε H)
      fun y hy hyp => ?_
    have hyn : 0 < ‖y - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hyp)
    have hyε : ‖y - p‖ < ε := by simpa [mem_ball, dist_eq_norm] using hy
    rw [remainder_eq_of_mem hp (hdisj p hp) hy, Real.norm_eq_abs]
    refine (hbd p hp y hy hyp).trans ?_
    rw [add_div]
    have : C ≤ C * ε / ‖y - p‖ := by rw [le_div_iff₀ hyn]; nlinarith
    linarith

theorem measurableSet_diff_biUnion {G : Set ℂ} (hG : IsOpen G) (P : Finset ℂ) (ρ : ℂ → ℝ) :
    MeasurableSet (G \ ⋃ p ∈ P, ball p (ρ p)) :=
  hG.measurableSet.diff (Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball)

/-- The terms `1_{B(p, ε)} |· - p|⁻²` are integrable away from the punctures. -/
theorem integrableOn_indicator_term {G : Set ℂ} (hG : IsOpen G) {P : Finset ℂ} {ε : ℝ}
    {ρ : ℂ → ℝ} (hρ : ∀ p ∈ P, 0 < ρ p) {p : ℂ} (hp : p ∈ P) :
    IntegrableOn ((ball p ε).indicator fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) (G \ ⋃ q ∈ P, ball q (ρ q)) := by
  have hSm : MeasurableSet (G \ ⋃ q ∈ P, ball q (ρ q)) := measurableSet_diff_biUnion hG P ρ
  have hg : Integrable ((ball p ε).indicator fun _ : ℂ => (ρ p ^ 2)⁻¹)
      (volume.restrict (G \ ⋃ q ∈ P, ball q (ρ q))) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((integrableOn_const (μ := volume) (s := ball p ε) measure_ball_lt_top.ne (by simp)).mono_measure
        Measure.restrict_le_self)
  refine hg.mono' ((measurable_indicator_term p ε).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem hSm fun x hx => ?_
  by_cases hxb : x ∈ ball p ε
  · rw [indicator_of_mem hxb, indicator_of_mem hxb, Real.norm_eq_abs]
    have hxp : ρ p ≤ ‖x - p‖ := by
      have := fun h => hx.2 (mem_biUnion hp h)
      by_contra hlt
      exact this (by rw [mem_ball, dist_eq_norm]; linarith)
    have hρp := hρ p hp
    rw [abs_of_nonneg (by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hρp.le hxp 2)
  · rw [indicator_of_notMem hxb, indicator_of_notMem hxb]; simp

/-- The exact value of the multi-radius truncated energy in terms of `Q`. -/
theorem truncMulti_eq {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hsub : ∀ p ∈ P, ball p ε ⊆ G) (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * ε ≤ ‖p - q‖)
    (hbd : ∀ p ∈ P, ∀ x ∈ ball p ε, x ≠ p →
      |‖gradient H x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹| ≤ C + C / ‖x - p‖)
    {ρ : ℂ → ℝ} (hρ : ∀ p ∈ P, 0 < ρ p ∧ ρ p < ε) :
    truncMulti G P H ρ =
      (1 / 2 : ℝ) * (∫ x in G \ ⋃ p ∈ P, ball p (ρ p), remainder P ε H x) +
        Real.pi * ∑ _p ∈ P, Real.log ε := by
  set S := G \ ⋃ p ∈ P, ball p (ρ p) with hS
  have hSm : MeasurableSet S := measurableSet_diff_biUnion hH.isOpen P ρ
  have hQ : IntegrableOn (remainder P ε H) S :=
    (integrableOn_remainder hH hε hC hsub hdisj hbd).mono_set sdiff_subset
  -- the terms `1_{B(p, ε)} |· - p|⁻²` on `S`
  have hind : ∀ p ∈ P, IntegrableOn ((ball p ε).indicator fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) S :=
    fun p hp => integrableOn_indicator_term hH.isOpen (fun q hq => (hρ q hq).1) hp
  have hint : ∀ p ∈ P, ∫ x in S, (ball p ε).indicator (fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) x =
      2 * Real.pi * Real.log (ε / ρ p) := by
    intro p hp
    rw [setIntegral_indicator measurableSet_ball]
    have hSeq : S ∩ ball p ε = ball p ε \ ball p (ρ p) := by
      ext x
      simp only [hS, mem_inter_iff, Set.mem_sdiff, mem_iUnion, exists_prop, not_exists, not_and]
      constructor
      · rintro ⟨⟨-, hx⟩, hxb⟩
        exact ⟨hxb, hx p hp⟩
      · rintro ⟨hxb, hxp⟩
        refine ⟨⟨hsub p hp hxb, fun q hq hxq => ?_⟩, hxb⟩
        by_cases hqp : q = p
        · exact hxp (hqp ▸ hxq)
        · have h1 := hdisj p hp q hq (Ne.symm hqp)
          have h2 : ‖p - q‖ ≤ ‖p - x‖ + ‖x - q‖ := by simpa using norm_add_le (p - x) (x - q)
          have h3 := (hρ q hq).2
          rw [mem_ball, dist_eq_norm] at hxb hxq
          rw [norm_sub_rev] at hxb
          linarith
    rw [hSeq]
    exact integral_inv_sq_annulus_center p (hρ p hp).1 (hρ p hp).2
  have hpt : ∀ x ∈ S, ‖gradient H x‖ ^ 2 = remainder P ε H x +
      ∑ p ∈ P, (ball p ε).indicator (fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) x := by
    intro x _; unfold remainder; ring
  rw [truncMulti, setIntegral_congr_fun hSm hpt, integral_add hQ (integrable_finsetSum _ hind),
    integral_finsetSum _ hind, Finset.sum_congr rfl hint]
  have : ∀ p ∈ P, Real.log (ε / ρ p) = Real.log ε - Real.log (ρ p) := fun p hp =>
    Real.log_div hε.ne' (hρ p hp).1.ne'
  rw [Finset.sum_congr rfl fun p hp => by rw [this p hp], ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- Radii tending to `0⁺` at each puncture. -/
@[expose] def RadiiToZero (P : Finset ℂ) (ρ : ℝ → ℂ → ℝ) : Prop :=
  ∀ p ∈ P, Tendsto (fun η => ρ η p) (𝓝[>] 0) (𝓝[>] 0)

theorem RadiiToZero.eventually_lt {P : Finset ℂ} {ρ : ℝ → ℂ → ℝ} (h : RadiiToZero P ρ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ p ∈ P, 0 < ρ η p ∧ ρ η p < ε := by
  rw [Filter.eventually_all_finset]
  intro p hp
  have h1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ρ η p ∈ Ioo 0 ε := (h p hp).eventually (Ioo_mem_nhdsGT hε)
  exact h1

/-- **Lemma 2.4 (multi-radius form).** For `H` admissible on `(G, P)` there is a real `W` such that
the truncated energies converge to `W` along every family of radii with `ρ η p ↓ 0` at each
`p ∈ P`. -/
theorem PunctureAdmissible.exists_tendsto_truncMulti {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) :
    ∃ W : ℝ, ∀ ρ : ℝ → ℂ → ℝ, RadiiToZero P ρ →
      Tendsto (fun η => truncMulti G P H (ρ η)) (𝓝[>] 0) (𝓝 W) := by
  obtain ⟨ε, C, hε, hC, hsub, hdisj, hbd⟩ := hH.exists_good
  have hQ := integrableOn_remainder hH hε hC hsub hdisj hbd
  refine ⟨(1 / 2 : ℝ) * (∫ x in G, remainder P ε H x) + Real.pi * ∑ _p ∈ P, Real.log ε,
    fun ρ hρ => ?_⟩
  have hlim : Tendsto (fun η => ∫ x in G \ ⋃ p ∈ P, ball p (ρ η p), remainder P ε H x) (𝓝[>] 0)
      (𝓝 (∫ x in G, remainder P ε H x)) := by
    have e : ∀ η, (∫ x in G \ ⋃ p ∈ P, ball p (ρ η p), remainder P ε H x) =
        ∫ x, (G \ ⋃ p ∈ P, ball p (ρ η p)).indicator (remainder P ε H) x :=
      fun η => (integral_indicator (measurableSet_diff_biUnion hH.isOpen P (ρ η))).symm
    have eG : (∫ x in G, remainder P ε H x) = ∫ x, G.indicator (remainder P ε H) x :=
      (integral_indicator hH.isOpen.measurableSet).symm
    simp only [e, eG]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖G.indicator (remainder P ε H) x‖) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun η =>
        (aestronglyMeasurable_remainder P ε H).indicator (measurableSet_diff_biUnion hH.isOpen P (ρ η))
    · refine Filter.Eventually.of_forall fun η => Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ G \ ⋃ p ∈ P, ball p (ρ η p)
      · rw [indicator_of_mem hx, indicator_of_mem hx.1]
      · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
    · exact ((integrable_indicator_iff hH.isOpen.measurableSet).2 hQ).norm
    · filter_upwards [P.finite_toSet.countable.ae_notMem volume] with x hx
      by_cases hxG : x ∈ G
      · have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), x ∈ G \ ⋃ p ∈ P, ball p (ρ η p) := by
          have : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ p ∈ P, ρ η p < ‖x - p‖ := by
            rw [Filter.eventually_all_finset]
            intro p hp
            have hpos : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hx (h ▸ hp))
            exact (hρ p hp).eventually (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hpos))
          filter_upwards [this] with η hη
          refine ⟨hxG, fun hmem => ?_⟩
          obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hmem
          rw [mem_ball, dist_eq_norm] at hxp
          exact absurd (hη p hp) (not_lt.2 hxp.le)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with η hη
        rw [indicator_of_mem hη, indicator_of_mem hxG]
      · have : ∀ η : ℝ, x ∉ G \ ⋃ p ∈ P, ball p (ρ η p) := fun η h => hxG h.1
        simp only [this, indicator_of_notMem, hxG, not_false_eq_true]
        exact tendsto_const_nhds
  have := (hlim.const_mul (1 / 2 : ℝ)).add_const (Real.pi * ∑ _p ∈ P, Real.log ε)
  refine this.congr' ?_
  filter_upwards [hρ.eventually_lt hε] with η hη
  rw [truncMulti_eq hH hε hC hsub hdisj hbd hη]

/-- **Lemma 2.4.** For admissible `H` the limit defining the puncture energy exists. -/
theorem PunctureAdmissible.exists_tendsto_punctureTrunc {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) :
    ∃ W : ℝ, Tendsto (punctureTrunc G P H) (𝓝[>] 0) (𝓝 W) := by
  obtain ⟨W, hW⟩ := hH.exists_tendsto_truncMulti
  refine ⟨W, ?_⟩
  have := hW (fun η _ => η) (fun p _ => tendsto_id)
  have e : punctureTrunc G P H = fun η => truncMulti G P H (fun _ => η) :=
    funext (punctureTrunc_eq_truncMulti G P H)
  rw [e]
  exact this

theorem PunctureAdmissible.tendsto_punctureEnergy {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) :
    Tendsto (punctureTrunc G P H) (𝓝[>] 0) (𝓝 (punctureEnergy G P H)) := by
  obtain ⟨W, hW⟩ := hH.exists_tendsto_punctureTrunc
  rw [punctureEnergy, hW.limUnder_eq]
  exact hW

/-- For admissible `H`, `|∇H|²` is integrable away from the punctures, with arbitrary positive radii. -/
theorem PunctureAdmissible.integrableOn_gradSq_multi {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) {ρ : ℂ → ℝ} (hρ : ∀ p ∈ P, 0 < ρ p) :
    IntegrableOn (fun x => ‖gradient H x‖ ^ 2) (G \ ⋃ p ∈ P, ball p (ρ p)) := by
  obtain ⟨ε, C, hε, hC, hsub, hdisj, hbd⟩ := hH.exists_good
  set ρ' : ℂ → ℝ := fun p => min (ρ p) (ε / 2) with hρ'
  have hρ'pos : ∀ p ∈ P, 0 < ρ' p := fun p hp => lt_min (hρ p hp) (by positivity)
  set S := G \ ⋃ p ∈ P, ball p (ρ' p) with hS
  have hQ : IntegrableOn (remainder P ε H) S :=
    (integrableOn_remainder hH hε hC hsub hdisj hbd).mono_set sdiff_subset
  have hind : ∀ p ∈ P, IntegrableOn ((ball p ε).indicator fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) S :=
    fun p hp => integrableOn_indicator_term hH.isOpen hρ'pos hp
  have hSm : MeasurableSet S := measurableSet_diff_biUnion hH.isOpen P ρ'
  have hsum := hQ.add (integrable_finsetSum P hind)
  have : IntegrableOn (fun x => ‖gradient H x‖ ^ 2) S := by
    refine hsum.congr_fun (fun x _ => ?_) hSm
    simp only [remainder, Pi.add_apply]
    ring
  refine this.mono_set ?_
  intro x ⟨hxG, hx⟩
  refine ⟨hxG, fun hmem => hx ?_⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hmem
  exact mem_biUnion hp (ball_subset_ball (min_le_left _ _) hxp)

end Sphere

end SandierSerfaty

end
