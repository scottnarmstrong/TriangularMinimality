/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.LogWindow
public import SandierSerfaty.Sphere.InversionChange
public import SandierSerfaty.Sphere.Scaling

/-!
# Choice of the cut radius (sphere note, Lemma 6.9)

For `X ∈ ℂⁿ`, `n ≥ 1`, and `r ∈ [1,2]`, put (`s = s_n = κ √n`, `x̃ = ι x`)
`Λ(r) = ∑ᵢ [log₊ (1 / (2 s | |xᵢ| - r |)) + log₊ (1 / (2 s | |x̃ᵢ| - 1/r |))]` (`Lower.lambdaSum`).
`Lower.exists_cut_radius`: there is `r ∈ [1,2]` with `|xᵢ| ≠ r` for all `i` and `Λ(r) ≤ 20 √n / κ`.

Proof: `∫₁² Λ ≤ 9 n / s` (the first sum by `lintegral_logPlus_le`; the second sum is compared pointwise,
for `r ∈ [1,2]`, with the first sum at scale `s/8`, which replaces the substitution `u = 1/r` of the sphere note),
and Markov's inequality leaves a set of measure `≥ 1/2` of good radii; remove the finite set `{|xᵢ|}`.
-/

open MeasureTheory Set
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem blowupKappa_ge_two : 2 ≤ blowupKappa := by
  have hc := cSep_pos
  have hlog : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have hlog0 := Real.log_pos (one_lt_two (α := ℝ))
  have h1 : cSep ≤ 1 := by
    unfold cSep
    rw [Real.sqrt_le_one]
    linarith
  unfold blowupKappa
  rw [le_div_iff₀ hc]
  linarith

theorem two_le_blowupScale {n : ℕ} (hn : 0 < n) : 2 ≤ blowupScale n := by
  unfold blowupScale
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  nlinarith [blowupKappa_ge_two]

theorem negLog_antitone {s a b : ℝ} (hs : 0 < s) (hb : 0 < b) (hab : b ≤ a) :
    max (-Real.log (2 * s * a)) 0 ≤ max (-Real.log (2 * s * b)) 0 := by
  have : -Real.log (2 * s * a) ≤ -Real.log (2 * s * b) := by
    rw [neg_le_neg_iff]
    exact Real.log_le_log (by positivity) (by gcongr)
  exact max_le_max this le_rfl

/-- Pointwise comparison of the inverted-chart term with the plain term, for `r ∈ [1,2]` and `s ≥ 2`. -/
theorem logPlus_inv_le {s ρ r : ℝ} (hs : 2 ≤ s) (hρ : 0 ≤ ρ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    logPlus (1 / (2 * (s * |ρ⁻¹ - r⁻¹|))) ≤ logPlus (1 / (2 * ((s / 8) * |ρ - r|))) := by
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < r := by linarith
  rw [logPlus_eq (abs_nonneg _), logPlus_eq (abs_nonneg _)]
  by_cases hρ4 : ρ⁻¹ < 1 / 4
  · -- far case: the left side vanishes
    have h1 : 1 / 4 ≤ |ρ⁻¹ - r⁻¹| := by
      have : r⁻¹ ≥ 1 / 2 := by
        rw [ge_iff_le, ← one_div, div_le_div_iff₀ (by norm_num) hr0]; linarith
      rw [abs_sub_comm]
      calc (1 : ℝ) / 4 ≤ r⁻¹ - ρ⁻¹ := by linarith
        _ ≤ |r⁻¹ - ρ⁻¹| := le_abs_self _
    have h2 : 1 ≤ 2 * s * |ρ⁻¹ - r⁻¹| := by nlinarith
    have : -Real.log (2 * s * |ρ⁻¹ - r⁻¹|) ≤ 0 := by
      have := Real.log_nonneg h2
      linarith
    rw [max_eq_right this]
    exact le_max_right _ _
  · push Not at hρ4
    have hρpos : 0 < ρ := by
      by_contra h
      have : ρ = 0 := le_antisymm (not_lt.1 h) hρ
      rw [this] at hρ4; norm_num at hρ4
    have hρ4' : ρ ≤ 4 := by
      have := (inv_le_inv₀ (by norm_num : (0:ℝ) < 4) hρpos).1 (by simpa using hρ4)
      simpa using this
    have hdiff : |ρ⁻¹ - r⁻¹| = |ρ - r| / (ρ * r) := by
      rw [show ρ⁻¹ - r⁻¹ = (r - ρ) / (ρ * r) by field_simp, abs_div, abs_of_pos (mul_pos hρpos hr0),
        abs_sub_comm]
    by_cases hu : |ρ - r| = 0
    · have : |ρ⁻¹ - r⁻¹| = 0 := by rw [hdiff, hu]; simp
      rw [this, hu]
      simp
    · have hupos : 0 < |ρ - r| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hu)
      have hb : (|ρ - r| / 8) ≤ |ρ⁻¹ - r⁻¹| := by
        rw [hdiff, div_le_div_iff₀ (by norm_num) (by positivity)]
        have : ρ * r ≤ 8 := by nlinarith
        nlinarith [abs_nonneg (ρ - r)]
      have := negLog_antitone hs0 (by positivity : 0 < |ρ - r| / 8) hb
      calc max (-Real.log (2 * s * |ρ⁻¹ - r⁻¹|)) 0
          ≤ max (-Real.log (2 * s * (|ρ - r| / 8))) 0 := this
        _ = max (-Real.log (2 * (s / 8) * |ρ - r|)) 0 := by
          congr 3; ring


theorem measurable_logPlus : Measurable logPlus :=
  Real.measurable_log.max measurable_const

/-- `Λ(r)` of the sphere note's Definition 6.8 (as a function of the radius `r`). -/
@[expose] noncomputable def lambdaSum {n : ℕ} (X : Fin n → ℂ) (r : ℝ) : ℝ :=
  ∑ i, (logPlus (1 / (2 * (blowupScale n * |‖X i‖ - r|))) +
    logPlus (1 / (2 * (blowupScale n * |‖invC (X i)‖ - r⁻¹|))))

theorem measurable_lambdaSum {n : ℕ} (X : Fin n → ℂ) : Measurable (lambdaSum X) := by
  unfold lambdaSum
  refine Finset.measurable_sum _ fun i _ => Measurable.add ?_ ?_
  · exact measurable_logPlus.comp (by fun_prop)
  · exact measurable_logPlus.comp (by fun_prop)

theorem lintegral_lambdaSum_le {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) :
    ∫⁻ r in Icc (1 : ℝ) 2, ENNReal.ofReal (lambdaSum X r) ≤
      ENNReal.ofReal (9 * n / blowupScale n) := by
  set s := blowupScale n with hs
  have hs2 : 2 ≤ s := two_le_blowupScale hn
  have hs0 : 0 < s := by linarith
  have hmeas : ∀ (c : ℝ) (i : Fin n), Measurable fun r : ℝ =>
      ENNReal.ofReal (logPlus (1 / (2 * (c * |‖X i‖ - r|)))) := fun c i =>
    ENNReal.measurable_ofReal.comp (measurable_logPlus.comp (by fun_prop))
  have hpt : ∀ r ∈ Icc (1 : ℝ) 2, ENNReal.ofReal (lambdaSum X r) ≤
      ∑ i, (ENNReal.ofReal (logPlus (1 / (2 * (s * |‖X i‖ - r|)))) +
        ENNReal.ofReal (logPlus (1 / (2 * ((s / 8) * |‖X i‖ - r|))))) := by
    intro r hr
    unfold lambdaSum
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => add_nonneg (logPlus_nonneg _) (logPlus_nonneg _))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ENNReal.ofReal_add (logPlus_nonneg _) (logPlus_nonneg _)]
    gcongr
    rw [norm_invC]
    exact logPlus_inv_le hs2 (norm_nonneg _) hr.1 hr.2
  calc ∫⁻ r in Icc (1 : ℝ) 2, ENNReal.ofReal (lambdaSum X r)
      ≤ ∫⁻ r in Icc (1 : ℝ) 2, ∑ i, (ENNReal.ofReal (logPlus (1 / (2 * (s * |‖X i‖ - r|)))) +
        ENNReal.ofReal (logPlus (1 / (2 * ((s / 8) * |‖X i‖ - r|))))) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ∑ i, ((∫⁻ r in Icc (1 : ℝ) 2, ENNReal.ofReal (logPlus (1 / (2 * (s * |‖X i‖ - r|))))) +
        (∫⁻ r in Icc (1 : ℝ) 2, ENNReal.ofReal (logPlus (1 / (2 * ((s / 8) * |‖X i‖ - r|)))))) := by
        rw [lintegral_finsetSum _ (fun i _ => ((hmeas s i).add (hmeas (s / 8) i) :
          Measurable fun r : ℝ => _ + _))]
        refine Finset.sum_congr rfl fun i _ => lintegral_add_left (hmeas s i) _
    _ ≤ ∑ _i : Fin n, (ENNReal.ofReal (1 / s) + ENNReal.ofReal (1 / (s / 8))) := by
        refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
        · exact lintegral_logPlus_le hs0 _ _
        · exact lintegral_logPlus_le (by positivity) _ _
    _ = ENNReal.ofReal (9 * n / s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring


/-- **Lemma 6.9 (choice of the cut radius).** There is `r ∈ [1,2]` with `|xᵢ| ≠ r` for all `i` and
`Λ(r) ≤ 20 √n / κ`. -/
theorem exists_cut_radius {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) :
    ∃ r ∈ Icc (1 : ℝ) 2, (∀ i, ‖X i‖ ≠ r) ∧ lambdaSum X r ≤ 20 * Real.sqrt n / blowupKappa := by
  set s := blowupScale n with hs
  have hs2 : 2 ≤ s := two_le_blowupScale hn
  have hs0 : 0 < s := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set c : ℝ≥0∞ := ENNReal.ofReal (18 * n / s) with hc
  have hc0 : 0 < 18 * (n : ℝ) / s := by positivity
  have hmark := mul_meas_ge_le_lintegral₀ (μ := volume.restrict (Icc (1 : ℝ) 2))
    (f := fun r => ENNReal.ofReal (lambdaSum X r))
    ((ENNReal.measurable_ofReal.comp (measurable_lambdaSum X)).aemeasurable) c
  have hI := lintegral_lambdaSum_le hn X
  -- the measure of the bad set is at most 1/2
  have hbad : (volume.restrict (Icc (1 : ℝ) 2)) {r | c ≤ ENNReal.ofReal (lambdaSum X r)} ≤
      ENNReal.ofReal (1 / 2) := by
    have h1 : c * (volume.restrict (Icc (1 : ℝ) 2)) {r | c ≤ ENNReal.ofReal (lambdaSum X r)} ≤
        ENNReal.ofReal (9 * n / s) := hmark.trans hI
    have hcpos : c ≠ 0 := by simp [hc, hc0]
    have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : c * ENNReal.ofReal (1 / 2) = ENNReal.ofReal (9 * n / s) := by
      rw [hc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    exact (ENNReal.mul_le_mul_iff_right hcpos hctop).1 (h1.trans h2.symm.le)
  -- hence a good radius exists, avoiding the finitely many `‖X i‖`
  set F : Set ℝ := Set.range fun i => ‖X i‖ with hF
  have hFnull : (volume.restrict (Icc (1 : ℝ) 2)) F = 0 := by
    have h0 : volume F = 0 := (Set.finite_range _).measure_zero _
    exact le_antisymm ((Measure.restrict_apply_le _ _).trans h0.le) bot_le
  have hex : ∃ r ∈ Icc (1 : ℝ) 2, r ∉ F ∧ ENNReal.ofReal (lambdaSum X r) < c := by
    by_contra hno
    push Not at hno
    have hsub : Icc (1 : ℝ) 2 ⊆ {r | c ≤ ENNReal.ofReal (lambdaSum X r)} ∪ F := by
      intro r hr
      by_cases hrF : r ∈ F
      · exact Or.inr hrF
      · exact Or.inl (hno r hr hrF)
    have h3 := (measure_mono (μ := volume.restrict (Icc (1 : ℝ) 2)) hsub).trans
      (measure_union_le _ _)
    rw [hFnull, add_zero, Measure.restrict_apply_self, Real.volume_Icc] at h3
    have := h3.trans hbad
    norm_num at this
  obtain ⟨r, hr, hrF, hlt⟩ := hex
  refine ⟨r, hr, fun i hi => hrF ⟨i, hi⟩, ?_⟩
  have h4 : lambdaSum X r < 18 * n / s := by
    rwa [hc, ENNReal.ofReal_lt_ofReal_iff hc0] at hlt
  have h5 : 18 * (n : ℝ) / s = 18 * Real.sqrt n / blowupKappa := by
    rw [hs]; unfold blowupScale
    have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
    have hk := blowupKappa_pos
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnr.le
    field_simp
    nlinarith [hsq]
  rw [h5] at h4
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hk := blowupKappa_pos
  have : 18 * Real.sqrt n / blowupKappa ≤ 20 * Real.sqrt n / blowupKappa := by gcongr; norm_num
  linarith


end Lower

end Sphere

end SandierSerfaty

end
