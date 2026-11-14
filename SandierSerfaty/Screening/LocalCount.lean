/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.RadialFields
public import SandierSerfaty.Screening.Mollify
public import SandierSerfaty.Screening.TruncFieldWeak
public import SandierSerfaty.Screening.EnergyExpansion

/-!
# Local charge counts (the counting step of the screening note's Lemmas 3.7 and 4.12)

The screening note, Lemma 2.7 (`lem:localcount`) in the form used by the
ring estimates of Lemma 4.12 (`lem:ring`). Let `E` be a charge field on an open set `U` with density
`m ≥ 0` and charges `C`, and `Φ = E_{1/4}` (all of `C` truncated at `¼`). For `x` with
`B̄(x, 3/2) ⊆ U`, testing the Lipschitz pairing I1 against the cutoff
`φ_x(y) = min(1, max(0, 3/2 - |y - x|))` (`ballCutoff`) bounds the number of charges within `¼` of
`x`:

* `card_le_of_ballCutoff`: `#P ≤ (9π/4) m + (2π)⁻¹ ∫_{B̄(x, 3/2)} |Φ|` for every finite `P ⊆ C`
  inside `B(x, ¼)`;
* `ofReal_card_sq_le`: the squared form `#P² ≤ 2((9π/4) m)² + (9/8π) ∫_{B̄(x, 3/2)} |Φ|²`.

Integrated against `x` with Tonelli (`lintegral_setLIntegral_closedBall_le`:
`∫_S ∫_{B̄(x, r)} f ≤ |B̄(0, r)| ∫ f`), the squared form replaces the grid counts of the screening note
Lemmas 3.1 and 4.12 (with different, larger constants; the constants of the screening theorem are
existential).

Helper: `sq_setIntegral_le`, Cauchy–Schwarz `(∫_S G)² ≤ |S| ∫_S G²` on a set of finite measure.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

/-! ### Cauchy–Schwarz on a set of finite measure -/

/-- **Cauchy–Schwarz**: `(∫_S G)² ≤ |S| ∫_S G²`. -/
theorem sq_setIntegral_le {S : Set ℂ} (hS : volume S ≠ ⊤) {G : ℂ → ℝ} (hG : IntegrableOn G S)
    (hG2 : IntegrableOn (fun x => G x ^ 2) S) :
    (∫ x in S, G x) ^ 2 ≤ volume.real S * ∫ x in S, G x ^ 2 := by
  set a := volume.real S
  set I := ∫ x in S, G x
  set J := ∫ x in S, G x ^ 2
  have hJ : 0 ≤ J := setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun x => by positivity)
  rcases (measureReal_nonneg : 0 ≤ a).eq_or_lt with ha | ha
  · have h0 : volume S = 0 := by
      rw [measureReal_def] at ha
      rcases (ENNReal.toReal_eq_zero_iff _).1 ha.symm with h | h
      · exact h
      · exact absurd h hS
    have : I = 0 := by simp only [I, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    rw [this]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg measureReal_nonneg hJ
  have hfin : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS
  have hpt : ∀ s, 2 * (I / a) * G s ≤ G s ^ 2 + (I / a) ^ 2 := fun s => by
    linarith [sq_nonneg (G s - I / a)]
  have hmono : ∫ s in S, 2 * (I / a) * G s ≤ ∫ s in S, (G s ^ 2 + (I / a) ^ 2) :=
    integral_mono (hG.const_mul _) (hG2.add (integrable_const _)) hpt
  rw [integral_const_mul, integral_add hG2 (integrable_const _), setIntegral_const,
    smul_eq_mul] at hmono
  have e1 : 2 * (I / a) * I = 2 * (I ^ 2 / a) := by ring
  have e2 : a * (I / a) ^ 2 = I ^ 2 / a := by field_simp
  have h3 : I ^ 2 / a ≤ J := by linarith
  have ha' : a ≠ 0 := ha.ne'
  calc I ^ 2 = a * (I ^ 2 / a) := (mul_div_cancel₀ _ ha').symm
    _ ≤ a * J := mul_le_mul_of_nonneg_left h3 ha.le

/-! ### The cutoff -/

/-- The cutoff `φ_x(y) = min(1, max(0, 3/2 - |y - x|))`: `1` on `B̄(x, ½)`, `0` off `B(x, 3/2)`. -/
@[expose] noncomputable def ballCutoff (x y : ℂ) : ℝ := min 1 (max 0 (3 / 2 - ‖y - x‖))

variable {x y : ℂ}

theorem lipschitzWith_ballCutoff (x : ℂ) : LipschitzWith 1 (ballCutoff x) := by
  have h1 : LipschitzWith 1 fun y : ℂ => 3 / 2 - dist y x := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    have := abs_dist_sub_le a b x
    rw [abs_sub_comm] at this
    calc |3 / 2 - dist a x - (3 / 2 - dist b x)| = |dist b x - dist a x| := by ring_nf
      _ ≤ dist a b := by rw [abs_sub_comm]; exact abs_dist_sub_le a b x
  have h2 := (h1.const_max 0).const_min 1
  have he : ballCutoff x = fun y => min 1 (max 0 (3 / 2 - dist y x)) := by
    ext y; rw [ballCutoff, dist_eq_norm]
  rw [he]; exact h2

theorem ballCutoff_nonneg (x y : ℂ) : 0 ≤ ballCutoff x y :=
  le_min zero_le_one (le_max_left _ _)

theorem ballCutoff_le_one (x y : ℂ) : ballCutoff x y ≤ 1 := min_le_left _ _

theorem ballCutoff_eq_one (h : ‖y - x‖ ≤ 1 / 2) : ballCutoff x y = 1 :=
  min_eq_left (le_max_of_le_right (by linarith))

theorem ballCutoff_eq_zero (h : 3 / 2 ≤ ‖y - x‖) : ballCutoff x y = 0 := by
  rw [ballCutoff, max_eq_left (by linarith), min_eq_right zero_le_one]

theorem tsupport_ballCutoff_subset (x : ℂ) : tsupport (ballCutoff x) ⊆ closedBall x (3 / 2) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra h
  rw [mem_closedBall, dist_eq_norm, not_le] at h
  exact hy (ballCutoff_eq_zero h.le)

theorem hasCompactSupport_ballCutoff (x : ℂ) : HasCompactSupport (ballCutoff x) :=
  (isCompact_closedBall x (3 / 2)).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_ballCutoff_subset x)

theorem gradient_ballCutoff_of_notMem (h : y ∉ closedBall x (3 / 2)) :
    gradient (ballCutoff x) y = 0 := by
  have hev : ballCutoff x =ᶠ[nhds y] fun _ => 0 := by
    have : (closedBall x (3 / 2))ᶜ ∈ nhds y := isClosed_closedBall.isOpen_compl.mem_nhds h
    filter_upwards [this] with z hz
    rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hz
    exact ballCutoff_eq_zero hz.le
  simp only [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]

theorem volume_closedBall_three_halves (x : ℂ) :
    volume.real (closedBall x (3 / 2)) = 9 * π / 4 := by
  rw [measureReal_def, Measure.addHaar_closedBall_eq_addHaar_ball, Complex.volume_ball]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

theorem volume_closedBall_three_halves_ne_top (x : ℂ) : volume (closedBall x (3 / 2)) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

/-! ### The local count -/

section Count

variable {U : Set ℂ} (hU : IsOpen U) {m : ℝ} (hm : 0 ≤ m) {C : Set ℂ}
  (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {E : ℂ → ℂ} (hE : IsChargeField U m C E)
  (hxU : closedBall x (3 / 2) ⊆ U)
include hU hm hC hE hxU

/-- **Local count**: a finite set `P ⊆ C` inside `B(x, ¼)` has
`#P ≤ (9π/4) m + (2π)⁻¹ ∫_{B̄(x, 3/2)} |Φ|`, `Φ = E_{1/4}`. -/
theorem card_le_of_ballCutoff {P : Finset ℂ} (hPC : (P : Set ℂ) ⊆ C)
    (hP : ∀ q ∈ P, ‖q - x‖ < 1 / 4) :
    (P.card : ℝ) ≤ 9 * π / 4 * m +
      (2 * π)⁻¹ * ∫ y in closedBall x (3 / 2), ‖truncField C (fun _ => 1 / 4) E y‖ := by
  set Φ := truncField C (fun _ => 1 / 4) E
  set φ := ballCutoff x
  have hα : ∀ p ∈ C, (0 : ℝ) < (fun _ : ℂ => (1 : ℝ) / 4) p := fun _ _ => by norm_num
  have hαb : ∃ M, ∀ p ∈ C, (fun _ : ℂ => (1 : ℝ) / 4) p ≤ M := ⟨1 / 4, fun _ _ => le_rfl⟩
  have hI1 := integral_inner_truncField_lipschitz hU hC hE hα hαb (lipschitzWith_ballCutoff x)
    (hasCompactSupport_ballCutoff x) ((tsupport_ballCutoff_subset x).trans hxU)
  -- the finsum is a finite sum over the charges near `x`
  set R := ‖x‖ + 2
  set S := (hC R).toFinset
  have hfar : ∀ p ∈ C, p ∉ S → Real.circleAverage φ p (1 / 4) = 0 := by
    intro p hp hpS
    have hpR := lt_norm_of_notMem_toFinset (hC R) hp hpS
    refine Real.circleAverage_const_on_circle fun z hz => ballCutoff_eq_zero ?_
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hz
    have h1 : ‖p‖ ≤ ‖p - z‖ + ‖z - x‖ + ‖x‖ := by
      calc ‖p‖ = ‖(p - z) + (z - x) + x‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    rw [norm_sub_rev] at hz
    linarith
  have hSC : (S : Set ℂ) ⊆ C := fun p hp => mem_of_mem_toFinset (hC R) hp
  rw [finsum_mem_eq_finsetSum hSC hfar] at hI1
  have hPS : P ⊆ S := by
    intro q hq
    rw [Set.Finite.mem_toFinset]
    refine ⟨hPC hq, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖q‖ ≤ ‖q - x‖ + ‖x‖ := by
      calc ‖q‖ = ‖(q - x) + x‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith [hP q hq]
  have hcount : (P.card : ℝ) ≤ ∑ p ∈ S, Real.circleAverage φ p (1 / 4) := by
    have hone : ∀ q ∈ P, Real.circleAverage φ q (1 / 4) = 1 := by
      intro q hq
      refine Real.circleAverage_const_on_circle fun z hz => ballCutoff_eq_one ?_
      rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hz
      calc ‖z - x‖ = ‖(z - q) + (q - x)‖ := by ring_nf
        _ ≤ ‖z - q‖ + ‖q - x‖ := norm_add_le _ _
        _ ≤ 1 / 2 := by linarith [hP q hq]
    calc (P.card : ℝ) = ∑ q ∈ P, Real.circleAverage φ q (1 / 4) := by
          rw [Finset.sum_congr rfl hone]; simp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hPS fun p _ _ =>
          Real.circleAverage_nonneg_of_nonneg fun z _ => ballCutoff_nonneg x z
  -- the background term
  have hB : MeasurableSet (closedBall x (3 / 2)) := measurableSet_closedBall
  have hφi : ∫ y, φ y ≤ 9 * π / 4 := by
    have hφeq : φ = (closedBall x (3 / 2)).indicator φ := by
      ext y
      by_cases hy : y ∈ closedBall x (3 / 2)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy]
        rw [mem_closedBall, dist_eq_norm, not_le] at hy
        exact ballCutoff_eq_zero hy.le
    rw [hφeq, integral_indicator hB, ← volume_closedBall_three_halves x]
    have hfin : IsFiniteMeasure (volume.restrict (closedBall x (3 / 2))) :=
      isFiniteMeasure_restrict.2 (volume_closedBall_three_halves_ne_top x)
    calc ∫ y in closedBall x (3 / 2), φ y ≤ ∫ _y in closedBall x (3 / 2), (1 : ℝ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun y => ballCutoff_nonneg x y)
            (integrable_const _) (Eventually.of_forall fun y => ballCutoff_le_one x y)
      _ = volume.real (closedBall x (3 / 2)) := by simp
  -- the field term
  have hΦi : IntegrableOn Φ (closedBall x (3 / 2)) :=
    integrableOn_truncField hC hE.1 hα hαb (isCompact_closedBall x (3 / 2)) hxU
  have hpt : ∀ y, inner ℝ (Φ y) (gradient φ y) ≤
      (closedBall x (3 / 2)).indicator (fun y => ‖Φ y‖) y := by
    intro y
    by_cases hy : y ∈ closedBall x (3 / 2)
    · rw [indicator_of_mem hy]
      calc inner ℝ (Φ y) (gradient φ y) ≤ ‖Φ y‖ * ‖gradient φ y‖ := real_inner_le_norm _ _
        _ ≤ ‖Φ y‖ * 1 := by
            gcongr
            simpa using norm_gradient_le_of_lipschitz (lipschitzWith_ballCutoff x) y
        _ = ‖Φ y‖ := mul_one _
    · rw [indicator_of_notMem hy, gradient_ballCutoff_of_notMem hy, inner_zero_right]
  have hinner : Integrable fun y => inner ℝ (Φ y) (gradient φ y) := by
    have heq : (fun y => inner ℝ (Φ y) (gradient φ y)) =
        (closedBall x (3 / 2)).indicator fun y => inner ℝ (Φ y) (gradient φ y) := by
      ext y
      by_cases hy : y ∈ closedBall x (3 / 2)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy, gradient_ballCutoff_of_notMem hy, inner_zero_right]
    rw [heq, integrable_indicator_iff hB]
    refine Integrable.mono' hΦi.norm ?_ (Eventually.of_forall fun y => ?_)
    · exact hΦi.aestronglyMeasurable.inner (aestronglyMeasurable_gradient φ)
    · rw [Real.norm_eq_abs]
      calc |inner ℝ (Φ y) (gradient φ y)| ≤ ‖Φ y‖ * ‖gradient φ y‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖Φ y‖ * 1 := by
            gcongr
            simpa using norm_gradient_le_of_lipschitz (lipschitzWith_ballCutoff x) y
        _ = ‖Φ y‖ := mul_one _
  have hfield : ∫ y, inner ℝ (Φ y) (gradient φ y) ≤ ∫ y in closedBall x (3 / 2), ‖Φ y‖ := by
    rw [← integral_indicator hB]
    exact integral_mono hinner ((integrable_indicator_iff hB).2 hΦi.norm) hpt
  have hpi : 0 < 2 * π := by positivity
  have key : 2 * π * (P.card : ℝ) ≤ 2 * π * (9 * π / 4 * m) +
      ∫ y in closedBall x (3 / 2), ‖Φ y‖ := by
    have h1 : 2 * π * (P.card : ℝ) ≤ 2 * π * ∑ p ∈ S, Real.circleAverage φ p (1 / 4) :=
      mul_le_mul_of_nonneg_left hcount hpi.le
    have h2 : 2 * π * (m * ∫ y, φ y) ≤ 2 * π * (9 * π / 4 * m) := by
      have := mul_le_mul_of_nonneg_left hφi hm
      nlinarith
    linarith
  calc (P.card : ℝ) ≤ (2 * π * (9 * π / 4 * m) + ∫ y in closedBall x (3 / 2), ‖Φ y‖) / (2 * π) :=
        (le_div_iff₀' hpi).2 key
    _ = _ := by field_simp

/-- **Local count, squared form**: with `J = ∫_{B̄(x, 3/2)} |Φ|² < ∞`,
`#P² ≤ 2((9π/4) m)² + (9/8π) J`. -/
theorem ofReal_card_sq_le {P : Finset ℂ} (hPC : (P : Set ℂ) ⊆ C)
    (hP : ∀ q ∈ P, ‖q - x‖ < 1 / 4)
    (hJ : ∫⁻ y in closedBall x (3 / 2), ENNReal.ofReal (‖truncField C (fun _ => 1 / 4) E y‖ ^ 2) ≠ ⊤) :
    ENNReal.ofReal ((P.card : ℝ) ^ 2) ≤ ENNReal.ofReal (2 * (9 * π / 4 * m) ^ 2) +
      ENNReal.ofReal (9 / (8 * π)) *
        ∫⁻ y in closedBall x (3 / 2), ENNReal.ofReal (‖truncField C (fun _ => 1 / 4) E y‖ ^ 2) := by
  set Φ := truncField C (fun _ => 1 / 4) E
  set B := closedBall x (3 / 2)
  have hα : ∀ p ∈ C, (0 : ℝ) < (fun _ : ℂ => (1 : ℝ) / 4) p := fun _ _ => by norm_num
  have hαb : ∃ M, ∀ p ∈ C, (fun _ : ℂ => (1 : ℝ) / 4) p ≤ M := ⟨1 / 4, fun _ _ => le_rfl⟩
  have hΦi : IntegrableOn Φ B :=
    integrableOn_truncField hC hE.1 hα hαb (isCompact_closedBall x (3 / 2)) hxU
  have hΦ2 : IntegrableOn (fun y => ‖Φ y‖ ^ 2) B :=
    integrableOn_norm_sq_of_lintegral subset_rfl hΦi.aestronglyMeasurable hJ
  have hcount := card_le_of_ballCutoff hU hm hC hE hxU hPC hP
  set I := ∫ y in B, ‖Φ y‖
  set J := ∫ y in B, ‖Φ y‖ ^ 2
  have hCS : I ^ 2 ≤ volume.real B * J :=
    sq_setIntegral_le (volume_closedBall_three_halves_ne_top x) hΦi.norm hΦ2
  rw [volume_closedBall_three_halves] at hCS
  have hJ0 : 0 ≤ J := setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun y => by positivity)
  have hpi := Real.pi_pos
  have hsq : (P.card : ℝ) ^ 2 ≤ 2 * (9 * π / 4 * m) ^ 2 + 9 / (8 * π) * J := by
    have h0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
    have h1 : (P.card : ℝ) ^ 2 ≤ (9 * π / 4 * m + (2 * π)⁻¹ * I) ^ 2 := by gcongr
    have h2 : (9 * π / 4 * m + (2 * π)⁻¹ * I) ^ 2 ≤
        2 * (9 * π / 4 * m) ^ 2 + 2 * ((2 * π)⁻¹ * I) ^ 2 := by
      linarith [sq_nonneg (9 * π / 4 * m - (2 * π)⁻¹ * I)]
    have h3 : 2 * ((2 * π)⁻¹ * I) ^ 2 ≤ 9 / (8 * π) * J := by
      rw [mul_pow, inv_pow]
      have : 2 * ((2 * π) ^ 2)⁻¹ * (9 * π / 4 * J) = 9 / (8 * π) * J := by
        field_simp; ring
      calc 2 * (((2 * π) ^ 2)⁻¹ * I ^ 2) = 2 * ((2 * π) ^ 2)⁻¹ * I ^ 2 := by ring
        _ ≤ 2 * ((2 * π) ^ 2)⁻¹ * (9 * π / 4 * J) := by gcongr
        _ = _ := this
    linarith
  have hJeq : ENNReal.ofReal J = ∫⁻ y in B, ENNReal.ofReal (‖Φ y‖ ^ 2) :=
    ofReal_integral_eq_lintegral_ofReal hΦ2 (Eventually.of_forall fun y => by positivity)
  calc ENNReal.ofReal ((P.card : ℝ) ^ 2) ≤ ENNReal.ofReal (2 * (9 * π / 4 * m) ^ 2 + 9 / (8 * π) * J) :=
        ENNReal.ofReal_le_ofReal hsq
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 / (8 * π)), hJeq]

end Count

/-! ### Tonelli for ball averages -/

/-- `∫_S ∫_{B̄(x, r)} f ≤ |B̄(0, r)| ∫ f` for `f ≥ 0` a.e.-measurable. -/
theorem lintegral_setLIntegral_closedBall_le {f : ℂ → ℝ≥0∞} (hf : AEMeasurable f) (S : Set ℂ)
    (r : ℝ) :
    ∫⁻ x in S, ∫⁻ y in closedBall x r, f y ≤ volume (closedBall (0 : ℂ) r) * ∫⁻ y, f y := by
  set D : Set (ℂ × ℂ) := {p | dist p.2 p.1 ≤ r}
  have hD : MeasurableSet D :=
    (isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  set F : ℂ → ℂ → ℝ≥0∞ := fun x y => D.indicator (fun p => f p.2) (x, y)
  have hF : AEMeasurable (Function.uncurry F) (volume.prod volume) := by
    have : Function.uncurry F = D.indicator (fun p => f p.2) := by ext p; rfl
    rw [this]
    exact (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).indicator hD
  have hin : ∀ x, ∫⁻ y in closedBall x r, f y = ∫⁻ y, F x y := by
    intro x
    rw [← lintegral_indicator measurableSet_closedBall]
    rfl
  have hvol : ∀ y : ℂ, volume (closedBall y r) = volume (closedBall (0 : ℂ) r) := by
    intro y
    rw [Measure.addHaar_closedBall_eq_addHaar_ball, Measure.addHaar_closedBall_eq_addHaar_ball,
      Complex.volume_ball, Complex.volume_ball]
  have hout : ∀ y, ∫⁻ x, F x y = f y * volume (closedBall (0 : ℂ) r) := by
    intro y
    have : (fun x => F x y) = (closedBall y r).indicator (fun _ => f y) := by
      ext x
      simp only [F, D, indicator, mem_ofPred_eq, mem_closedBall, dist_comm x y]
    rw [this, lintegral_indicator_const measurableSet_closedBall, hvol, mul_comm]
  calc ∫⁻ x in S, ∫⁻ y in closedBall x r, f y ≤ ∫⁻ x, ∫⁻ y in closedBall x r, f y :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, ∫⁻ y, F x y := by simp_rw [hin]
    _ = ∫⁻ y, ∫⁻ x, F x y := lintegral_lintegral_swap hF
    _ = ∫⁻ y, f y * volume (closedBall (0 : ℂ) r) := by simp_rw [hout]
    _ = _ := by rw [lintegral_mul_const' _ _ measure_closedBall_lt_top.ne, mul_comm]

end SandierSerfaty.Screening

end
