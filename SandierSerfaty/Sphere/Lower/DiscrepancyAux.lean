/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Cutoff
public import SandierSerfaty.Sphere.Lower.Counting
public import SandierSerfaty.Sphere.Lower.Quantize
public import SandierSerfaty.Sphere.Lower.DensityFreeze

/-!
# Elementary pieces of the discrepancy lemma (sphere note, Lemma 6.7)

Square geometry (`Lower.mem_sqShrink`, volumes of layers), a Cauchy–Schwarz bound, the circle average of the cutoff and
the bound `|∫_Q m - ∫ m χ| ≤ 4 m₊ t`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal Pointwise

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem mem_sqShrink {a z : ℂ} {t s : ℝ} : z ∈ sqShrink a t s ↔
    a.re + s ≤ z.re ∧ z.re ≤ a.re + t - s ∧ a.im + s ≤ z.im ∧ z.im ≤ a.im + t - s := by
  simp only [sqShrink, sqAt, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem mem_sqAt {a z : ℂ} {t : ℝ} : z ∈ sqAt a t ↔
    a.re ≤ z.re ∧ z.re ≤ a.re + t ∧ a.im ≤ z.im ∧ z.im ≤ a.im + t := by
  simp only [sqAt, Set.mem_ofPred_eq]

theorem sqShrink_zero (a : ℂ) (t : ℝ) : sqShrink a t 0 = sqAt a t := by
  ext z
  rw [mem_sqShrink, mem_sqAt]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem sqShrink_anti (a : ℂ) (t : ℝ) {s s' : ℝ} (h : s ≤ s') : sqShrink a t s' ⊆ sqShrink a t s := by
  intro z hz
  rw [mem_sqShrink] at hz ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hz
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem sqShrink_subset_sqAt (a : ℂ) (t : ℝ) {s : ℝ} (h : 0 ≤ s) : sqShrink a t s ⊆ sqAt a t := by
  rw [← sqShrink_zero]; exact sqShrink_anti a t h

theorem measurableSet_sqShrink (a : ℂ) (t s : ℝ) : MeasurableSet (sqShrink a t s) :=
  measurableSet_sqAt _ _

theorem isCompact_sqAt (a : ℂ) (t : ℝ) : IsCompact (sqAt a t) := by
  have hcl : IsClosed (sqAt a t) := by
    have : sqAt a t = {z : ℂ | a.re ≤ z.re} ∩ ({z : ℂ | z.re ≤ a.re + t} ∩
        ({z : ℂ | a.im ≤ z.im} ∩ {z : ℂ | z.im ≤ a.im + t})) := by
      ext z; simp [mem_sqAt]
    rw [this]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := a) (r := 2 * |t|)).subset fun z hz => ?_
  rw [mem_sqAt] at hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 : |(z - a).re| ≤ |t| := by
    rw [Complex.sub_re, abs_le]; constructor <;> cases abs_cases t <;> linarith [hz.1, hz.2.1]
  have h2 : |(z - a).im| ≤ |t| := by
    rw [Complex.sub_im, abs_le]; constructor <;> cases abs_cases t <;> linarith [hz.2.2.1, hz.2.2.2]
  have := Complex.norm_le_abs_re_add_abs_im (z - a)
  linarith

theorem volume_real_sqAt (a : ℂ) {t : ℝ} (ht : 0 ≤ t) : volume.real (sqAt a t) = t ^ 2 := by
  rw [measureReal_def, volume_sqAt, ← ENNReal.ofReal_mul ht, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem volume_sqAt_ne_top (a : ℂ) (t : ℝ) : volume (sqAt a t) ≠ ⊤ := by
  rw [volume_sqAt]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The layer `Q^{1/2} ∖ Q¹` has area `2 t - 3 ≤ 2 t` (for `t ≥ 2`). -/
theorem volume_real_layer (a : ℂ) {t : ℝ} (ht : 2 ≤ t) :
    volume.real (sqShrink a t (1 / 2) \ sqShrink a t 1) ≤ 2 * t := by
  rw [measureReal_sdiff (sqShrink_anti a t (by norm_num)) (measurableSet_sqShrink _ _ _)
    (volume_sqAt_ne_top _ _)]
  unfold sqShrink
  rw [volume_real_sqAt _ (by linarith), volume_real_sqAt _ (by linarith)]
  linarith

/-- The boundary layer `Q ∖ Q¹` has area at most `4 t`. -/
theorem volume_real_layer' (a : ℂ) {t : ℝ} (ht : 2 ≤ t) :
    volume.real (sqAt a t \ sqShrink a t 1) ≤ 4 * t := by
  rw [measureReal_sdiff (sqShrink_subset_sqAt a t (by norm_num)) (measurableSet_sqShrink _ _ _)
    (volume_sqAt_ne_top _ _)]
  unfold sqShrink
  rw [volume_real_sqAt _ (by linarith), volume_real_sqAt _ (by linarith)]
  linarith

/-- The `1/2`-neighborhood of the boundary layer `Q ∖ Q^{5/4}` has area at most `9 t`. -/
theorem volume_boundary_nbhd (a : ℂ) {t : ℝ} (ht : 2 ≤ t) :
    volume (((sqAt a t \ sqShrink a t (5 / 4)) + Metric.ball (0 : ℂ) (1 / 2))) ≤ ENNReal.ofReal (9 * t) := by
  have hsub : ((sqAt a t \ sqShrink a t (5 / 4)) + Metric.ball (0 : ℂ) (1 / 2)) ⊆
      sqAt (a - ⟨1 / 2, 1 / 2⟩) (t + 1) \ sqShrink a t (7 / 4) := by
    intro w hw
    obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_add.1 hw
    have hb' : ‖b‖ < 1 / 2 := by simpa using hb
    have hbr : |b.re| ≤ 1 / 2 := (Complex.abs_re_le_norm b).trans hb'.le
    have hbi : |b.im| ≤ 1 / 2 := (Complex.abs_im_le_norm b).trans hb'.le
    rw [abs_le] at hbr hbi
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_sqAt] at hp1
    rw [mem_sqShrink] at hp2
    constructor
    · rw [mem_sqAt]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro hq
      rw [mem_sqShrink] at hq
      simp only [Complex.add_re, Complex.add_im] at hq
      apply hp2
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine (measure_mono hsub).trans ?_
  have hT : sqShrink a t (7 / 4) ⊆ sqAt (a - ⟨1 / 2, 1 / 2⟩) (t + 1) := by
    intro z hz
    rw [mem_sqShrink] at hz
    rw [mem_sqAt]
    simp only [Complex.sub_re, Complex.sub_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [← ofReal_measureReal (ne_top_of_le_ne_top (volume_sqAt_ne_top (a - ⟨1 / 2, 1 / 2⟩) (t + 1))
    (measure_mono Set.sdiff_subset))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [measureReal_sdiff hT (measurableSet_sqShrink _ _ _) (volume_sqAt_ne_top _ _),
    volume_real_sqAt _ (by linarith)]
  have h0 : 0 ≤ volume.real (sqShrink a t (7 / 4)) := measureReal_nonneg
  by_cases h : 7 / 2 ≤ t
  · unfold sqShrink
    rw [volume_real_sqAt _ (by linarith)]
    linarith
  · nlinarith

/-- Cauchy–Schwarz: `∫ g ≤ √μ(ℂ) · √(∫ g²)` for `g ≥ 0` in `L²` of a finite measure. -/
theorem integral_le_sqrt_mul_sqrt {μ : Measure ℂ} [IsFiniteMeasure μ] {g : ℂ → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : MemLp g 2 μ) :
    ∫ x, g x ∂μ ≤ Real.sqrt (μ.real univ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h1 : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have h2 : MemLp (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : ℂ => (1 : ℝ)) 2 μ)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Eventually.of_forall hg0) (Eventually.of_forall fun _ => zero_le_one) h1 h2
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [mul_comm]
  simpa [Measure.real] using h

end Lower

end Sphere

end SandierSerfaty

end
