/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.KernelSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The radial integrals along a ray of the model sector

Paper, verification of `cal:angle-density`. Along the ray of angle `φ`, with `t = d sec φ`, the series part of the trial
potential is `∑ᵢ cᵢ (r/t)^{kᵢ}` (`cᵢ = Dᵢ(t)`). The four radial integrals of the angle density, for absolutely
summable coefficient sequences (`t > 0`):

* `integral_weighted_series`: `∫₀ᵗ w(r) ∑ qᵢ (r/t)^{kᵢ} dr = ∑ qᵢ ∫₀ᵗ w(r) (r/t)^{kᵢ} dr` for a bounded weight `w`;
* `integral_source_series`: `∫₀ᵗ r ∑ cᵢ (r/t)^{kᵢ} dr = t² ∑ cᵢ/(kᵢ+2)`;
* `integral_B₁_series`: `∫₀ᵗ B₁(r) ∑ aᵢ (r/t)^{kᵢ} dr = ∑ aᵢ H_{kᵢ}(t)`;
* `integral_series_div`: `∫₀ᵗ (∑ aᵢ (r/t)^{kᵢ}) dr/r = ∑ aᵢ/kᵢ`;
* `integral_sq_series_div`: `∫₀ᵗ (∑ aᵢ (r/t)^{kᵢ})² dr/r = ∑_{i,j} aᵢ aⱼ/(kᵢ+kⱼ)`;
* `integral_radial_sq`: `∫_η^t r B'(r)² dr = S₂(t) - S₂(η) + log t - log η`.
-/

open Set MeasureTheory intervalIntegral

public section

namespace SandierSerfaty

namespace Calibration

/-- Scaling `r = t v`: `∫₀ᵗ F(r) dr/r = ∫₀¹ F(t v) dv/v`. -/
theorem integral_scale_div {t : ℝ} (ht : 0 < t) (F : ℝ → ℝ) :
    ∫ r in (0 : ℝ)..t, F r / r = ∫ v in (0 : ℝ)..1, F (t * v) / v := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun r => F r / r) ht.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  have e : ∀ v : ℝ, F (t * v) / v = t * (F (t * v) / (t * v)) := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · field_simp
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp

theorem pow_div_le_one {t r : ℝ} (ht : 0 < t) (hr0 : 0 ≤ r) (hr : r ≤ t) (n : ℕ) : (r / t) ^ n ≤ 1 :=
  pow_le_one₀ (div_nonneg hr0 ht.le) ((div_le_one ht).2 hr)

theorem integral_weighted_series {w : ℝ → ℝ} {C t : ℝ} (ht : 0 < t)
    (hwm : AEStronglyMeasurable w (volume.restrict (Ioc 0 t))) (hC : ∀ r ∈ Ioc 0 t, |w r| ≤ C)
    {q : ℕ → ℝ} (hq : Summable fun i => |q i|) :
    ∫ r in (0 : ℝ)..t, w r * ∑' i, q i * (r / t) ^ k i =
      ∑' i, q i * ∫ r in (0 : ℝ)..t, w r * (r / t) ^ k i := by
  set F : ℕ → ℝ → ℝ := fun i r => q i * (w r * (r / t) ^ k i) with hF
  have hmeasF : ∀ i, AEStronglyMeasurable (F i) (volume.restrict (uIoc (0 : ℝ) t)) := fun i => by
    rw [uIoc_of_le ht.le]
    exact aestronglyMeasurable_const.mul
      (hwm.mul (((continuous_id.div_const t).pow _).aestronglyMeasurable))
  have hbound : ∀ i, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ uIoc (0 : ℝ) t → ‖F i r‖ ≤ |q i| * |C| := by
    intro i
    refine Filter.Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le ht.le] at hr
    simp only [hF, norm_mul, Real.norm_eq_abs, abs_pow]
    have h1 := hC r hr
    have h2 : (|r / t|) ^ k i ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hr.1.le ht.le)]; exact pow_div_le_one ht hr.1.le hr.2 _
    calc |q i| * (|w r| * |r / t| ^ k i) ≤ |q i| * (|C| * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact mul_le_mul (h1.trans (le_abs_self C)) h2 (by positivity) (abs_nonneg _)
      _ = |q i| * |C| := by ring
  have hlim : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ uIoc (0 : ℝ) t →
      HasSum (fun i => F i r) (w r * ∑' i, q i * (r / t) ^ k i) := by
    refine Filter.Eventually.of_forall fun r hr => ?_
    rw [uIoc_of_le ht.le] at hr
    have hs : Summable fun i => q i * (r / t) ^ k i := by
      refine Summable.of_norm_bounded hq fun i => ?_
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.1.le ht.le)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_div_le_one ht hr.1.le hr.2 _)
    have := hs.hasSum.mul_left (w r)
    convert this using 1
    funext i; simp only [hF]; ring
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := t)
    (f := fun r => w r * ∑' i, q i * (r / t) ^ k i) (F := F) (fun i _ => |q i| * |C|) hmeasF hbound
    (Filter.Eventually.of_forall fun r _ => hq.mul_right _) intervalIntegrable_const hlim
  rw [← key.tsum_eq]
  refine tsum_congr fun i => ?_
  simp only [hF]
  rw [intervalIntegral.integral_const_mul]

/-- `∫₀ᵗ r (r/t)^k dr = t²/(k+2)`. -/
theorem integral_r_mul_pow_div {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∫ r in (0 : ℝ)..t, r * (r / t) ^ n = t ^ 2 / ((n : ℝ) + 2) := by
  have : ∀ r : ℝ, r * (r / t) ^ n = (t ^ n)⁻¹ * r ^ (n + 1) := fun r => by
    rw [div_pow, pow_succ]; field_simp
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hn : t ^ (n + 1 + 1) = t ^ n * t ^ 2 := by rw [pow_add]; ring
  field_simp
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
  push_cast
  rw [hn]
  field_simp
  ring

theorem integral_source_series {t : ℝ} (ht : 0 < t) {c : ℕ → ℝ} (hc : Summable fun i => |c i|) :
    ∫ r in (0 : ℝ)..t, r * ∑' i, c i * (r / t) ^ k i = t ^ 2 * ∑' i, c i / ((k i : ℝ) + 2) := by
  have := integral_weighted_series (w := fun r => r) (C := t) ht
    ((continuous_id.aestronglyMeasurable)) (fun r hr => by
      rw [abs_of_pos hr.1]; exact hr.2) hc
  rw [this, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [integral_r_mul_pow_div ht]
  ring

theorem integral_pow_div_B₁ {t : ℝ} (_ht : 0 < t) (n : ℕ) :
    ∫ r in (0 : ℝ)..t, B₁ r * (r / t) ^ n = H n t := by
  have : ∀ r : ℝ, B₁ r * (r / t) ^ n = (t ^ n)⁻¹ * (B₁ r * r ^ n) := fun r => by
    rw [div_pow]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  rfl

theorem integral_B₁_series {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} (ha : Summable fun i => |a i|) :
    ∫ r in (0 : ℝ)..t, B₁ r * ∑' i, a i * (r / t) ^ k i = ∑' i, a i * H (k i) t := by
  obtain ⟨C, hC0, hC⟩ := exists_B₁_bound t
  have hm : AEStronglyMeasurable B₁ (volume.restrict (Ioc 0 t)) :=
    (continuousOn_B₁.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  rw [integral_weighted_series ht hm hC ha]
  refine tsum_congr fun i => ?_
  rw [integral_pow_div_B₁ ht]

theorem integral_series_div {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} (ha : Summable fun i => |a i|) :
    ∫ r in (0 : ℝ)..t, (∑' i, a i * (r / t) ^ k i) / r = ∑' i, a i / (k i : ℝ) := by
  rw [integral_scale_div ht (fun r => ∑' i, a i * (r / t) ^ k i)]
  have : ∀ v : ℝ, (∑' i, a i * (t * v / t) ^ k i) = ∑' i, a i * v ^ k i := fun v => by
    simp [mul_div_cancel_left₀ _ ht.ne']
  simp_rw [this]
  exact integral_series_inv ha

theorem integral_sq_series_div {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} (ha : Summable fun i => |a i|) :
    ∫ r in (0 : ℝ)..t, (∑' i, a i * (r / t) ^ k i) ^ 2 / r =
      ∑' ij : ℕ × ℕ, a ij.1 * a ij.2 / ((k ij.1 : ℝ) + k ij.2) := by
  rw [integral_scale_div ht (fun r => (∑' i, a i * (r / t) ^ k i) ^ 2)]
  have : ∀ v : ℝ, (∑' i, a i * (t * v / t) ^ k i) = ∑' i, a i * v ^ k i := fun v => by
    simp [mul_div_cancel_left₀ _ ht.ne']
  simp_rw [this]
  exact integral_sq_series ha

/-- The singular radial part: `∫_η^t r B'(r)² dr = S₂(t) - S₂(η) + log t - log η`. -/
theorem integral_radial_sq {η t : ℝ} (hη : 0 < η) (hηt : η ≤ t) :
    ∫ r in η..t, r * (deriv B r) ^ 2 = (S₂ t - S₂ η) + (Real.log t - Real.log η) := by
  have ht : 0 < t := lt_of_lt_of_le hη hηt
  set g : ℝ → ℝ := fun r => -2 * B₁ r + r * B₁ r ^ 2 with hg
  have hgt : IntervalIntegrable g volume 0 t := nearZero_S₂.intervalIntegrable ht
  have hgη : IntervalIntegrable g volume 0 η := nearZero_S₂.intervalIntegrable hη
  have hgs : IntervalIntegrable g volume η t := by
    refine (hgt.mono_set ?_)
    rw [uIcc_of_le hηt, uIcc_of_le ht.le]
    exact Icc_subset_Icc hη.le le_rfl
  have hinv : IntervalIntegrable (fun r : ℝ => 1 / r) volume η t := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.div continuousOn_id fun r hr => by
      rw [uIcc_of_le hηt] at hr; exact (lt_of_lt_of_le hη hr.1).ne'
  have hcongr : ∫ r in η..t, r * (deriv B r) ^ 2 = ∫ r in η..t, (g r + 1 / r) := by
    refine integral_congr fun r hr => ?_
    rw [uIcc_of_le hηt] at hr
    have hr0 : 0 < r := lt_of_lt_of_le hη hr.1
    simp only [hg]
    unfold B₁
    field_simp
    ring
  rw [hcongr, integral_add hgs hinv, integral_one_div_of_pos hη ht, Real.log_div ht.ne' hη.ne']
  have : ∫ r in η..t, g r = S₂ t - S₂ η := by
    unfold S₂
    rw [← integral_interval_sub_left hgt hgη]
  rw [this]

end Calibration

end SandierSerfaty

end
