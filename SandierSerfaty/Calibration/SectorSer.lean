/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorRadial
public import SandierSerfaty.Calibration.SectorH
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The radial series `ser a t r = ∑ aᵢ (r/t)^{kᵢ}` and its integrability

`ser a t r = ∑ᵢ aᵢ (r/t)^{kᵢ}` is the series part of the trial potential (with `aᵢ = Dᵢ(t)`), of the radial
gradient (`aᵢ = kᵢ Dᵢ(t)`) and of the angular gradient (`aᵢ = Qᵢ(t)`) along a ray. For `∑ |aᵢ| < ∞`,
`|ser a t r| ≤ (r/t)^6 ∑ |aᵢ|` on `[0, t]`, hence `ser a t r / r` and `ser a t r² / r` are bounded on `(0, t]`.
All integrability facts needed by `Calibration/SectorRest.lean` and `Calibration/AngleDensity.lean` are here.
-/

open Set MeasureTheory intervalIntegral

public section

namespace SandierSerfaty

namespace Calibration

/-- The radial series `∑ aᵢ (r/t)^{kᵢ}`. -/
@[expose] noncomputable def ser (a : ℕ → ℝ) (t r : ℝ) : ℝ := ∑' i, a i * (r / t) ^ k i

theorem measurable_ser (a : ℕ → ℝ) (t : ℝ) : Measurable (ser a t) := by
  unfold ser
  exact Measurable.tsum fun i => (measurable_const.mul ((measurable_id.div_const t).pow_const _))

theorem abs_ser_le {a : ℕ → ℝ} (ha : Summable fun i => |a i|) {t r : ℝ} (ht : 0 < t) (hr0 : 0 ≤ r)
    (hr : r ≤ t) : |ser a t r| ≤ (r / t) ^ 6 * ∑' i, |a i| := by
  have hq0 : 0 ≤ r / t := div_nonneg hr0 ht.le
  have hq1 : r / t ≤ 1 := (div_le_one ht).2 hr
  have hb : ∀ i, ‖a i * (r / t) ^ k i‖ ≤ (r / t) ^ 6 * |a i| := fun i => by
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0]
    rw [mul_comm ((r / t) ^ 6)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 (six_le_k i)) (abs_nonneg _)
  have := tsum_of_norm_bounded (ha.mul_left ((r / t) ^ 6)).hasSum hb
  rw [tsum_mul_left] at this
  simpa [ser, Real.norm_eq_abs] using this

theorem abs_ser_div_le {a : ℕ → ℝ} (ha : Summable fun i => |a i|) {t r : ℝ} (ht : 0 < t) (hr0 : 0 < r)
    (hr : r ≤ t) : |ser a t r / r| ≤ (∑' i, |a i|) / t := by
  have h := abs_ser_le ha ht hr0.le hr
  have hS : 0 ≤ ∑' i, |a i| := tsum_nonneg fun i => abs_nonneg _
  have hq0 : 0 ≤ r / t := div_nonneg hr0.le ht.le
  have hq1 : r / t ≤ 1 := (div_le_one ht).2 hr
  rw [abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
  have h6 : (r / t) ^ 6 ≤ r / t := by
    simpa using pow_le_pow_of_le_one hq0 hq1 (by norm_num : 1 ≤ 6)
  calc |ser a t r| ≤ (r / t) ^ 6 * ∑' i, |a i| := h
    _ ≤ (r / t) * ∑' i, |a i| := mul_le_mul_of_nonneg_right h6 hS
    _ = (∑' i, |a i|) / t * r := by field_simp

theorem abs_ser_div_sq_le {a : ℕ → ℝ} (ha : Summable fun i => |a i|) {t r : ℝ} (ht : 0 < t) (hr0 : 0 < r)
    (hr : r ≤ t) : |ser a t r| / r ^ 2 ≤ (∑' i, |a i|) / t ^ 2 := by
  have h := abs_ser_le ha ht hr0.le hr
  have hS : 0 ≤ ∑' i, |a i| := tsum_nonneg fun i => abs_nonneg _
  have hq0 : 0 ≤ r / t := div_nonneg hr0.le ht.le
  have hq1 : r / t ≤ 1 := (div_le_one ht).2 hr
  have h6 : (r / t) ^ 6 ≤ (r / t) ^ 2 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  calc |ser a t r| ≤ (r / t) ^ 6 * ∑' i, |a i| := h
    _ ≤ (r / t) ^ 2 * ∑' i, |a i| := mul_le_mul_of_nonneg_right h6 hS
    _ = (∑' i, |a i|) / t ^ 2 * r ^ 2 := by field_simp

theorem intervalIntegrable_of_bounded_Ioc {f : ℝ → ℝ} {t C : ℝ} (ht : 0 < t)
    (hm : AEStronglyMeasurable f volume) (hb : ∀ r ∈ Ioc 0 t, |f r| ≤ C) :
    IntervalIntegrable f volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hm ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall fun r hr => by simpa using hb r hr)

variable {a : ℕ → ℝ} {t : ℝ}

theorem intervalIntegrable_ser_div (ha : Summable fun i => |a i|) (ht : 0 < t) :
    IntervalIntegrable (fun r => ser a t r / r) volume 0 t :=
  intervalIntegrable_of_bounded_Ioc ht ((measurable_ser a t).div measurable_id).aestronglyMeasurable
    (fun _ hr => abs_ser_div_le ha ht hr.1 hr.2)

theorem intervalIntegrable_ser_sq_div (ha : Summable fun i => |a i|) (ht : 0 < t) :
    IntervalIntegrable (fun r => ser a t r ^ 2 / r) volume 0 t := by
  refine intervalIntegrable_of_bounded_Ioc (C := ((∑' i, |a i|) / t) * ∑' i, |a i|) ht
    (((measurable_ser a t).pow_const 2).div measurable_id).aestronglyMeasurable fun r hr => ?_
  have h1 := abs_ser_div_le ha ht hr.1 hr.2
  have h2 := abs_ser_le ha ht hr.1.le hr.2
  have hq1 : r / t ≤ 1 := (div_le_one ht).2 hr.2
  have hq0 : 0 ≤ r / t := div_nonneg hr.1.le ht.le
  have hS : 0 ≤ ∑' i, |a i| := tsum_nonneg fun i => abs_nonneg _
  have e : ser a t r ^ 2 / r = (ser a t r / r) * ser a t r := by
    field_simp
  rw [e, abs_mul]
  refine mul_le_mul h1 (h2.trans ?_) (abs_nonneg _) (by positivity)
  calc (r / t) ^ 6 * ∑' i, |a i| ≤ 1 * ∑' i, |a i| :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hS
    _ = ∑' i, |a i| := one_mul _

theorem measurable_B₁ : Measurable B₁ := by
  unfold B₁
  exact (measurable_deriv B).add (measurable_const.div measurable_id)

theorem intervalIntegrable_B₁_ser (ha : Summable fun i => |a i|) (ht : 0 < t) :
    IntervalIntegrable (fun r => B₁ r * ser a t r) volume 0 t := by
  obtain ⟨C, hC0, hC⟩ := exists_B₁_bound t
  have hS : 0 ≤ ∑' i, |a i| := tsum_nonneg fun i => abs_nonneg _
  refine intervalIntegrable_of_bounded_Ioc (C := C * ∑' i, |a i|) ht
    (measurable_B₁.mul (measurable_ser a t)).aestronglyMeasurable fun r hr => ?_
  rw [abs_mul]
  have h2 := abs_ser_le ha ht hr.1.le hr.2
  have hq1 : r / t ≤ 1 := (div_le_one ht).2 hr.2
  have hq0 : 0 ≤ r / t := div_nonneg hr.1.le ht.le
  refine mul_le_mul (hC r hr) (h2.trans ?_) (abs_nonneg _) hC0
  calc (r / t) ^ 6 * ∑' i, |a i| ≤ 1 * ∑' i, |a i| :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hS
    _ = ∑' i, |a i| := one_mul _

theorem intervalIntegrable_r_ser (ha : Summable fun i => |a i|) (ht : 0 < t) :
    IntervalIntegrable (fun r => r * ser a t r) volume 0 t := by
  have hS : 0 ≤ ∑' i, |a i| := tsum_nonneg fun i => abs_nonneg _
  refine intervalIntegrable_of_bounded_Ioc (C := t * ∑' i, |a i|) ht
    (measurable_id.mul (measurable_ser a t)).aestronglyMeasurable fun r hr => ?_
  rw [abs_mul, abs_of_pos hr.1]
  have h2 := abs_ser_le ha ht hr.1.le hr.2
  have hq1 : r / t ≤ 1 := (div_le_one ht).2 hr.2
  have hq0 : 0 ≤ r / t := div_nonneg hr.1.le ht.le
  refine mul_le_mul hr.2 (h2.trans ?_) (abs_nonneg _) ht.le
  calc (r / t) ^ 6 * ∑' i, |a i| ≤ 1 * ∑' i, |a i| :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1) hS
    _ = ∑' i, |a i| := one_mul _

end Calibration

end SandierSerfaty

end
