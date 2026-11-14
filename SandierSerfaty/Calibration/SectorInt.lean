/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SeriesB
public import SandierSerfaty.Calibration.Sector
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `C²` of the sector integrals `S₁, S₂, H_k` and uniform bounds on `H_k`

paper `cal:radial-integrals`.

* `B₁ = B' + 1/t` is `C¹` on `(0, ∞)` (`contDiffOn_B₁`) and `|B₁(r)| ≤ C r` near `0` (`radial_origin`), so `B₁`
  is bounded on every `(0, T]` (`exists_B₁_bound`);
* `NearZero F`: `F` is continuous on `(0, ∞)` and dominated near `0` by an interval-integrable function; then
  the primitive `x ↦ ∫₀ˣ F` has derivative `F` on `(0, ∞)` (`hasDerivAt_primitive`), and is `C²` if `F` is `C¹`;
* `S₁ = ∫₀ˣ B r dr`, `S₂`, and `I_k = ∫₀ˣ B₁ r^k dr` are `C²` on `(0, ∞)`; so is `H_k = t^{-k} I_k`;
* `H_k' = B₁ - (k/t) H_k`, and for `t ∈ [d, T]`: `|H_k| ≤ A`, `|H_k'| ≤ A(1+k)`, `|H_k''| ≤ A(1+k)²`
  with `A` independent of `k` (`exists_H_bound`).
-/

open Set MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

/-- `B₁` is `C¹` on `(0, ∞)`. -/
theorem contDiffOn_B₁ : ContDiffOn ℝ 1 B₁ (Ioi 0) := by
  unfold B₁
  have h : ContDiffOn ℝ 1 (deriv B) (Ioi 0) :=
    contDiffOn_B.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
  exact h.add (contDiffOn_const.div contDiffOn_id fun x hx => ne_of_gt hx)

theorem continuousOn_B : ContinuousOn B (Ioi 0) := contDiffOn_B.continuousOn

theorem continuousOn_B₁ : ContinuousOn B₁ (Ioi 0) := contDiffOn_B₁.continuousOn

theorem continuousOn_deriv_B₁ : ContinuousOn (deriv B₁) (Ioi 0) :=
  (contDiffOn_B₁.deriv_of_isOpen isOpen_Ioi (m := 0) (by norm_num)).continuousOn

/-- Near `0`: `|B₁ r| ≤ C r` and `|B r| ≤ |log r| + C` on `(0, 1/4]`. -/
theorem near_zero_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0 : ℝ) (1 / 4),
    |B₁ r| ≤ C * r ∧ |B r| ≤ |Real.log r| + C := by
  obtain ⟨C, hC⟩ := radial_origin
  refine ⟨|C|, abs_nonneg _, fun r hr => ?_⟩
  have hr' : r ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hr.1, by linarith [hr.2]⟩
  obtain ⟨h1, h2⟩ := hC r hr'
  have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
  refine ⟨?_, ?_⟩
  · unfold B₁
    exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hr.1.le)
  · have : |B r| ≤ |B r + Real.log r| + |Real.log r| := by
      have := abs_sub (B r + Real.log r) (Real.log r)
      simpa using this
    have h3 : C * r ^ 2 ≤ |C| := by
      calc C * r ^ 2 ≤ |C| * r ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg r)
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
        _ = |C| := mul_one _
    linarith

/-- `B₁` is bounded on `(0, T]`. -/
theorem exists_B₁_bound (T : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc 0 T, |B₁ r| ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := near_zero_bounds
  have hsub : Icc (1 / 4 : ℝ) T ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (by norm_num) hr.1
  obtain ⟨C₁, h₁⟩ := (isCompact_Icc (a := (1 / 4 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuousOn_B₁.mono hsub)
  refine ⟨max C₀ (max C₁ 0), le_max_of_le_left hC₀, fun r hr => ?_⟩
  by_cases h : r ≤ 1 / 4
  · have := (h₀ r ⟨hr.1, h⟩).1
    have h' : C₀ * r ≤ C₀ := by nlinarith [hr.1]
    exact (this.trans h').trans (le_max_left _ _)
  · push Not at h
    have := h₁ r ⟨h.le, hr.2⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))

/-! ### Primitives of functions dominated near `0` -/

/-- `F` is continuous on `(0, ∞)` and dominated near `0` by an integrable function. -/
def NearZero (F : ℝ → ℝ) : Prop :=
  ContinuousOn F (Ioi 0) ∧ ∃ g : ℝ → ℝ, IntervalIntegrable g volume 0 (1 / 4) ∧
    ∀ r ∈ Ioc (0 : ℝ) (1 / 4), |F r| ≤ g r

theorem NearZero.intervalIntegrable {F : ℝ → ℝ} (hF : NearZero F) {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable F volume 0 t := by
  obtain ⟨hc, g, hg, hb⟩ := hF
  have h1 : IntervalIntegrable F volume 0 (1 / 4) := by
    refine hg.mono_fun' ?_ ?_
    · rw [Set.uIoc_of_le (by norm_num)]
      exact (hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · rw [Set.uIoc_of_le (by norm_num)]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa using hb r hr
  have h2 : IntervalIntegrable F volume (1 / 4) t := by
    refine (hc.mono fun x hx => ?_).intervalIntegrable
    exact lt_of_lt_of_le (lt_min (by norm_num) ht) hx.1
  exact h1.trans h2

theorem hasDerivAt_primitive {F : ℝ → ℝ} (hF : NearZero F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, F r) (F t) t :=
  intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable ht)
    (hF.1.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hF.1.continuousAt (Ioi_mem_nhds ht))

theorem contDiffOn_primitive {F : ℝ → ℝ} (hF : NearZero F) (hF1 : ContDiffOn ℝ 1 F (Ioi 0)) :
    ContDiffOn ℝ 2 (fun x => ∫ r in (0 : ℝ)..x, F r) (Ioi 0) := by
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, F r) (F x) x :=
    fun x hx => hasDerivAt_primitive hF hx
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact hF1.congr fun x hx => (hd x hx).deriv

/-! ### The integrands -/

theorem nearZero_S₁ : NearZero fun r => B r * r := by
  obtain ⟨C, hC0, hC⟩ := near_zero_bounds
  refine ⟨continuousOn_B.mul continuousOn_id, fun r => |Real.log r| + C,
    (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1 / 4)).abs.add intervalIntegrable_const,
    fun r hr => ?_⟩
  have h := (hC r hr).2
  have hr1 : r ≤ 1 := by linarith [hr.2]
  rw [abs_mul, abs_of_pos hr.1]
  calc |B r| * r ≤ |B r| * 1 := mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)
    _ ≤ _ := by simpa using h

theorem nearZero_const_bound {F : ℝ → ℝ} (hc : ContinuousOn F (Ioi 0)) (C : ℝ)
    (hb : ∀ r ∈ Ioc (0 : ℝ) (1 / 4), |F r| ≤ C) : NearZero F :=
  ⟨hc, fun _ => C, intervalIntegrable_const, hb⟩

theorem nearZero_S₂ : NearZero fun r => -2 * B₁ r + r * B₁ r ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := near_zero_bounds
  refine nearZero_const_bound ?_ (2 * C + C ^ 2) fun r hr => ?_
  · exact (continuousOn_B₁.const_smul (-2 : ℝ)).add (continuousOn_id.mul (continuousOn_B₁.pow 2))
  · have h := (hC r hr).1
    have hr1 : r ≤ 1 := by linarith [hr.2]
    have hb : |B₁ r| ≤ C := h.trans (by nlinarith [hr.1])
    calc |-2 * B₁ r + r * B₁ r ^ 2| ≤ |-2 * B₁ r| + |r * B₁ r ^ 2| := abs_add_le _ _
      _ ≤ 2 * C + C ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos hr.1, abs_pow]
          have h2 : |B₁ r| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          have h3 : r * |B₁ r| ^ 2 ≤ C ^ 2 := by
            calc r * |B₁ r| ^ 2 ≤ 1 * |B₁ r| ^ 2 :=
                  mul_le_mul_of_nonneg_right hr1 (sq_nonneg _)
              _ ≤ C ^ 2 := by linarith
          have h2' : B₁ r ^ 2 ≤ C ^ 2 := by rw [← sq_abs]; exact h2
          have h3' : r * B₁ r ^ 2 ≤ C ^ 2 := by rw [← sq_abs]; exact h3
          norm_num
          linarith

theorem nearZero_Ik (n : ℕ) : NearZero fun r => B₁ r * r ^ n := by
  obtain ⟨C, hC0, hC⟩ := near_zero_bounds
  refine nearZero_const_bound ?_ C fun r hr => ?_
  · exact continuousOn_B₁.mul (continuousOn_id.pow n)
  · have h := (hC r hr).1
    have hr1 : r ≤ 1 := by linarith [hr.2]
    have hb : |B₁ r| ≤ C := h.trans (by nlinarith [hr.1])
    rw [abs_mul, abs_pow, abs_of_pos hr.1]
    calc |B₁ r| * r ^ n ≤ |B₁ r| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hr.1.le hr1) (abs_nonneg _)
      _ ≤ C := by simpa using hb

theorem contDiffOn_integrand_S₁ : ContDiffOn ℝ 1 (fun r => B r * r) (Ioi 0) :=
  (contDiffOn_B.of_le (by norm_num)).mul contDiffOn_id

theorem contDiffOn_integrand_S₂ : ContDiffOn ℝ 1 (fun r => -2 * B₁ r + r * B₁ r ^ 2) (Ioi 0) :=
  (contDiffOn_const.mul contDiffOn_B₁).add (contDiffOn_id.mul (contDiffOn_B₁.pow 2))

theorem contDiffOn_integrand_Ik (n : ℕ) : ContDiffOn ℝ 1 (fun r => B₁ r * r ^ n) (Ioi 0) :=
  contDiffOn_B₁.mul (contDiffOn_id.pow n)

theorem contDiffOn_S₁ : ContDiffOn ℝ 2 S₁ (Ioi 0) :=
  contDiffOn_primitive nearZero_S₁ contDiffOn_integrand_S₁

theorem contDiffOn_S₂ : ContDiffOn ℝ 2 S₂ (Ioi 0) :=
  contDiffOn_primitive nearZero_S₂ contDiffOn_integrand_S₂

/-- `I_k(t) = ∫₀ᵗ B₁ r^k dr`. -/
@[expose] noncomputable def Ik (n : ℕ) (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, B₁ r * r ^ n

theorem contDiffOn_Ik (n : ℕ) : ContDiffOn ℝ 2 (Ik n) (Ioi 0) :=
  contDiffOn_primitive (nearZero_Ik n) (contDiffOn_integrand_Ik n)

theorem hasDerivAt_Ik (n : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (Ik n) (B₁ t * t ^ n) t :=
  hasDerivAt_primitive (nearZero_Ik n) ht

theorem H_eq (n : ℕ) (t : ℝ) : H n t = (t ^ n)⁻¹ * Ik n t := rfl

theorem contDiffOn_H (n : ℕ) : ContDiffOn ℝ 2 (H n) (Ioi 0) := by
  have h : ContDiffOn ℝ 2 (fun t : ℝ => (t ^ n)⁻¹ * Ik n t) (Ioi 0) :=
    (ContDiffOn.inv (contDiffOn_id.pow n) fun x hx => pow_ne_zero n (ne_of_gt hx)).mul
      (contDiffOn_Ik n)
  exact h

/-- `H_k' = B₁ - (k/t) H_k`. -/
theorem hasDerivAt_H (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (H n) (B₁ t - n / t * H n t) t := by
  have h1 := (hasDerivAt_pow n t).inv (pow_ne_zero n ht.ne')
  have h2 := h1.mul (hasDerivAt_Ik n ht)
  refine h2.congr_deriv ?_
  simp only [Pi.inv_apply]
  rw [H_eq]
  rcases n with _ | m
  · simp
  · have hs : t ^ m ≠ 0 := pow_ne_zero m ht.ne'
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
    ring

end Calibration

end SandierSerfaty

end
