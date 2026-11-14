/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Jet2
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Jets of the integral functions `S₁, S₂, H_k` (paper `tail:H-estimate`)

The sector functions are integrals `t ↦ ∫₀ᵗ g` and `H_k(t) = t^{-k} ∫₀ᵗ g(r) r^k dr`. For an integrand `g` that is
continuous on `(0, ∞)` and bounded near `0` (`IntegrableNear0`):

* `intervalIntegrable_of_nearZero`, `hasDerivAt_integral_nearZero`, `jet_integral`: `∫₀ᵗ g` has the jet
  `(∫₀ᵗ g, g, g')`;
* `Hk g k t = t^{-k} ∫₀ᵗ g r^k` has the jet `(Hk, Hd1, Hd2)` with `H' = g - k H/t`,
  `H'' = g' - (k/t)(H' - H/t)` (paper §6.5, `jet_Hk`), and the bounds
  `|H| ≤ t G/(k+1)`, `|H'| ≤ 2G`, `|H''| ≤ |g'| + 2kG/t` for `|g| ≤ G` on `(0, t]` (`jn_Hk_le`).
-/

open Set Filter MeasureTheory

public section

namespace SandierSerfaty

namespace Tails

/-- Continuous on `(0, ∞)` and bounded near `0`. -/
@[expose] def NearZero (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Ioi 0) ∧ ∃ C δ : ℝ, 0 < δ ∧ ∀ r ∈ Ioc 0 δ, |g r| ≤ C

namespace NearZero

theorem add {g h : ℝ → ℝ} (hg : NearZero g) (hh : NearZero h) : NearZero (fun r => g r + h r) := by
  obtain ⟨c1, C1, δ1, d1, b1⟩ := hg
  obtain ⟨c2, C2, δ2, d2, b2⟩ := hh
  refine ⟨c1.add c2, C1 + C2, min δ1 δ2, lt_min d1 d2, fun r hr => ?_⟩
  have h1 := b1 r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have h2 := b2 r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem sub {g h : ℝ → ℝ} (hg : NearZero g) (hh : NearZero h) : NearZero (fun r => g r - h r) := by
  obtain ⟨c1, C1, δ1, d1, b1⟩ := hg
  obtain ⟨c2, C2, δ2, d2, b2⟩ := hh
  refine ⟨c1.sub c2, C1 + C2, min δ1 δ2, lt_min d1 d2, fun r hr => ?_⟩
  have h1 := b1 r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have h2 := b2 r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  exact (abs_sub _ _).trans (add_le_add h1 h2)

theorem const_mul (c : ℝ) {g : ℝ → ℝ} (hg : NearZero g) : NearZero (fun r => c * g r) := by
  obtain ⟨c1, C1, δ1, d1, b1⟩ := hg
  refine ⟨continuousOn_const.mul c1, |c| * C1, δ1, d1, fun r hr => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (b1 r hr) (abs_nonneg c)

theorem mul {g h : ℝ → ℝ} (hg : NearZero g) (hh : NearZero h) : NearZero (fun r => g r * h r) := by
  obtain ⟨c1, C1, δ1, d1, b1⟩ := hg
  obtain ⟨c2, C2, δ2, d2, b2⟩ := hh
  refine ⟨c1.mul c2, C1 * C2, min δ1 δ2, lt_min d1 d2, fun r hr => ?_⟩
  have h1 := b1 r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have h2 := b2 r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

theorem mul_pow_self {g : ℝ → ℝ} (hg : NearZero g) (k : ℕ) : NearZero (fun r => g r * r ^ k) := by
  obtain ⟨c1, C1, δ1, d1, b1⟩ := hg
  refine ⟨c1.mul (continuousOn_id.pow k), C1 * δ1 ^ k, δ1, d1, fun r hr => ?_⟩
  rw [abs_mul, abs_pow, abs_of_pos hr.1]
  exact mul_le_mul (b1 r hr) (pow_le_pow_left₀ hr.1.le hr.2 k) (pow_nonneg hr.1.le k) ((abs_nonneg _).trans (b1 r hr))

theorem id_mul {g : ℝ → ℝ} (hg : NearZero g) : NearZero (fun r => r * g r) := by
  have := (NearZero.mul_pow_self hg 1)
  simpa [mul_comm] using this

end NearZero

theorem intervalIntegrable_of_nearZero {g : ℝ → ℝ} (h : NearZero g) {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable g volume 0 t := by
  obtain ⟨hc, C, δ, hδ, hb⟩ := h
  set δ' := min δ t with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ ht
  have h1 : IntervalIntegrable g volume 0 δ' := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hδ'pos.le]
    have hm : AEStronglyMeasurable g (volume.restrict (Ioc 0 δ')) :=
      (hc.mono (fun r (hr : r ∈ Ioc 0 δ') => hr.1)).aestronglyMeasurable measurableSet_Ioc
    refine Integrable.mono' (g := fun _ => C) (integrableOn_const (by simp)) hm ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    simpa using hb r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hu : uIcc δ' t = Icc δ' t := uIcc_of_le (min_le_right δ t)
  have h2 : IntervalIntegrable g volume δ' t := by
    refine ContinuousOn.intervalIntegrable (hc.mono fun r hr => ?_)
    rw [hu] at hr
    exact lt_of_lt_of_le hδ'pos hr.1
  exact h1.trans h2

theorem hasDerivAt_integral_nearZero {g : ℝ → ℝ} (h : NearZero g) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, g r) (g t) t := by
  have hc : ContinuousAt g t := h.1.continuousAt (Ioi_mem_nhds ht)
  have hm : StronglyMeasurableAtFilter g (nhds t) volume :=
    h.1.stronglyMeasurableAtFilter isOpen_Ioi t ht
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_of_nearZero h ht) hm hc

theorem jet_integral {g g₁ : ℝ → ℝ} (h : NearZero g) (hg : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g₁ x) x) :
    Jet2 (Ioi 0) (Ioi 0) (fun x => ∫ r in (0 : ℝ)..x, g r) g g₁ :=
  ⟨fun _ hx => hasDerivAt_integral_nearZero h hx, hg, subset_rfl⟩

/-! ### `H_k(t) = t^{-k} ∫₀ᵗ g r^k dr` -/

/-- `H_k[g](t) = t^{-k} ∫₀ᵗ g(r) r^k dr` (paper `cal:radial-integrals`; `Calibration.H k = Hk B₁ k`). -/
@[expose] noncomputable def Hk (g : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (t ^ k)⁻¹ * ∫ r in (0 : ℝ)..t, g r * r ^ k

/-- `H_k' = g - k H_k/t` (paper §6.5). -/
@[expose] noncomputable def Hd1 (g : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ := g t - (k : ℝ) * Hk g k t / t

/-- `H_k'' = g' - k H_k'/t + k H_k/t²`. -/
@[expose] noncomputable def Hd2 (g g₁ : ℝ → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  g₁ t - (k : ℝ) * Hd1 g k t / t + (k : ℝ) * Hk g k t / t ^ 2

theorem hasDerivAt_inv_pow (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => (t ^ k)⁻¹) (-(k : ℝ) * (t ^ k)⁻¹ / t) t := by
  cases k with
  | zero => simpa using hasDerivAt_const t (1 : ℝ)
  | succ n =>
    have h := (hasDerivAt_pow (n + 1) t).inv (pow_ne_zero _ ht)
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem jet_Hk {g g₁ : ℝ → ℝ} (h : NearZero g) (hg : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g₁ x) x) (k : ℕ) :
    Jet2 (Ioi 0) (Ioi 0) (Hk g k) (Hd1 g k) (Hd2 g g₁ k) := by
  have hI := (h.mul_pow_self k)
  refine ⟨fun x hx => ?_, fun x hx => ?_, subset_rfl⟩
  · have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 := hasDerivAt_integral_nearZero hI hx
    have h2 := (hasDerivAt_inv_pow k hx0).mul h1
    refine h2.congr_deriv ?_
    unfold Hd1 Hk
    have : x ^ k ≠ 0 := pow_ne_zero _ hx0
    field_simp
    ring
  · have hx0 : x ≠ 0 := ne_of_gt hx
    have hH : HasDerivAt (Hk g k) (Hd1 g k x) x := by
      have h1 := hasDerivAt_integral_nearZero hI hx
      have h2 := (hasDerivAt_inv_pow k hx0).mul h1
      refine h2.congr_deriv ?_
      unfold Hd1 Hk
      have : x ^ k ≠ 0 := pow_ne_zero _ hx0
      field_simp
      ring
    have h3 : HasDerivAt (fun t => (k : ℝ) * Hk g k t / t) ((k : ℝ) * (Hd1 g k x * x - Hk g k x) / x ^ 2) x := by
      have := ((hH.const_mul (k : ℝ)).div (hasDerivAt_id' x) hx0)
      refine this.congr_deriv ?_
      field_simp
    have h4 := (hg x hx).sub h3
    refine h4.congr_deriv ?_
    unfold Hd2
    field_simp
    ring

theorem abs_Hk_le {g : ℝ → ℝ} (_h : NearZero g) (k : ℕ) {t G : ℝ} (ht : 0 < t)
    (hG : ∀ r ∈ Ioc 0 t, |g r| ≤ G) : |Hk g k t| ≤ t * G / ((k : ℝ) + 1) := by
  have hI : IntervalIntegrable (fun r : ℝ => G * r ^ k) volume 0 t :=
    (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
  have h1 : ‖∫ r in (0 : ℝ)..t, g r * r ^ k‖ ≤ ∫ r in (0 : ℝ)..t, G * r ^ k := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht.le (Filter.Eventually.of_forall fun r hr => ?_) hI
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hr.1]
    exact mul_le_mul_of_nonneg_right (hG r hr) (pow_nonneg hr.1.le k)
  rw [intervalIntegral.integral_const_mul, integral_pow] at h1
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have htk : 0 < t ^ k := pow_pos ht k
  unfold Hk
  rw [abs_mul, abs_inv, abs_of_pos htk]
  rw [Real.norm_eq_abs] at h1
  calc (t ^ k)⁻¹ * |∫ r in (0 : ℝ)..t, g r * r ^ k|
      ≤ (t ^ k)⁻¹ * (G * ((t ^ (k + 1) - 0 ^ (k + 1)) / ((k : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = t * G / ((k : ℝ) + 1) := by
        rw [zero_pow (Nat.succ_ne_zero k)]
        field_simp
        ring

/-- **The `H_k` estimate** (paper §6.5): if `|g| ≤ G` on `(0, t]`, then
`|H_k|_{2,t} ≤ t G/(k+1) + 2G + |g'(t)|/2 + k G/t`. -/
theorem jn_Hk_le {g g₁ : ℝ → ℝ} (h : NearZero g) (k : ℕ) {t G : ℝ} (ht : 0 < t)
    (hG : ∀ r ∈ Ioc 0 t, |g r| ≤ G) :
    jn (Hk g k) (Hd1 g k) (Hd2 g g₁ k) t ≤
      t * G / ((k : ℝ) + 1) + 2 * G + |g₁ t| / 2 + (k : ℝ) * G / t := by
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG t ⟨ht, le_rfl⟩)
  have hH := abs_Hk_le h k ht hG
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hgt := hG t ⟨ht, le_rfl⟩
  -- (k+1) H / t is bounded by G
  have hkH : |((k : ℝ) + 1) * Hk g k t / t| ≤ G := by
    rw [abs_div, abs_mul, abs_of_pos hk1, abs_of_pos ht, div_le_iff₀ ht]
    calc ((k : ℝ) + 1) * |Hk g k t| ≤ ((k : ℝ) + 1) * (t * G / ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hH hk1.le
      _ = G * t := by field_simp
  have hkH' : |(k : ℝ) * Hk g k t / t| ≤ G := by
    rw [abs_div, abs_mul, abs_of_nonneg hk0, abs_of_pos ht, div_le_iff₀ ht]
    calc (k : ℝ) * |Hk g k t| ≤ ((k : ℝ) + 1) * (t * G / ((k : ℝ) + 1)) :=
          mul_le_mul (by linarith) hH (abs_nonneg _) hk1.le
      _ = G * t := by field_simp
  have h1 : |Hd1 g k t| ≤ 2 * G := by
    unfold Hd1
    have := abs_sub (g t) ((k : ℝ) * Hk g k t / t)
    linarith
  have h2 : |Hd1 g k t - Hk g k t / t| ≤ 2 * G := by
    have e : Hd1 g k t - Hk g k t / t = g t - ((k : ℝ) + 1) * Hk g k t / t := by
      unfold Hd1; ring
    rw [e]
    have := abs_sub (g t) (((k : ℝ) + 1) * Hk g k t / t)
    linarith
  have h3 : |Hd2 g g₁ k t| ≤ |g₁ t| + 2 * (k : ℝ) * G / t := by
    have e : Hd2 g g₁ k t = g₁ t - (k : ℝ) / t * (Hd1 g k t - Hk g k t / t) := by
      unfold Hd2; field_simp; ring
    rw [e]
    refine (abs_sub _ _).trans (add_le_add_right ?_ _)
    rw [abs_mul, abs_div, abs_of_nonneg hk0, abs_of_pos ht]
    calc (k : ℝ) / t * |Hd1 g k t - Hk g k t / t| ≤ (k : ℝ) / t * (2 * G) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * (k : ℝ) * G / t := by ring
  unfold jn
  have : |Hd2 g g₁ k t| / 2 ≤ |g₁ t| / 2 + (k : ℝ) * G / t := by
    have : 2 * (k : ℝ) * G / t / 2 = (k : ℝ) * G / t := by ring
    linarith [h3, show |Hd2 g g₁ k t| / 2 ≤ (|g₁ t| + 2 * (k : ℝ) * G / t) / 2 by linarith]
  linarith

end Tails

end SandierSerfaty

end
