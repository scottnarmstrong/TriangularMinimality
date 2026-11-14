/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.WeylCalculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic cutoffs around a point of `ℂ`

A point has zero capacity in the plane. Quantitatively: for `0 < k` the function
`η k c z = Theta k (‖z - c‖²)`, where `Theta k s = θ (-(k log s))` for `s > 0` and `θ` is a smooth
transition from `0` (on `(-∞, 1]`) to `1` (on `[2, ∞)`), is smooth, equals `1` on
`‖z - c‖ ≤ exp (-1/k)`, vanishes for `‖z - c‖ ≥ exp (-1/(2k))`, and

* `|Δ η| ≤ 4 k² B / ‖z - c‖²`,
* `|∂_v η| ≤ 2 k A / ‖z - c‖`,

both supported in the annulus `exp (-1/k) ≤ ‖z - c‖ ≤ exp (-1/(2k))`, where `A, B` bound `θ'`, `θ''`.
Since `∫ 1/‖z-c‖²` over the annulus is a constant multiple of `1/k`, the `L¹` norm of `Δ η`
is `O(k)`: this is the capacity estimate used in `SandierSerfaty.Analysis.RemovableSingularity`.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- The smooth transition from `0` on `(-∞, 1]` to `1` on `[2, ∞)`. -/
@[expose] noncomputable def theta (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem contDiff_theta : ContDiff ℝ ∞ theta :=
  Real.smoothTransition.contDiff (n := ⊤) |>.comp (contDiff_id.sub contDiff_const)

theorem theta_nonneg (t : ℝ) : 0 ≤ theta t := Real.smoothTransition.nonneg _
theorem theta_le_one (t : ℝ) : theta t ≤ 1 := Real.smoothTransition.le_one _
theorem theta_eq_zero {t : ℝ} (h : t ≤ 1) : theta t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem theta_eq_one {t : ℝ} (h : 2 ≤ t) : theta t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem deriv_theta_eq_zero {t : ℝ} (h : t < 1 ∨ 2 < t) : deriv theta t = 0 := by
  rcases h with h | h
  · have : theta =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs using theta_eq_zero (le_of_lt hs)
    rw [this.deriv_eq]; simp
  · have : theta =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with s hs using theta_eq_one (le_of_lt hs)
    rw [this.deriv_eq]; simp

theorem deriv_deriv_theta_eq_zero {t : ℝ} (h : t < 1 ∨ 2 < t) : deriv (deriv theta) t = 0 := by
  have : deriv theta =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    rcases h with h | h
    · filter_upwards [Iio_mem_nhds h] with s hs using deriv_theta_eq_zero (Or.inl hs)
    · filter_upwards [Ioi_mem_nhds h] with s hs using deriv_theta_eq_zero (Or.inr hs)
  rw [this.deriv_eq]; simp

theorem exists_theta_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ t, |deriv theta t| ≤ A ∧ |deriv (deriv theta) t| ≤ B := by
  have hd1 : ContDiff ℝ ∞ (deriv theta) := by
    have := (contDiff_infty_iff_deriv.1 contDiff_theta).2
    exact this
  have hd2 : ContDiff ℝ ∞ (deriv (deriv theta)) := (contDiff_infty_iff_deriv.1 hd1).2
  have hcs1 : HasCompactSupport (deriv theta) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun t ht => ?_
    exact deriv_theta_eq_zero (by simp only [mem_Icc, not_and_or, not_le] at ht; tauto)
  have hcs2 : HasCompactSupport (deriv (deriv theta)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun t ht => ?_
    exact deriv_deriv_theta_eq_zero (by simp only [mem_Icc, not_and_or, not_le] at ht; tauto)
  obtain ⟨A, hA⟩ := hcs1.exists_bound_of_continuous hd1.continuous
  obtain ⟨B, hB⟩ := hcs2.exists_bound_of_continuous hd2.continuous
  refine ⟨max A 0, max B 0, le_max_right _ _, le_max_right _ _, fun t => ⟨?_, ?_⟩⟩
  · have := hA t
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have := hB t
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The radial profile of the cutoff, `Theta k s = θ (-(k log s))` for `s > 0` and `1` for `s ≤ 0`. -/
@[expose] noncomputable def Theta (k s : ℝ) : ℝ := if s ≤ 0 then 1 else theta (-(k * Real.log s))

theorem Theta_of_pos {k s : ℝ} (hs : 0 < s) : Theta k s = theta (-(k * Real.log s)) := by
  simp [Theta, not_le.mpr hs]

theorem Theta_eq_one {k s : ℝ} (hk : 0 < k) (hs : s ≤ Real.exp (-2 / k)) : Theta k s = 1 := by
  by_cases h0 : s ≤ 0
  · simp [Theta, h0]
  · rw [Theta_of_pos (not_le.mp h0)]
    apply theta_eq_one
    have : Real.log s ≤ -2 / k := by
      rw [Real.log_le_iff_le_exp (not_le.mp h0)]; exact hs
    have := mul_le_mul_of_nonneg_left this hk.le
    rw [mul_div_cancel₀ _ hk.ne'] at this
    linarith

theorem Theta_eq_zero {k s : ℝ} (hk : 0 < k) (hs : Real.exp (-1 / k) ≤ s) : Theta k s = 0 := by
  have hs0 : 0 < s := lt_of_lt_of_le (Real.exp_pos _) hs
  rw [Theta_of_pos hs0]
  apply theta_eq_zero
  have : -1 / k ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hs0]; exact hs
  have := mul_le_mul_of_nonneg_left this hk.le
  rw [mul_div_cancel₀ _ hk.ne'] at this
  linarith

theorem contDiff_Theta {k : ℝ} (hk : 0 < k) : ContDiff ℝ ∞ (Theta k) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : 0 < s
  · have hev : Theta k =ᶠ[𝓝 s] fun t => theta (-(k * Real.log t)) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using Theta_of_pos ht
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact contDiff_theta.contDiffAt.comp s
      ((contDiffAt_const.mul (Real.contDiffAt_log.2 hs.ne')).neg)
  · have hev : Theta k =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt (not_lt.mp hs) (Real.exp_pos (-2 / k)))]
        with t ht using Theta_eq_one hk (le_of_lt ht)
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem Theta_nonneg (k s : ℝ) : 0 ≤ Theta k s := by
  unfold Theta; split_ifs
  · exact zero_le_one
  · exact theta_nonneg _

theorem Theta_le_one (k s : ℝ) : Theta k s ≤ 1 := by
  unfold Theta; split_ifs
  · exact le_rfl
  · exact theta_le_one _

/-- First derivative of the profile for `s > 0`. -/
theorem deriv_Theta {k s : ℝ} (hs : 0 < s) :
    deriv (Theta k) s = deriv theta (-(k * Real.log s)) * (-(k / s)) := by
  have hev : Theta k =ᶠ[𝓝 s] fun t => theta (-(k * Real.log t)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht using Theta_of_pos ht
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun t => -(k * Real.log t)) (-(k / s)) s := by
    have := ((Real.hasDerivAt_log hs.ne').const_mul k).neg
    convert this using 1
    simp [div_eq_mul_inv]
  have hth : HasDerivAt theta (deriv theta (-(k * Real.log s))) (-(k * Real.log s)) :=
    ((contDiff_theta.differentiable (by norm_num)) _).hasDerivAt
  exact (hth.comp s hg).deriv

/-- Second derivative of the profile for `s > 0`. -/
theorem deriv_deriv_Theta {k s : ℝ} (hs : 0 < s) :
    deriv (deriv (Theta k)) s =
      deriv (deriv theta) (-(k * Real.log s)) * (k / s) ^ 2 + deriv theta (-(k * Real.log s)) * (k / s ^ 2) := by
  have hev : deriv (Theta k) =ᶠ[𝓝 s] fun t => deriv theta (-(k * Real.log t)) * (-(k / t)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht using deriv_Theta ht
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun t => -(k * Real.log t)) (-(k / s)) s := by
    have := ((Real.hasDerivAt_log hs.ne').const_mul k).neg
    convert this using 1
    simp [div_eq_mul_inv]
  have hd1 : ContDiff ℝ ∞ (deriv theta) := (contDiff_infty_iff_deriv.1 contDiff_theta).2
  have hth : HasDerivAt (deriv theta) (deriv (deriv theta) (-(k * Real.log s)))
      (-(k * Real.log s)) := ((hd1.differentiable (by norm_num)) _).hasDerivAt
  have h1 := hth.comp s hg
  have h2 : HasDerivAt (fun t : ℝ => -(k / t)) (k / s ^ 2) s := by
    have := (hasDerivAt_inv hs.ne').const_mul k |>.neg
    simp only [← div_eq_mul_inv] at this
    convert this using 1
    field_simp
  have h3 : HasDerivAt (fun t => deriv theta (-(k * Real.log t)) * -(k / t)) _ s := h1.mul h2
  rw [h3.deriv]
  simp only [Function.comp]
  field_simp

/-- The cutoff `η k c z = Theta k (‖z - c‖²)`. -/
@[expose] noncomputable def eta (k : ℝ) (c z : ℂ) : ℝ := Theta k (‖z - c‖ ^ 2)

theorem contDiff_eta {k : ℝ} (hk : 0 < k) (c : ℂ) : ContDiff ℝ ∞ (eta k c) :=
  contDiff_comp_normSq_sub (contDiff_Theta hk) c

theorem eta_eq_one {k : ℝ} (hk : 0 < k) {c z : ℂ} (hz : ‖z - c‖ ≤ Real.exp (-1 / k)) :
    eta k c z = 1 := by
  apply Theta_eq_one hk
  have h0 : 0 ≤ ‖z - c‖ := norm_nonneg _
  calc ‖z - c‖ ^ 2 ≤ Real.exp (-1 / k) ^ 2 := by gcongr
    _ = Real.exp (-2 / k) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem eta_eq_zero {k : ℝ} (hk : 0 < k) {c z : ℂ} (hz : Real.exp (-1 / (2 * k)) ≤ ‖z - c‖) :
    eta k c z = 0 := by
  apply Theta_eq_zero hk
  calc Real.exp (-1 / k) = Real.exp (-1 / (2 * k)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
    _ ≤ ‖z - c‖ ^ 2 := by gcongr

/-- The annulus `exp (-1/k) ≤ ‖z - c‖ ≤ exp (-1/(2k))`, as an interval of radii. -/
@[expose] noncomputable def Lam (k y : ℝ) : ℝ :=
  (Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))).indicator (fun y => k ^ 2 * (y ^ 2)⁻¹) y

theorem Lam_nonneg (k y : ℝ) : 0 ≤ Lam k y := by
  unfold Lam
  exact Set.indicator_nonneg (fun y _ => by positivity) y

theorem exp_neg_inv_le {k : ℝ} (hk : 0 < k) : Real.exp (-1 / (2 * k)) ≤ k := by
  have hx : 0 ≤ 1 / (2 * k) := by positivity
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : 2 * (1 / (2 * k)) ≤ Real.exp (1 / (2 * k)) := by
    nlinarith [sq_nonneg (1 / (2 * k) - 1)]
  have h3 : Real.exp (-1 / (2 * k)) = (Real.exp (1 / (2 * k)))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h3, inv_le_comm₀ (Real.exp_pos _) hk]
  calc k⁻¹ = 2 * (1 / (2 * k)) := by field_simp
    _ ≤ _ := h2

/-- Outside the annulus the profile `theta` has vanishing first and second derivatives. -/
theorem deriv_theta_comp_eq_zero {k y : ℝ} (hk : 0 < k) (hy : 0 < y)
    (hn : y ∉ Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))) :
    (-(k * Real.log (y ^ 2)) < 1 ∨ 2 < -(k * Real.log (y ^ 2))) := by
  simp only [mem_Icc, not_and_or, not_le] at hn
  have hy2 : 0 < y ^ 2 := by positivity
  rcases hn with h | h
  · right
    have h1 : y ^ 2 < Real.exp (-2 / k) := by
      calc y ^ 2 < Real.exp (-1 / k) ^ 2 := by gcongr
        _ = Real.exp (-2 / k) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h2 : Real.log (y ^ 2) < -2 / k := by
      rw [Real.log_lt_iff_lt_exp hy2]; exact h1
    have := mul_lt_mul_of_pos_left h2 hk
    rw [mul_div_cancel₀ _ hk.ne'] at this
    linarith
  · left
    have h1 : Real.exp (-1 / k) < y ^ 2 := by
      calc Real.exp (-1 / k) = Real.exp (-1 / (2 * k)) ^ 2 := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
        _ < y ^ 2 := by gcongr
    have h2 : -1 / k < Real.log (y ^ 2) := by
      rw [Real.lt_log_iff_exp_lt hy2]; exact h1
    have := mul_lt_mul_of_pos_left h2 hk
    rw [mul_div_cancel₀ _ hk.ne'] at this
    linarith

/-- `|Δ η| ≤ 4 B k² / ‖z - c‖²` on the annulus, and `Δ η = 0` off it. -/
theorem abs_lap_eta_le {k : ℝ} (hk : 0 < k) {B : ℝ} (hB : ∀ t, |deriv (deriv theta) t| ≤ B)
    {c z : ℂ} (hz : z ≠ c) : |Δ (eta k c) z| ≤ 4 * B * Lam k ‖z - c‖ := by
  have hr : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hs : 0 < ‖z - c‖ ^ 2 := by positivity
  have hT : ContDiff ℝ 2 (Theta k) := (contDiff_Theta hk).of_le (by norm_num)
  have hL : Δ (eta k c) z = 4 * deriv (deriv theta) (-(k * Real.log (‖z - c‖ ^ 2))) * k ^ 2
      / ‖z - c‖ ^ 2 := by
    unfold eta
    rw [lap_comp_normSq_sub hT c z, deriv_deriv_Theta hs, deriv_Theta hs]
    field_simp
    ring
  rw [hL]
  by_cases hn : ‖z - c‖ ∈ Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))
  · have hLam : Lam k ‖z - c‖ = k ^ 2 * (‖z - c‖ ^ 2)⁻¹ := by
      unfold Lam; rw [Set.indicator_of_mem hn]
    rw [hLam, abs_div, abs_of_pos hs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < k ^ 2)]
    rw [div_le_iff₀ hs]
    have := hB (-(k * Real.log (‖z - c‖ ^ 2)))
    have h4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
    rw [h4]
    calc 4 * |deriv (deriv theta) (-(k * Real.log (‖z - c‖ ^ 2)))| * k ^ 2
        ≤ 4 * B * k ^ 2 := by gcongr
      _ = 4 * B * (k ^ 2 * (‖z - c‖ ^ 2)⁻¹) * ‖z - c‖ ^ 2 := by field_simp
  · have hLam : Lam k ‖z - c‖ = 0 := by unfold Lam; rw [Set.indicator_of_notMem hn]
    rw [hLam, deriv_deriv_theta_eq_zero (deriv_theta_comp_eq_zero hk hr hn)]
    simp

/-- `|∂_v η| ≤ 2 A k² / ‖z - c‖²` on the annulus (`‖v‖ = 1`), and `∂_v η = 0` off it. -/
theorem abs_pd_eta_le {k : ℝ} (hk : 0 < k) {A : ℝ} (hA : ∀ t, |deriv theta t| ≤ A)
    {c z : ℂ} (hz : z ≠ c) {v : ℂ} (hv : ‖v‖ = 1) :
    |pd v (eta k c) z| ≤ 2 * A * Lam k ‖z - c‖ := by
  have hr : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hs : 0 < ‖z - c‖ ^ 2 := by positivity
  have hT : Differentiable ℝ (Theta k) := (contDiff_Theta hk).differentiable (by norm_num)
  have hL : pd v (eta k c) z = deriv theta (-(k * Real.log (‖z - c‖ ^ 2))) *
      (-(k / ‖z - c‖ ^ 2)) * (2 * inner ℝ v (z - c)) := by
    unfold eta
    rw [pd_comp_normSq hT c v]
    show deriv (Theta k) (‖z - c‖ ^ 2) * (2 * inner ℝ v (z - c)) = _
    rw [deriv_Theta hs]
  rw [hL]
  by_cases hn : ‖z - c‖ ∈ Icc (Real.exp (-1 / k)) (Real.exp (-1 / (2 * k)))
  · have hLam : Lam k ‖z - c‖ = k ^ 2 * (‖z - c‖ ^ 2)⁻¹ := by
      unfold Lam; rw [Set.indicator_of_mem hn]
    have hrk : ‖z - c‖ ≤ k := hn.2.trans (exp_neg_inv_le hk)
    have hin : |inner ℝ v (z - c)| ≤ ‖z - c‖ := by
      have := abs_real_inner_le_norm v (z - c)
      rwa [hv, one_mul] at this
    have hA' := hA (-(k * Real.log (‖z - c‖ ^ 2)))
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
    have hkr : 1 ≤ k / ‖z - c‖ := by rw [le_div_iff₀ hr]; linarith
    have hid : k ^ 2 * (‖z - c‖ ^ 2)⁻¹ = (k / ‖z - c‖) * (k / ‖z - c‖) := by field_simp
    rw [hLam, abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hk, abs_of_pos hs,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc |deriv theta (-(k * Real.log (‖z - c‖ ^ 2)))| * (k / ‖z - c‖ ^ 2) *
          (2 * |inner ℝ v (z - c)|)
        ≤ A * (k / ‖z - c‖ ^ 2) * (2 * ‖z - c‖) := by gcongr
      _ = 2 * A * (k / ‖z - c‖) := by field_simp
      _ ≤ 2 * A * (k ^ 2 * (‖z - c‖ ^ 2)⁻¹) := by
          rw [hid]
          gcongr
          exact le_mul_of_one_le_right (by linarith) hkr
  · have hLam : Lam k ‖z - c‖ = 0 := by unfold Lam; rw [Set.indicator_of_notMem hn]
    rw [hLam, deriv_theta_eq_zero (deriv_theta_comp_eq_zero hk hr hn)]
    simp

end SandierSerfaty.Weyl

end
