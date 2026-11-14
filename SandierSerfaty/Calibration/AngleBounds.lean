/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.AnglePolar
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Bounds for the trial potential and its energy density on the model sector

Paper `cal:trial-potential`. On `S = S(d, α, β)` (`secRadius d α β = T₀`):

* `bound_H`: `‖w‖ |H(w)| ≤ C` (the potential has a logarithmic singularity at the apex);
* `bound_rest`: `|restSq d w| ≤ C` (the non-singular part of `|∇H|²` is bounded);
* `bound_radial_sq`: `B'(‖w‖)² ≤ C` on `S ∩ {‖w‖ > η}`.

The coefficient sums `∑|Dᵢ(t)|, ∑|kᵢ Dᵢ(t)|, ∑|Qᵢ(t)|` are bounded uniformly for `t ∈ [d, T₀]` by
`∑ Mᵢ`, `∑ Mᵢ`, `2 ∑ Mᵢ`, with `M` the majorant of `Bnd` (`radialData_isAdmissible`).
-/

open Set Filter Topology MeasureTheory Real

public section

namespace SandierSerfaty

namespace Calibration

open SandierSerfaty.Dual

section Data

variable {d T : ℝ} {M : ℕ → ℝ}

theorem abs_Q_le_of_bnd (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) (i : ℕ) :
    |Q i t| ≤ 2 * M i := by
  have h1 := hM.t_mul_abs_deriv_le i ht
  have h2 := hM.k_mul_abs_D_le hd i ht
  unfold Q
  calc |t * deriv (D i) t - (k i : ℝ) * D i t| ≤ |t * deriv (D i) t| + |(k i : ℝ) * D i t| := abs_sub _ _
    _ ≤ M i + M i := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]; exact h1
        · rw [abs_mul, Nat.abs_cast]; exact h2
    _ = 2 * M i := by ring

theorem abs_kD_le (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) (i : ℕ) :
    |(k i : ℝ) * D i t| ≤ M i := by
  rw [abs_mul, Nat.abs_cast]; exact hM.k_mul_abs_D_le hd i ht

theorem summable_abs_D' (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) :
    Summable fun i => |D i t| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => hM.abs_D_le hd i ht) hM.summable

theorem tsum_abs_D_le (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) :
    ∑' i, |D i t| ≤ ∑' i, M i :=
  (summable_abs_D' hM hd ht).tsum_le_tsum (fun i => hM.abs_D_le hd i ht) hM.summable

theorem summable_abs_kD (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) :
    Summable fun i => |(k i : ℝ) * D i t| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => abs_kD_le hM hd ht i) hM.summable

theorem tsum_abs_kD_le (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) :
    ∑' i, |(k i : ℝ) * D i t| ≤ ∑' i, M i :=
  (summable_abs_kD hM hd ht).tsum_le_tsum (fun i => abs_kD_le hM hd ht i) hM.summable

theorem tsum_abs_Q_le_of_bnd (hM : Bnd radialData d T M) (hd : 0 < d) {t : ℝ} (ht : t ∈ Icc d T) :
    ∑' i, |Q i t| ≤ 2 * ∑' i, M i := by
  rw [← tsum_mul_left]
  exact (summable_abs_Q (lt_of_lt_of_le hd ht.1)).tsum_le_tsum (fun i => abs_Q_le_of_bnd hM hd ht i)
    (hM.summable.mul_left 2)

end Data

/-- `r |B(r)|` is bounded on `(0, T]`. -/
theorem exists_rB_bound (T : ℝ) : ∃ C : ℝ, ∀ r ∈ Ioc 0 T, r * |B r| ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := near_zero_bounds
  have hsub : Icc (1 / 4 : ℝ) T ⊆ Ioi 0 := fun r hr => lt_of_lt_of_le (by norm_num) hr.1
  obtain ⟨C₁, h₁⟩ := (isCompact_Icc (a := (1 / 4 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuousOn_B.mono hsub)
  refine ⟨max (1 + C₀) (|T| * |C₁|), fun r hr => ?_⟩
  by_cases h : r ≤ 1 / 4
  · refine le_max_of_le_left ?_
    have h2 := (h₀ r ⟨hr.1, h⟩).2
    have hl := Real.abs_log_mul_self_lt r hr.1 (by linarith)
    have : r * |B r| ≤ r * (|Real.log r| + C₀) := mul_le_mul_of_nonneg_left h2 hr.1.le
    have e : r * |Real.log r| = |Real.log r * r| := by rw [abs_mul, abs_of_pos hr.1]; ring
    nlinarith [hr.1, hr.2]
  · push Not at h
    refine le_max_of_le_right ?_
    have := h₁ r ⟨h.le, hr.2⟩
    rw [Real.norm_eq_abs] at this
    have hr0 : 0 ≤ r := hr.1.le
    calc r * |B r| ≤ |T| * |C₁| := by
          refine mul_le_mul ?_ (this.trans (le_abs_self C₁)) (abs_nonneg _) (abs_nonneg _)
          exact hr.2.trans (le_abs_self T)
      _ = |T| * |C₁| := rfl

theorem tφ_mem_T₁ {d α β φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hφ : φ ∈ Ioo (-α) β) : Tφ d φ ∈ Icc d (secRadius d α β + 1) :=
  ⟨(Tφ_mem hd hα hβ hφ).1, (Tφ_mem hd hα hβ hφ).2.trans (by linarith)⟩

/-- A radius on a ray of the sector is below `secRadius`. -/
theorem r_le_secRadius {d α β r φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hφ : φ ∈ Ioo (-α) β) (hrt : r * Real.cos φ < d) : r ≤ secRadius d α β :=
  (((lt_Tφ_iff hα hβ hφ).1 hrt).le).trans (Tφ_mem hd hα hβ hφ).2

/-- `‖w‖ |H(w)|` is bounded on the sector. -/
theorem bound_H {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    ∃ C : ℝ, ∀ w ∈ modelSector d α β, ‖w‖ * |modelH radialData d w| ≤ C := by
  obtain ⟨M, hM⟩ := exists_bnd_model hd hα hβ
  obtain ⟨CB, hCB⟩ := exists_rB_bound (secRadius d α β)
  set K : ℝ := ∑' i, M i with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun i => hM.nonneg hd (by linarith [d_le_secRadius hd hα hβ]) i
  have hT0 := secRadius_pos hd hα hβ
  refine ⟨CB + secRadius d α β * K, fun w hw => ?_⟩
  obtain ⟨r, φ, hr, hφ, hrt, rfl⟩ := exists_polar_rep hα hβ hw
  have hrT := r_le_secRadius hd hα hβ hφ hrt
  have hTt := (lt_Tφ_iff hα hβ hφ).1 hrt
  have hts := tφ_mem_T₁ hd hα hβ hφ
  rw [polarCoord_symm_norm (x := (r, φ)) hr, modelH_polar hd hα hβ hr hφ hrt]
  simp only
  have hser := abs_ser_le (summable_abs_D' hM hd hts) (Tφ_pos hd hα hβ hφ) hr.le hTt.le
  have hq0 : 0 ≤ r / Tφ d φ := div_nonneg hr.le (Tφ_pos hd hα hβ hφ).le
  have hq1 : r / Tφ d φ ≤ 1 := (div_le_one (Tφ_pos hd hα hβ hφ)).2 hTt.le
  have hser' : |ser (fun i => D i (Tφ d φ)) (Tφ d φ) r| ≤ K := by
    refine hser.trans ?_
    calc (r / Tφ d φ) ^ 6 * ∑' i, |D i (Tφ d φ)| ≤ 1 * K :=
          mul_le_mul (pow_le_one₀ hq0 hq1) (tsum_abs_D_le hM hd hts) (tsum_nonneg fun i => abs_nonneg _)
            zero_le_one
      _ = K := one_mul _
  calc r * |B r + ser (fun i => D i (Tφ d φ)) (Tφ d φ) r|
      ≤ r * (|B r| + |ser (fun i => D i (Tφ d φ)) (Tφ d φ) r|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hr.le
    _ = r * |B r| + r * |ser (fun i => D i (Tφ d φ)) (Tφ d φ) r| := by ring
    _ ≤ CB + secRadius d α β * K := add_le_add (hCB r ⟨hr, hrT⟩)
        (mul_le_mul hrT hser' (abs_nonneg _) hT0.le)

/-- `B'(‖w‖)²` is bounded on the sector away from the apex. -/
theorem bound_radial_sq {d α β η : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hη : 0 < η) :
    ∃ C : ℝ, ∀ w ∈ modelSector d α β, η < ‖w‖ → (deriv B ‖w‖) ^ 2 ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_B₁_bound (secRadius d α β)
  refine ⟨(C₁ + 1 / η) ^ 2, fun w hw hηw => ?_⟩
  obtain ⟨r, φ, hr, hφ, hrt, rfl⟩ := exists_polar_rep hα hβ hw
  have hrT := r_le_secRadius hd hα hβ hφ hrt
  rw [polarCoord_symm_norm (x := (r, φ)) hr] at hηw ⊢
  have h1 := hC₁ r ⟨hr, hrT⟩
  have h2 : deriv B r = B₁ r - 1 / r := by unfold B₁; ring
  have h3 : 1 / r ≤ 1 / η := one_div_le_one_div_of_le hη hηw.le
  have h4 : |deriv B r| ≤ C₁ + 1 / η := by
    rw [h2]
    calc |B₁ r - 1 / r| ≤ |B₁ r| + |1 / r| := abs_sub _ _
      _ ≤ C₁ + 1 / η := by rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / r)]; linarith
  calc (deriv B r) ^ 2 = |deriv B r| ^ 2 := (sq_abs _).symm
    _ ≤ (C₁ + 1 / η) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2

theorem tan_sq_le {d α β φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hφ : φ ∈ Ioo (-α) β) : Real.tan φ ^ 2 ≤ (secRadius d α β / d) ^ 2 := by
  have hc := cos_pos_of_mem hα hβ hφ
  have hT := Tφ_mem hd hα hβ hφ
  have h1 : Real.tan φ ^ 2 ≤ (1 / Real.cos φ) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, div_pow, one_div, inv_pow, ← one_div]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.sin_sq_add_cos_sq φ]) (by positivity)
  refine h1.trans ?_
  have : 1 / Real.cos φ = Tφ d φ / d := by unfold Tφ; field_simp
  rw [this]
  exact pow_le_pow_left₀ (by have := (Tφ_pos hd hα hβ hφ); positivity)
    (div_le_div_of_nonneg_right hT.2 hd.le) 2

/-- The non-singular part of the energy density is bounded on the sector. -/
theorem bound_rest {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    ∃ C : ℝ, ∀ w ∈ modelSector d α β, |restSq d w| ≤ C := by
  obtain ⟨M, hM⟩ := exists_bnd_model hd hα hβ
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_B₁_bound (secRadius d α β)
  set K : ℝ := ∑' i, M i with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun i => hM.nonneg hd (by linarith [d_le_secRadius hd hα hβ]) i
  have hT0 := secRadius_pos hd hα hβ
  refine ⟨2 * (C₁ * (K / d) + K / d ^ 2) + (K / d) ^ 2 + (secRadius d α β / d) ^ 2 * (2 * K / d) ^ 2,
    fun w hw => ?_⟩
  obtain ⟨r, φ, hr, hφ, hrt, rfl⟩ := exists_polar_rep hα hβ hw
  have hrT := r_le_secRadius hd hα hβ hφ hrt
  have hTt := (lt_Tφ_iff hα hβ hφ).1 hrt
  have hts := tφ_mem_T₁ hd hα hβ hφ
  have htpos := Tφ_pos hd hα hβ hφ
  have htd : d ≤ Tφ d φ := (Tφ_mem hd hα hβ hφ).1
  rw [restSq_eq_polar hd hα hβ hr hφ hrt]
  set SA := ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r with hSA
  set SQ := ser (fun i => Q i (Tφ d φ)) (Tφ d φ) r with hSQ
  have haS := summable_abs_kD hM hd hts
  have hqS : Summable fun i => |Q i (Tφ d φ)| := summable_abs_Q htpos
  have hx : |SA / r| ≤ K / d := by
    refine (abs_ser_div_le haS htpos hr hTt.le).trans ?_
    calc (∑' i, |(k i : ℝ) * D i (Tφ d φ)|) / Tφ d φ ≤ K / Tφ d φ :=
          div_le_div_of_nonneg_right (tsum_abs_kD_le hM hd hts) htpos.le
      _ ≤ K / d := div_le_div_of_nonneg_left hK0 hd htd
  have hy : |SQ / r| ≤ 2 * K / d := by
    refine (abs_ser_div_le hqS htpos hr hTt.le).trans ?_
    calc (∑' i, |Q i (Tφ d φ)|) / Tφ d φ ≤ 2 * K / Tφ d φ :=
          div_le_div_of_nonneg_right (tsum_abs_Q_le_of_bnd hM hd hts) htpos.le
      _ ≤ 2 * K / d := div_le_div_of_nonneg_left (by positivity) hd htd
  have hz : |SA| / r ^ 2 ≤ K / d ^ 2 := by
    refine (abs_ser_div_sq_le haS htpos hr hTt.le).trans ?_
    calc (∑' i, |(k i : ℝ) * D i (Tφ d φ)|) / Tφ d φ ^ 2 ≤ K / Tφ d φ ^ 2 :=
          div_le_div_of_nonneg_right (tsum_abs_kD_le hM hd hts) (by positivity)
      _ ≤ K / d ^ 2 := div_le_div_of_nonneg_left hK0 (by positivity) (pow_le_pow_left₀ hd.le htd 2)
  have hB' : |deriv B r * (SA / r)| ≤ C₁ * (K / d) + K / d ^ 2 := by
    have e : deriv B r * (SA / r) = B₁ r * (SA / r) - SA / r ^ 2 := by
      unfold B₁; field_simp; ring
    rw [e]
    calc |B₁ r * (SA / r) - SA / r ^ 2| ≤ |B₁ r * (SA / r)| + |SA / r ^ 2| := abs_sub _ _
      _ ≤ C₁ * (K / d) + K / d ^ 2 := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]; exact mul_le_mul (hC₁ r ⟨hr, hrT⟩) hx (abs_nonneg _) hC₁0
          · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2)]; exact hz
  have htan := tan_sq_le hd hα hβ hφ
  calc |2 * deriv B r * (SA / r) + (SA / r) ^ 2 + Real.tan φ ^ 2 * (SQ / r) ^ 2|
      ≤ |2 * deriv B r * (SA / r) + (SA / r) ^ 2| + |Real.tan φ ^ 2 * (SQ / r) ^ 2| := abs_add_le _ _
    _ ≤ (|2 * deriv B r * (SA / r)| + |(SA / r) ^ 2|) + |Real.tan φ ^ 2 * (SQ / r) ^ 2| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 2 * (C₁ * (K / d) + K / d ^ 2) + (K / d) ^ 2 + (secRadius d α β / d) ^ 2 * (2 * K / d) ^ 2 := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · have : 2 * deriv B r * (SA / r) = 2 * (deriv B r * (SA / r)) := by ring
          rw [this, abs_mul]; simpa using mul_le_mul_of_nonneg_left hB' (by norm_num : (0 : ℝ) ≤ 2)
        · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
        · rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.tan φ)), abs_pow]
          exact mul_le_mul htan (pow_le_pow_left₀ (abs_nonneg _) hy 2) (sq_nonneg _) (sq_nonneg _)

end Calibration

end SandierSerfaty

end
