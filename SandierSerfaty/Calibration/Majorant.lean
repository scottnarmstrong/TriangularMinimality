/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.ModeDerivative
public import SandierSerfaty.Calibration.TsumDeriv
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summable majorants of the radial data and their derivatives

From `tail:mode-derivative-bound` (`Tails/ModeDerivative.lean`) and the vanishing of `D_i` beyond `l`:

* `summable_pow_wk n`: `∑_m (6m)^n w_{6m} < ∞` for every `n` (the explicit geometric terms of paper `tail:w-definition`);
* `u_bounds`, `D_bounds`: for `m ≥ 39` and *every* `t > 0` the values and first two derivatives of
  `u_m`, `D_m` at `t` are at most `w_{6m}` (for `t ≥ l` they are constant, resp. zero);
* `exists_D_majorant d`: for `d > 0` a nonnegative `M : ℕ → ℝ`, with `∑ (k_i)^a M_i < ∞` for all `a`, bounding
  `|D_i|, |D_i'|, |D_i''|` on `[d, ∞)` for **all** modes (the finitely many retained modes by compactness
  of `[d, l]`). This supplies the first half of a step that the paper leaves implicit (the series `∑ k_i^a sup |D_i^{(j)}|`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

theorem l_pos' : 0 < l := by have := R₀_pos; have := R₀_lt_l; linarith

theorem summable_pow_geom_six (n : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun m : ℕ => ((6 * m : ℕ) : ℝ) ^ n * ρ ^ (6 * m) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one n (r := ρ ^ 6)
    (by rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg h0]; exact pow_lt_one₀ h0 h1 (by norm_num))
  refine (h.mul_left (6 ^ n)).congr fun m => ?_
  push_cast
  rw [pow_mul]
  ring

theorem Tails.wk_nonneg (k : ℕ) : 0 ≤ Tails.wk k := by unfold Tails.wk; positivity

theorem summable_pow_wk (n : ℕ) :
    Summable fun m : ℕ => ((6 * m : ℕ) : ℝ) ^ n * Tails.wk (6 * m) := by
  have h1 := (summable_pow_geom_six (n + 2) (ρ := 13 / 20) (by norm_num) (by norm_num)).mul_left 30
  have h2 := (summable_pow_geom_six (n + 3) (ρ := 1 / 2) (by norm_num) (by norm_num)).mul_left
    (3 * 10 ^ 6)
  have h3 := (summable_pow_geom_six (n + 5) (ρ := 3 / 5) (by norm_num) (by norm_num)).mul_left 5600
  have h4 := (summable_pow_geom_six (n + 2) (ρ := 289 / 500) (by norm_num) (by norm_num)).mul_left
    (7 * 10 ^ 11)
  refine (((h1.add h2).add h3).add h4).mul_left (10 ^ 6) |>.congr fun m => ?_
  unfold Tails.wk
  rw [one_div, inv_pow]
  ring

/-! ### Bounds for every `t > 0` -/

theorem deriv_u_of_ge (i : ℕ) {r : ℝ} (hr : l ≤ r) : deriv (u i) r = 0 ∧ deriv (deriv (u i)) r = 0 := by
  have h := deriv_deriv_eq_of_eqOn (f := u i) (g := fun _ => u i l) (s := Ici l) (U := Ioi 0)
    (uniqueDiffOn_Ici l) isOpen_Ioi (fun x hx => lt_of_lt_of_le l_pos' hx)
    (fun x hx => u_eq_of_ge hx) (contDiffOn_u i) contDiffOn_const
  have e : deriv (fun _ : ℝ => u i l) = fun _ => 0 := by funext x; simp
  refine ⟨?_, ?_⟩
  · have := h.1 hr; rwa [e] at this
  · have := h.2 hr; rw [e] at this; simpa using this

theorem deriv_D_of_ge (i : ℕ) {r : ℝ} (hr : l ≤ r) : deriv (D i) r = 0 ∧ deriv (deriv (D i)) r = 0 := by
  have h := deriv_deriv_eq_of_eqOn (f := D i) (g := fun _ => (0 : ℝ)) (s := Ici l) (U := Ioi 0)
    (uniqueDiffOn_Ici l) isOpen_Ioi (fun x hx => lt_of_lt_of_le l_pos' hx)
    (fun x hx => D_of_ge hx) (contDiffOn_D i) contDiffOn_const
  have e : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by funext x; simp
  refine ⟨?_, ?_⟩
  · have := h.1 hr; rwa [e] at this
  · have := h.2 hr; rw [e] at this; simpa using this

theorem u_bounds {m : ℕ} (hm : 39 ≤ m) {t : ℝ} (ht : 0 < t) :
    |u m t| ≤ Tails.wk (6 * m) ∧ |deriv (u m) t| ≤ Tails.wk (6 * m) ∧
      |deriv (deriv (u m)) t| ≤ Tails.wk (6 * m) := by
  by_cases h : t ≤ l
  · exact (Tails.mode_derivative_bound_le_two hm ⟨ht, h⟩).1 |> fun x => by
      have := k_of_pos (show 0 < m by omega); rw [this] at x; exact x
  · push Not at h
    obtain ⟨d1, d2⟩ := deriv_u_of_ge m h.le
    have hw := Tails.wk_nonneg (6 * m)
    have h0 := (Tails.mode_derivative_bound_le_two hm ⟨l_pos', le_rfl⟩).1.1
    rw [k_of_pos (show 0 < m by omega)] at h0
    refine ⟨?_, by simpa [d1] using hw, by simpa [d2] using hw⟩
    rwa [u_eq_of_ge h.le]

theorem D_bounds {m : ℕ} (hm : 39 ≤ m) {t : ℝ} (ht : 0 < t) :
    |D m t| ≤ Tails.wk (6 * m) ∧ |deriv (D m) t| ≤ Tails.wk (6 * m) ∧
      |deriv (deriv (D m)) t| ≤ Tails.wk (6 * m) := by
  by_cases h : t ≤ l
  · exact (Tails.mode_derivative_bound_le_two hm ⟨ht, h⟩).2 |> fun x => by
      have := k_of_pos (show 0 < m by omega); rw [this] at x; exact x
  · push Not at h
    obtain ⟨d1, d2⟩ := deriv_D_of_ge m h.le
    have hw := Tails.wk_nonneg (6 * m)
    refine ⟨by simpa [D_of_ge h.le] using hw, by simpa [d1] using hw, by simpa [d2] using hw⟩

/-! ### Majorants on `[d, ∞)` for all modes -/

theorem continuousOn_deriv_deriv_D (i : ℕ) : ContinuousOn (deriv (deriv (D i))) (Ioi 0) :=
  (((contDiffOn_D i).deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).deriv_of_isOpen
    isOpen_Ioi (m := 0) (by norm_num)).continuousOn

theorem continuousOn_deriv_D (i : ℕ) : ContinuousOn (deriv (D i)) (Ioi 0) :=
  ((contDiffOn_D i).deriv_of_isOpen isOpen_Ioi (m := 0) (by norm_num)).continuousOn

theorem continuousOn_D (i : ℕ) : ContinuousOn (D i) (Ioi 0) :=
  (contDiffOn_D i).continuousOn

/-- Each mode is bounded, with its first two derivatives, on `[d, ∞)`. -/
theorem exists_D_bound (i : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, d ≤ t →
      |D i t| ≤ C ∧ |deriv (D i) t| ≤ C ∧ |deriv (deriv (D i)) t| ≤ C := by
  have hsub : Icc d l ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hd ht.1
  obtain ⟨C₀, h₀⟩ := (isCompact_Icc (a := d) (b := l)).exists_bound_of_continuousOn
    ((continuousOn_D i).mono hsub)
  obtain ⟨C₁, h₁⟩ := (isCompact_Icc (a := d) (b := l)).exists_bound_of_continuousOn
    ((continuousOn_deriv_D i).mono hsub)
  obtain ⟨C₂, h₂⟩ := (isCompact_Icc (a := d) (b := l)).exists_bound_of_continuousOn
    ((continuousOn_deriv_deriv_D i).mono hsub)
  refine ⟨max (max C₀ C₁) (max C₂ 0), le_max_of_le_right (le_max_right _ _), fun t ht => ?_⟩
  by_cases h : l ≤ t
  · obtain ⟨e1, e2⟩ := deriv_D_of_ge i h
    simp [D_of_ge h, e1, e2]
  · push Not at h
    have hm : t ∈ Icc d l := ⟨ht, h.le⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (Real.norm_eq_abs _ ▸ h₀ t hm).trans (by simp)
    · exact (Real.norm_eq_abs _ ▸ h₁ t hm).trans (by simp)
    · exact (Real.norm_eq_abs _ ▸ h₂ t hm).trans (by simp)

/-- A summable majorant of `|D_i|, |D_i'|, |D_i''|` on `[d, ∞)`, uniform over all modes, which stays
summable against every polynomial weight `k_i^a`. -/
theorem exists_D_majorant {d : ℝ} (hd : 0 < d) :
    ∃ M : ℕ → ℝ, (∀ i, 0 ≤ M i) ∧ (∀ a : ℕ, Summable fun i => ((k i : ℕ) : ℝ) ^ a * M i) ∧
      ∀ i, ∀ t, d ≤ t → |D i t| ≤ M i ∧ |deriv (D i) t| ≤ M i ∧ |deriv (deriv (D i)) t| ≤ M i := by
  choose C hC0 hC using fun i => exists_D_bound i hd
  refine ⟨fun i => if i < 39 then C i else Tails.wk (6 * i), fun i => ?_, fun a => ?_, fun i t ht => ?_⟩
  · show 0 ≤ if i < 39 then C i else Tails.wk (6 * i)
    split_ifs
    · exact hC0 i
    · exact Tails.wk_nonneg _
  · rw [← summable_nat_add_iff 39]
    refine ((summable_nat_add_iff 39).2 (summable_pow_wk a)).congr fun m => ?_
    have h1 : ¬ (m + 39 < 39) := by omega
    simp only [h1, ite_false, k_of_pos (show 0 < m + 39 by omega)]
  · by_cases hi : i < 39
    · simpa [hi] using hC i t ht
    · simp only [hi, ite_false]
      exact D_bounds (by omega) (lt_of_lt_of_le hd ht)

end Calibration

end SandierSerfaty

end
