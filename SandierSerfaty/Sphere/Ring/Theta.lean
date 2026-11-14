/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Rows
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The interaction bound (sphere note, Lemma 5.2 (iii))

* `Sphere.ringTheta`: `Θ(s) = -log(1 - e^{-s})`;
* `Sphere.ringTheta_antitoneOn`, `Sphere.ringTheta_add_le` (`Θ(s + a) ≤ e^{-a} Θ(s)`);
* `Sphere.RowConfig.abs_X_le`: `|X_{kl}| ≤ min(N_k, N_l) Θ(max(N_k, N_l) |t_k - t_l|)`.
-/

open Complex Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `Θ(s) = -log(1 - e^{-s})` (Lemma 5.2 (iii)). -/
@[expose] noncomputable def ringTheta (s : ℝ) : ℝ := -Real.log (1 - Real.exp (-s))

theorem ringTheta_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ ringTheta s := by
  unfold ringTheta
  have h1 : Real.exp (-s) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h0 : 0 < Real.exp (-s) := Real.exp_pos _
  have : Real.log (1 - Real.exp (-s)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

theorem ringTheta_antitoneOn : AntitoneOn ringTheta (Set.Ioi 0) := by
  intro s hs s' hs' hss'
  unfold ringTheta
  have h1 : Real.exp (-s) < 1 := Real.exp_lt_one_iff.2 (by simp at hs; linarith)
  have h2 : Real.exp (-s') ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
  have := Real.log_le_log (by linarith) (show 1 - Real.exp (-s) ≤ 1 - Real.exp (-s') by linarith)
  linarith

/-- `-log(1 - v u) ≤ -v log(1 - u)` for `0 ≤ u < 1`, `0 ≤ v ≤ 1` (concavity of `log`). -/
theorem neg_log_one_sub_mul_le {u v : ℝ} (_hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    -Real.log (1 - v * u) ≤ v * -Real.log (1 - u) := by
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 (show (1 : ℝ) ∈ Set.Ioi 0 by simp)
    (show 1 - u ∈ Set.Ioi 0 by simp; linarith) (show 0 ≤ 1 - v by linarith) hv0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  have : (1 - v) + v * (1 - u) = 1 - v * u := by ring
  rw [this] at hc
  linarith

/-- `Θ(s + a) ≤ e^{-a} Θ(s)` for `s > 0`, `a ≥ 0`. -/
theorem ringTheta_add_le {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) :
    ringTheta (s + a) ≤ Real.exp (-a) * ringTheta s := by
  unfold ringTheta
  have h := neg_log_one_sub_mul_le (Real.exp_pos (-s)).le (Real.exp_lt_one_iff.2 (by linarith))
    (Real.exp_pos (-a)).le (Real.exp_le_one_iff.2 (by linarith))
  rwa [← Real.exp_add, show -a + -s = -(s + a) by ring] at h

namespace RowConfig

variable (R : RowConfig)

/-- **Lemma 5.2 (iii)**: `|X_{kl}| ≤ min(N_k, N_l) Θ(max(N_k, N_l) |t_k - t_l|)` for nonempty rows at
distinct heights. -/
theorem abs_X_le (k l : ℕ) (hk : 0 < R.N k) (hl : 0 < R.N l) (h : R.t k ≠ R.t l) :
    |R.X k l| ≤ (min (R.N k) (R.N l) : ℕ) * ringTheta ((max (R.N k) (R.N l) : ℕ) * |R.t k - R.t l|) := by
  set γ := Nat.gcd (R.N k) (R.N l)
  set L := Nat.lcm (R.N k) (R.N l)
  set D := |R.t k - R.t l|
  have hD : 0 < D := abs_pos.2 (sub_ne_zero.2 h)
  have hL0 : 0 < L := Nat.lcm_pos hk hl
  have hγmin : γ ≤ min (R.N k) (R.N l) :=
    le_min (Nat.gcd_le_left _ hk) (Nat.gcd_le_right _ hl)
  have hLmax : max (R.N k) (R.N l) ≤ L :=
    max_le (Nat.le_of_dvd hL0 (Nat.dvd_lcm_left _ _)) (Nat.le_of_dvd hL0 (Nat.dvd_lcm_right _ _))
  have hmax0 : 0 < max (R.N k) (R.N l) := lt_max_of_lt_left hk
  set w : ℂ := Complex.exp ((-((L : ℝ) * D) : ℝ) : ℂ) *
    Complex.exp ((((L : ℝ) * (R.φ l - R.φ k) : ℝ) : ℂ) * I) with hw
  set r := Real.exp (-((L : ℝ) * D)) with hr
  have hwn : ‖w‖ = r := by
    rw [hw, norm_mul, Complex.norm_exp, Complex.norm_exp]
    simp [hr]
  have hLD : 0 < (L : ℝ) * D := mul_pos (by exact_mod_cast hL0) hD
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hr0 : 0 < r := Real.exp_pos _
  -- `|log |1 - w|| ≤ Θ(L D)`
  have hlog : |Real.log ‖1 - w‖| ≤ ringTheta ((L : ℝ) * D) := by
    have hlo : 1 - r ≤ ‖1 - w‖ := by
      have := norm_sub_norm_le (1 : ℂ) w
      rw [norm_one, hwn] at this
      linarith
    have hhi : ‖1 - w‖ ≤ 1 + r := by
      have := norm_sub_le (1 : ℂ) w
      rwa [norm_one, hwn] at this
    have hpos : 0 < ‖1 - w‖ := by linarith
    unfold ringTheta
    rw [← hr, abs_le]
    constructor
    · have := Real.log_le_log (by linarith) hlo
      linarith
    · have h1 := Real.log_le_log hpos hhi
      have h2 : Real.log (1 + r) + Real.log (1 - r) ≤ 0 := by
        rw [← Real.log_mul (by linarith) (by linarith)]
        exact Real.log_nonpos (by nlinarith) (by nlinarith)
      linarith
  have hθ : ringTheta ((L : ℝ) * D) ≤ ringTheta ((max (R.N k) (R.N l) : ℕ) * D) :=
    ringTheta_antitoneOn (show (0 : ℝ) < (max (R.N k) (R.N l) : ℕ) * D from
        mul_pos (by exact_mod_cast hmax0) hD) (show (0 : ℝ) < L * D from hLD)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hLmax) hD.le)
  have hθ0 : 0 ≤ ringTheta ((max (R.N k) (R.N l) : ℕ) * D) := le_trans (ringTheta_nonneg hLD) hθ
  unfold X
  rw [abs_mul, abs_neg, Nat.abs_cast]
  calc (γ : ℝ) * |Real.log ‖1 - w‖| ≤ γ * ringTheta ((max (R.N k) (R.N l) : ℕ) * D) :=
        mul_le_mul_of_nonneg_left (hlog.trans hθ) (Nat.cast_nonneg _)
    _ ≤ (min (R.N k) (R.N l) : ℕ) * ringTheta ((max (R.N k) (R.N l) : ℕ) * D) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hγmin) hθ0

end RowConfig

end Sphere

end SandierSerfaty

end
