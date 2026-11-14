/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.HexSector
public import SandierSerfaty.Calibration.RadialAdmissible
public import SandierSerfaty.Calibration.EdgeForm
public import SandierSerfaty.Dual.ModelSector

/-!
# The trial potential on the hexagon is the Green function (paper proof of `cal:energy-identity`)

On the model sector `S(p, π/6, π/6)` (a sixth of the hexagon, `p ≤ t ≤ R₀`), the radial data are
`u_0 = γ`, `u_m = (-1)^m c_m r^{k_m}` (`r ≤ t ≤ R₀`), and `D_0 = 0`, `D_m(t) = V_m(t) - (-1)^m c_m t^{k_m}`. The
alternating terms cancel and `(r/t)^{k_m} V_m(t) = c_m Re(w^{k_m})` (the edge trace, `V_edge_cos`), so
`modelH radialData p w = γ(|w|) + ∑_{m ≥ 1} c_m Re (w^{6 m})` (`modelH_hex`): the trial potential equals
`h_△ - C_△` (paper proof of `cal:energy-identity`).
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm

theorem R₀_lt_a : R₀ < a := by
  have h := R₀_sq
  have := a_eq_two_mul_p
  have := R₀_pos
  have := a_pos
  have := p_pos
  nlinarith

/-- `Re (w^n) = |w|^n cos (n arg w)`. -/
theorem re_pow_eq (w : ℂ) (n : ℕ) : (w ^ n).re = ‖w‖ ^ n * Real.cos ((n : ℝ) * Complex.arg w) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have : (n : ℂ) * ((Complex.arg w : ℂ) * Complex.I) = (((n : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem sector_facts {w : ℂ} (hw : w ∈ modelSector p (Real.pi / 6) (Real.pi / 6)) :
    0 < w.re ∧ w.re < p ∧ w.re ≤ ‖w‖ ∧ 3 * ‖w‖ ^ 2 ≤ 4 * w.re ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  rw [Real.tan_pi_div_six] at h3 h4
  have hs := sqrt_three_pos
  have hs2 := sqrt_three_mul_self
  have hc : √3 * (1 / √3) = 1 := by field_simp
  have e1 : √3 * w.im < w.re := by
    have := mul_lt_mul_of_pos_left h4 hs
    rwa [← mul_assoc, hc, one_mul] at this
  have e2 : -w.re < √3 * w.im := by
    have := mul_lt_mul_of_pos_left h3 hs
    have e : √3 * (-(1 / √3) * w.re) = -w.re := by
      field_simp
    rwa [e] at this
  have e3 : (√3 * w.im) ^ 2 < w.re ^ 2 := sq_lt_sq' e2 e1
  have e4 : (√3 * w.im) ^ 2 = 3 * w.im ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  refine ⟨h1, h2, le_trans (le_abs_self _) (Complex.abs_re_le_norm w), ?_⟩
  rw [Complex.sq_norm, Complex.normSq_apply]
  linarith

theorem hasSum_sector {w : ℂ} (hw0 : w ≠ 0) (hwa : ‖w‖ < a) :
    Summable fun m : ℕ => coeff (m + 1) * (w ^ (6 * (m + 1))).re :=
  (green_expansion_hasSum hw0 hwa).summable

theorem summable_alt {r : ℝ} (hr0 : 0 < r) (hra : r < a) :
    Summable fun m : ℕ => (-1 : ℝ) ^ (m + 1) * coeff (m + 1) * r ^ (6 * (m + 1)) := by
  have hz : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr0.ne'
  have hn : ‖(r : ℂ)‖ < a := by rwa [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have h := hasSum_sector hz hn
  have h' : Summable fun m : ℕ => coeff (m + 1) * r ^ (6 * (m + 1)) := by
    refine h.congr fun m => ?_
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  refine summable_abs_iff.1 ?_
  refine h'.abs.congr fun m => ?_
  simp [abs_mul, abs_pow]

/-- On the sector, `B(r) = γ(r) + ∑_{m ≥ 1} (-1)^m c_m r^{6m}` for `0 < r ≤ R₀`. -/
theorem B_eq_of_le_R₀ {r : ℝ} (hr0 : 0 < r) (hr : r ≤ R₀) :
    B r = gamma r + ∑' m : ℕ, (-1 : ℝ) ^ (m + 1) * coeff (m + 1) * r ^ (6 * (m + 1)) := by
  have hra : r < a := lt_of_le_of_lt hr R₀_lt_a
  have hu : ∀ m : ℕ, u (m + 1) r = (-1 : ℝ) ^ (m + 1) * coeff (m + 1) * r ^ (6 * (m + 1)) := by
    intro m
    rw [u_of_le_R₀ (Nat.succ_pos m) hr, k_of_pos (Nat.succ_pos m)]
  have hs : Summable fun m : ℕ => u (m + 1) r := by
    simpa only [hu] using summable_alt hr0 hra
  unfold B
  rw [tsum_eq_zero_add' (f := fun i => u i r) hs]
  simp only [hu, u_zero_of_le_R₀ hr]

theorem D_edge {m : ℕ} (hm : 0 < m) {t : ℝ} (h1 : p ≤ t) (h2 : t ≤ R₀) :
    D m t = V m t - (-1 : ℝ) ^ m * coeff m * t ^ k m := by
  unfold D
  rw [bRad_of_mem_edge hm h1 h2, u_of_le_R₀ hm h2]

/-- **The trial potential on the hexagon sector** (paper proof of `cal:energy-identity`):
`H(w) = γ(|w|) + ∑_{m ≥ 1} c_m Re (w^{6m}) = h_△(w) - C_△`. -/
theorem modelH_hex {w : ℂ} (hw : w ∈ modelSector p (Real.pi / 6) (Real.pi / 6)) :
    Dual.modelH radialData p w =
      gamma ‖w‖ + ∑' m : ℕ, coeff (m + 1) * (w ^ (6 * (m + 1))).re := by
  obtain ⟨hX, hXp, hXn, h3⟩ := sector_facts hw
  have hp := p_pos
  have hw0 : w ≠ 0 := by rintro rfl; simp at hX
  have hr0 : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set r := ‖w‖ with hr
  set s := w.re / p with hs
  have hs0 : 0 < s := div_pos hX hp
  have hs1 : s ≤ 1 := by rw [hs, div_le_one hp]; exact hXp.le
  set t := r / s with ht
  have hrt : r = s * t := by rw [ht]; field_simp
  have ht1 : p ≤ t := by
    rw [ht, le_div_iff₀ hs0, hs, mul_div_cancel₀ _ hp.ne']; exact hXn
  have ht2 : t ≤ R₀ := by
    rw [ht, div_le_iff₀ hs0]
    refine (sq_le_sq₀ hr0.le (by have := R₀_pos; positivity)).1 ?_
    rw [mul_pow, R₀_sq, hs, div_pow]
    field_simp
    linarith
  have hr_le : r ≤ R₀ := by
    have : 0 ≤ t := by linarith
    nlinarith
  have hra : r < a := lt_of_le_of_lt hr_le R₀_lt_a
  have ht0 : 0 < t := by linarith
  -- the left side
  have hF : Dual.modelH radialData p w = B r + ∑' i : ℕ, s ^ k i * D i t := rfl
  have hB := B_eq_of_le_R₀ hr0 hr_le
  have hC := hasSum_sector hw0 hra
  have hA := summable_alt hr0 hra
  -- the terms of the correction series
  have hφ : Real.cos (Complex.arg w) = w.re / r := Complex.cos_arg hw0
  have hterm : ∀ m : ℕ, s ^ k (m + 1) * D (m + 1) t =
      coeff (m + 1) * (w ^ (6 * (m + 1))).re -
        (-1 : ℝ) ^ (m + 1) * coeff (m + 1) * r ^ (6 * (m + 1)) := by
    intro m
    have hm : 0 < m + 1 := Nat.succ_pos m
    have hk : k (m + 1) = 6 * (m + 1) := k_of_pos hm
    have htp : t = p / Real.cos (Complex.arg w) := by
      rw [hφ, ht, hs]; field_simp
    have hV : V (m + 1) t = coeff (m + 1) * t ^ k (m + 1) *
        Real.cos ((k (m + 1) : ℝ) * Complex.arg w) := by
      have hc : Real.cos (Complex.arg w) ≠ 0 := by rw [hφ]; positivity
      rw [htp]
      exact V_edge_cos (m + 1) hc
    rw [D_edge hm ht1 ht2, hV, hk, re_pow_eq]
    rw [hk] at hV
    have e : s ^ (6 * (m + 1)) * t ^ (6 * (m + 1)) = r ^ (6 * (m + 1)) := by
      rw [← mul_pow, ← hrt]
    push_cast
    have e2 : s ^ (6 * (m + 1)) * (coeff (m + 1) * t ^ (6 * (m + 1)) *
        Real.cos (6 * ((m : ℝ) + 1) * Complex.arg w) -
        (-1) ^ (m + 1) * coeff (m + 1) * t ^ (6 * (m + 1))) =
        coeff (m + 1) * (s ^ (6 * (m + 1)) * t ^ (6 * (m + 1))) *
          Real.cos (6 * ((m : ℝ) + 1) * Complex.arg w) -
        (-1) ^ (m + 1) * coeff (m + 1) * (s ^ (6 * (m + 1)) * t ^ (6 * (m + 1))) := by ring
    rw [e2, e]
    ring
  have hsum1 : Summable fun m : ℕ => s ^ k (m + 1) * D (m + 1) t := by
    simp only [hterm]
    exact hC.sub hA
  have hD0 : D 0 t = 0 := D_zero_of_le_R₀ ht2
  rw [hF, hB, tsum_eq_zero_add' (f := fun i => s ^ k i * D i t) hsum1, hD0, mul_zero, zero_add]
  simp only [hterm]
  rw [Summable.tsum_sub hC hA, add_assoc]
  congr 1
  ring

end Calibration

end SandierSerfaty

end
