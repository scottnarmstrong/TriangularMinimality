/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Weights
public import SandierSerfaty.Tails.JetCalc
public import SandierSerfaty.Calibration.EdgeForm

/-!
# The edge polynomial away from the edge: `|V_m^{(j)}| ≤ 3·10⁶ k² (289/500)^k` on `[p + .01, R₀]`
(paper §6.2)

On `r > p` put `s(r) = √(r² - p²)` and `z(r) = p + i s(r)`, so that `|z| = r` and `V_m = Re (c_m z^{k})`
(`Calibration.V_eq_re`). The derivatives of `s` are `s' = r/s`, `s'' = -p²/s³`, `s''' = 3 p² r/s⁵`;
on `[p + .01, R₀]` one has `s ≥ .103`, `r ≤ R₀ < .621`, hence
`|z'| ≤ 7`, `|z''| ≤ 300`, `|z'''| ≤ 60000` (paper §6.2). The chain rule for `z^{k}` (`BJ.pow3` over `ℂ`)
and `|c_m| R₀^k ≤ (7/k) (R₀/a)^k` give the bound for all derivative orders `0, …, 3` (`BJ_V_mid`).
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- `s(r) = √(r² - p²)`. -/
@[expose] noncomputable def sRoot (r : ℝ) : ℝ := √(r ^ 2 - p ^ 2)

/-- `s' = r/s`. -/
@[expose] noncomputable def sRoot1 (r : ℝ) : ℝ := r / sRoot r

/-- `s'' = -p²/s³`. -/
@[expose] noncomputable def sRoot2 (r : ℝ) : ℝ := -p ^ 2 / sRoot r ^ 3

/-- `s''' = 3 p² r/s⁵`. -/
@[expose] noncomputable def sRoot3 (r : ℝ) : ℝ := 3 * p ^ 2 * r / sRoot r ^ 5

theorem sRoot_pos {r : ℝ} (hr : p < r) : 0 < sRoot r := by
  have := p_pos
  exact Real.sqrt_pos.2 (by nlinarith)

theorem sRoot_sq {r : ℝ} (hr : p < r) : sRoot r ^ 2 = r ^ 2 - p ^ 2 := by
  have := p_pos
  exact Real.sq_sqrt (by nlinarith)

theorem hasDerivAt_sRoot {r : ℝ} (hr : p < r) : HasDerivAt sRoot (sRoot1 r) r := by
  have hp := p_pos
  have hpos : r ^ 2 - p ^ 2 ≠ 0 := by nlinarith
  have h := ((hasDerivAt_pow 2 r).sub_const (p ^ 2)).sqrt hpos
  have hs := sRoot_pos hr
  refine h.congr_deriv ?_
  unfold sRoot1 sRoot
  have : (√(r ^ 2 - p ^ 2)) ≠ 0 := hs.ne'
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

theorem hasDerivAt_sRoot1 {r : ℝ} (hr : p < r) : HasDerivAt sRoot1 (sRoot2 r) r := by
  have hs := sRoot_pos hr
  have hs2 := sRoot_sq hr
  have h := (hasDerivAt_id r).div (hasDerivAt_sRoot hr) hs.ne'
  have e : sRoot1 = fun r => id r / sRoot r := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold sRoot2
  have : (1 * sRoot r - id r * sRoot1 r) / sRoot r ^ 2 = (sRoot r ^ 2 - r ^ 2) / sRoot r ^ 3 := by
    unfold sRoot1; simp only [id]; field_simp
  rw [this, hs2]
  ring

theorem hasDerivAt_sRoot2 {r : ℝ} (hr : p < r) : HasDerivAt sRoot2 (sRoot3 r) r := by
  have hs := sRoot_pos hr
  have hs2 := sRoot_sq hr
  have hd : HasDerivAt (fun r => sRoot r ^ 3) (3 * sRoot r ^ 2 * sRoot1 r) r := by
    have h3 := (hasDerivAt_pow 3 (sRoot r)).comp r (hasDerivAt_sRoot hr)
    exact h3.congr_deriv (by norm_num)
  have h := (hasDerivAt_const r (-p ^ 2)).div hd (pow_pos hs 3).ne'
  have e : sRoot2 = fun r => (fun _ => -p ^ 2) r / (fun r => sRoot r ^ 3) r := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold sRoot3 sRoot1
  field_simp
  ring

/-! ### The complex curve `z(r) = p + i s(r)` -/

/-- `z(r) = p + i √(r² - p²)`, a point of modulus `r` on the edge of the Voronoi cell. -/
@[expose] noncomputable def zc (r : ℝ) : ℂ := (p : ℂ) + ((sRoot r : ℝ) : ℂ) * Complex.I

/-- The first derivative `z' = i s'`. -/
@[expose] noncomputable def zc1 (r : ℝ) : ℂ := ((sRoot1 r : ℝ) : ℂ) * Complex.I

/-- The second derivative `z'' = i s''`. -/
@[expose] noncomputable def zc2 (r : ℝ) : ℂ := ((sRoot2 r : ℝ) : ℂ) * Complex.I

/-- The third derivative `z''' = i s'''`. -/
@[expose] noncomputable def zc3 (r : ℝ) : ℂ := ((sRoot3 r : ℝ) : ℂ) * Complex.I

theorem jet3_zc : Jet3 (Ioi p) zc zc1 zc2 zc3 :=
  ⟨fun _ hr => ((hasDerivAt_sRoot hr).ofReal_comp.mul_const Complex.I).const_add (p : ℂ),
    fun _ hr => (hasDerivAt_sRoot1 hr).ofReal_comp.mul_const Complex.I,
    fun _ hr => (hasDerivAt_sRoot2 hr).ofReal_comp.mul_const Complex.I⟩

theorem norm_zc {r : ℝ} (hr : p < r) : ‖zc r‖ = r := by
  have hs2 := sRoot_sq hr
  have hr0 : 0 ≤ r := by linarith [p_pos]
  have h : ‖zc r‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [zc, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    nlinarith
  exact (sq_eq_sq₀ (norm_nonneg _) hr0).1 h

/-- `s ≥ .103` on `[p + .01, ∞)` (paper §6.2). -/
theorem sRoot_ge {r : ℝ} (hr : p + 1 / 100 ≤ r) : 103 / 1000 ≤ sRoot r := by
  have hp := p_gt
  have hp0 := p_pos
  unfold sRoot
  apply Real.le_sqrt_of_sq_le
  nlinarith

theorem norm_zc1_le {r : ℝ} (hr : p + 1 / 100 ≤ r) (hr1 : r ≤ R₀) : ‖zc1 r‖ ≤ 7 := by
  have hs := sRoot_ge hr
  have hR := R₀_lt
  have hs0 : 0 < sRoot r := by linarith
  unfold zc1 sRoot1
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg (by
    have : 0 ≤ r := by linarith [p_pos]
    positivity), div_le_iff₀ hs0]
  linarith

theorem norm_zc2_le {r : ℝ} (hr : p + 1 / 100 ≤ r) : ‖zc2 r‖ ≤ 300 := by
  have hs := sRoot_ge hr
  have hp := p_lt
  have hp0 := p_pos
  have hs0 : 0 < sRoot r := by linarith
  have h3 : (103 / 1000 : ℝ) ^ 3 ≤ sRoot r ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  unfold zc2 sRoot2
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ p ^ 2), abs_of_pos (pow_pos hs0 3),
    div_le_iff₀ (pow_pos hs0 3)]
  nlinarith

theorem norm_zc3_le {r : ℝ} (hr : p + 1 / 100 ≤ r) (hr1 : r ≤ R₀) : ‖zc3 r‖ ≤ 60000 := by
  have hs := sRoot_ge hr
  have hp := p_lt
  have hp0 := p_pos
  have hR := R₀_lt
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < sRoot r := by linarith
  have h5 : (103 / 1000 : ℝ) ^ 5 ≤ sRoot r ^ 5 := pow_le_pow_left₀ (by norm_num) hs 5
  have hp2 : p ^ 2 ≤ (538 / 1000) ^ 2 := pow_le_pow_left₀ hp0.le hp.le 2
  unfold zc3 sRoot3
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * p ^ 2 * r / sRoot r ^ 5),
    div_le_iff₀ (pow_pos hs0 5)]
  nlinarith [mul_le_mul hp2 hr1 hr0.le (by positivity : (0 : ℝ) ≤ (538 / 1000) ^ 2)]

/-- The jets of `z` on `[p + .01, R₀]`: `|z| ≤ R₀`, `|z'| ≤ 7`, `|z''| ≤ 300`, `|z'''| ≤ 60000`
(paper §6.2). -/
theorem BJ_zc : BJ (Ioi p) (Icc (p + 1 / 100) R₀) zc R₀ 7 300 60000 :=
  ⟨_, _, _, jet3_zc, fun r hr => by
    have hpr : p < r := by linarith [hr.1]
    exact ⟨(norm_zc hpr).le.trans hr.2, norm_zc1_le hr.1 hr.2, norm_zc2_le hr.1,
      norm_zc3_le hr.1 hr.2⟩⟩

end Tails

end SandierSerfaty

end
