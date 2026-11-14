/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.EdgeNear
public import SandierSerfaty.Tails.Weights

/-!
# The edge polynomial near the edge: `|V_m^{(j)}| ≤ 5600 k⁵ (3/5)^k` on `[p, p + .01]` (paper §6.2)

For `m ≥ 39` (`k = 6m ≥ 234`), `0 ≤ j ≤ 3` and `p ≤ r ≤ p + 1/100` the `j`-th derivatives of
`V_m(r) = c_m Vsum m (r² - p²)` are at most `5600 k⁵ (3/5)^k` (`BJ_V_near`).

With `w = r² - p²` and `X = p + √w`: `.02p + .0001 < .04p²` gives `√w ≤ p/5`, hence `X ≤ 1.2 p = (3/5) a`
(paper §6.2); also `X > 1/2` and `r < .55`. The chain rule of `BJ.comp` replaces
`V''' = 8 r³ V_www + 12 r V_ww` (paper §6.2), and `abs_VsumD_le` bounds `V_{w^ℓ}` by
`|c_m| k^{2ℓ} X^{k-2ℓ}`.
-/

open Set

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The jet `(2r, 2, 0)` of `r ↦ r² - c`. -/
theorem BJ_sq_sub (c : ℝ) (U s : Set ℝ) {W₀ W₁ : ℝ} (h0 : ∀ r ∈ s, |r ^ 2 - c| ≤ W₀)
    (h1 : ∀ r ∈ s, |2 * r| ≤ W₁) : BJ U s (fun r : ℝ => r ^ 2 - c) W₀ W₁ 2 0 := by
  refine ⟨fun r => 2 * r, fun _ => 2, fun _ => 0, ⟨fun x _ => ?_, fun x _ => ?_,
    fun x _ => hasDerivAt_const x _⟩, fun x hx => ⟨by simpa using h0 x hx, by simpa using h1 x hx,
    by simp, by simp⟩⟩
  · simpa using (hasDerivAt_pow 2 x).sub_const c
  · simpa using (hasDerivAt_id x).const_mul 2

/-- `.02 p + .0001 ≤ p²/25`: the near-edge window is inside `√w ≤ p/5` (paper §6.2). -/
theorem near_edge_window {r : ℝ} (h0 : p ≤ r) (h1 : r ≤ p + 1 / 100) :
    0 ≤ r ^ 2 - p ^ 2 ∧ r ^ 2 - p ^ 2 ≤ (p / 5) ^ 2 := by
  have hp := p_gt
  have hp0 := p_pos
  refine ⟨by nlinarith, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ r + p),
    mul_nonneg (sub_nonneg.2 hp.le) hp0.le]

/-- `|c_m| κ^{2ℓ} X^{k-2ℓ} ≤ 7 · 4^ℓ κ^{2ℓ-1} (3/5)^k` for `X = (6/5) p`. -/
theorem coeff_mul_G_le {m : ℕ} (hm : 2 ≤ m) {ℓ : ℕ} (hℓ : 2 * ℓ ≤ k m) :
    |coeff m| * (((k m : ℕ) : ℝ) ^ (2 * ℓ) * ((6 / 5) * p) ^ (k m - 2 * ℓ)) ≤
      7 * 4 ^ ℓ * ((k m : ℝ) ^ (2 * ℓ) / (k m : ℝ)) * (3 / 5 : ℝ) ^ (k m) := by
  have hp := half_lt_p
  have hX : (1 / 2 : ℝ) ≤ (6 / 5) * p := by linarith
  have hXpos : (0 : ℝ) < (6 / 5) * p := by linarith
  have hXa : (6 / 5) * p = (3 / 5) * a := by unfold p; ring
  have hkpos : (0 : ℝ) < (k m : ℝ) := by exact_mod_cast k_pos m
  -- `X^{k-2ℓ} ≤ 4^ℓ X^k`
  have h1 : ((6 / 5) * p) ^ (k m - 2 * ℓ) ≤ 4 ^ ℓ * ((6 / 5) * p) ^ (k m) := by
    have e : ((6 / 5) * p) ^ (k m) = ((6 / 5) * p) ^ (k m - 2 * ℓ) * ((6 / 5) * p) ^ (2 * ℓ) := by
      rw [← pow_add]; congr 1; omega
    have h2 : (1 / 4 : ℝ) ^ ℓ ≤ ((6 / 5) * p) ^ (2 * ℓ) := by
      have : (1 / 4 : ℝ) ^ ℓ = (1 / 2 : ℝ) ^ (2 * ℓ) := by
        rw [pow_mul]; norm_num
      rw [this]; exact pow_le_pow_left₀ (by norm_num) hX _
    have h3 : 0 ≤ ((6 / 5) * p) ^ (k m - 2 * ℓ) := by positivity
    have h4 : (4 : ℝ) ^ ℓ * (1 / 4 : ℝ) ^ ℓ = 1 := by rw [← mul_pow]; norm_num
    calc ((6 / 5) * p) ^ (k m - 2 * ℓ) = ((6 / 5) * p) ^ (k m - 2 * ℓ) * (4 ^ ℓ * (1 / 4) ^ ℓ) := by
          rw [h4]; ring
      _ ≤ ((6 / 5) * p) ^ (k m - 2 * ℓ) * (4 ^ ℓ * ((6 / 5) * p) ^ (2 * ℓ)) := by gcongr
      _ = 4 ^ ℓ * ((6 / 5) * p) ^ (k m) := by rw [e]; ring
  have h5 := abs_coeff_mul_pow_le hm (x := (6 / 5) * p) hXpos.le
  have hXa' : ((6 / 5) * p) / a = 3 / 5 := by rw [mul_div_assoc, p_div_a]; norm_num
  rw [hXa'] at h5
  have hc := abs_nonneg (coeff m)
  have hk0 : (0 : ℝ) ≤ ((k m : ℕ) : ℝ) ^ (2 * ℓ) := by positivity
  calc |coeff m| * (((k m : ℕ) : ℝ) ^ (2 * ℓ) * ((6 / 5) * p) ^ (k m - 2 * ℓ))
      ≤ |coeff m| * (((k m : ℕ) : ℝ) ^ (2 * ℓ) * (4 ^ ℓ * ((6 / 5) * p) ^ (k m))) := by gcongr
    _ = ((k m : ℕ) : ℝ) ^ (2 * ℓ) * 4 ^ ℓ * (|coeff m| * ((6 / 5) * p) ^ (k m)) := by ring
    _ ≤ ((k m : ℕ) : ℝ) ^ (2 * ℓ) * 4 ^ ℓ * ((7 / (k m : ℝ)) * (3 / 5 : ℝ) ^ (k m)) := by gcongr
    _ = _ := by ring

theorem VsumD_le_G (ℓ m : ℕ) (hℓ : 2 * ℓ ≤ k m) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ (p / 5) ^ 2) :
    |VsumD ℓ m w| ≤ ((k m : ℕ) : ℝ) ^ (2 * ℓ) * ((6 / 5) * p) ^ (k m - 2 * ℓ) := by
  refine (abs_VsumD_le ℓ m hℓ hw0).trans ?_
  have hp := p_pos
  have hs : √w ≤ p / 5 := Real.sqrt_le_iff.2 ⟨by positivity, hw1⟩
  have : p + √w ≤ (6 / 5) * p := by linarith
  gcongr

/-- **Near-edge bound** (paper §6.2): for `m ≥ 39`, `0 ≤ j ≤ 3` and `p ≤ r ≤ p + 1/100`,
`|V_m^{(j)}(r)| ≤ 5600 k⁵ (3/5)^k`. -/
theorem BJ_V_near {m : ℕ} (hm : 39 ≤ m) :
    BJ Set.univ (Icc p (p + 1 / 100)) (V m) (5600 * ((k m : ℕ) : ℝ) ^ 5 * (3 / 5 : ℝ) ^ (k m))
      (5600 * ((k m : ℕ) : ℝ) ^ 5 * (3 / 5 : ℝ) ^ (k m))
      (5600 * ((k m : ℕ) : ℝ) ^ 5 * (3 / 5 : ℝ) ^ (k m))
      (5600 * ((k m : ℕ) : ℝ) ^ 5 * (3 / 5 : ℝ) ^ (k m)) := by
  have hk : k m = 6 * m := k_of_pos (by omega)
  have hk234 : 234 ≤ k m := by omega
  have hκ : (234 : ℝ) ≤ ((k m : ℕ) : ℝ) := by exact_mod_cast hk234
  have hp := p_pos
  set X : ℝ := (6 / 5) * p with hX
  have hX0 : 0 ≤ X := by positivity
  -- the outer function
  have hg : BJ Set.univ (Icc 0 ((p / 5) ^ 2)) (VsumD 0 m)
      (((k m : ℕ) : ℝ) ^ (2 * 0) * X ^ (k m - 2 * 0)) (((k m : ℕ) : ℝ) ^ (2 * 1) * X ^ (k m - 2 * 1))
      (((k m : ℕ) : ℝ) ^ (2 * 2) * X ^ (k m - 2 * 2)) (((k m : ℕ) : ℝ) ^ (2 * 3) * X ^ (k m - 2 * 3)) :=
    ⟨_, _, _, jet3_VsumD m, fun w hw => ⟨VsumD_le_G 0 m (by omega) hw.1 hw.2,
      VsumD_le_G 1 m (by omega) hw.1 hw.2, VsumD_le_G 2 m (by omega) hw.1 hw.2,
      VsumD_le_G 3 m (by omega) hw.1 hw.2⟩⟩
  have hw : BJ Set.univ (Icc p (p + 1 / 100)) (fun r : ℝ => r ^ 2 - p ^ 2) ((p / 5) ^ 2) (11 / 10) 2 0 :=
    BJ_sq_sub (p ^ 2) _ _ (fun r hr => by
      obtain ⟨a1, a2⟩ := near_edge_window hr.1 hr.2
      rw [abs_of_nonneg a1]; exact a2) (fun r hr => by
      have := p_lt
      rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2])
  have hmaps : ∀ r ∈ Icc p (p + 1 / 100), r ^ 2 - p ^ 2 ∈ Icc 0 ((p / 5) ^ 2) := fun r hr =>
    near_edge_window hr.1 hr.2
  have hcomp := BJ.comp hg hw hmaps (by positivity) (by positivity) (by positivity) (by norm_num)
    (by norm_num)
  have hcm := hcomp.const_mul (coeff m)
  have hV : V m = fun r => coeff m * VsumD 0 m (r ^ 2 - p ^ 2) := by
    funext r; simp [V, VsumD_zero]
  rw [hV]
  have H0 := coeff_mul_G_le (m := m) (by omega) (ℓ := 0) (by omega)
  have H1 := coeff_mul_G_le (m := m) (by omega) (ℓ := 1) (by omega)
  have H2 := coeff_mul_G_le (m := m) (by omega) (ℓ := 2) (by omega)
  have H3 := coeff_mul_G_le (m := m) (by omega) (ℓ := 3) (by omega)
  set κ : ℝ := ((k m : ℕ) : ℝ) with hκdef
  set E : ℝ := (3 / 5 : ℝ) ^ (k m) with hE
  have hE0 : 0 ≤ E := by positivity
  have hκ1 : (1 : ℝ) ≤ κ := by linarith
  have e0 : κ ^ (2 * 0) / κ = 1 / κ := by simp
  have e1 : κ ^ (2 * 1) / κ = κ := by field_simp
  have e2 : κ ^ (2 * 2) / κ = κ ^ 3 := by field_simp
  have e3 : κ ^ (2 * 3) / κ = κ ^ 5 := by field_simp
  rw [← hX] at H0 H1 H2 H3
  rw [e0] at H0
  rw [e1] at H1
  rw [e2] at H2
  rw [e3] at H3
  simp only [Real.norm_eq_abs] at hcm
  have hk5 : κ ≤ κ ^ 5 := by
    have : κ ^ 1 ≤ κ ^ 5 := pow_le_pow_right₀ hκ1 (by norm_num)
    simpa using this
  have hk3 : κ ^ 3 ≤ κ ^ 5 := pow_le_pow_right₀ hκ1 (by norm_num)
  have hk0 : 1 / κ ≤ κ ^ 5 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_le_pow_right₀ hκ1 (by norm_num : 1 ≤ 5 + 1)]
  have hEk5 : 0 ≤ κ ^ 5 * E := by positivity
  generalize κ ^ (2 * 0) * X ^ (k m - 2 * 0) = G0 at hcm H0
  generalize κ ^ (2 * 1) * X ^ (k m - 2 * 1) = G1 at hcm H1
  generalize κ ^ (2 * 2) * X ^ (k m - 2 * 2) = G2 at hcm H2
  generalize κ ^ (2 * 3) * X ^ (k m - 2 * 3) = G3 at hcm H3
  generalize |coeff m| = c at hcm H0 H1 H2 H3
  refine hcm.mono ?_ ?_ ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_right hk0 hE0]
  · nlinarith [mul_le_mul_of_nonneg_right hk5 hE0]
  · nlinarith [mul_le_mul_of_nonneg_right hk5 hE0, mul_le_mul_of_nonneg_right hk3 hE0]
  · nlinarith [mul_le_mul_of_nonneg_right hk5 hE0, mul_le_mul_of_nonneg_right hk3 hE0]

end Tails

end SandierSerfaty

end
