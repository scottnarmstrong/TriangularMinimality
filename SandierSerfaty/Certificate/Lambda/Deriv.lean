/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.LambdaOrigin
public import SandierSerfaty.Certificate.Box.Radial2
public import SandierSerfaty.Certificate.Lambda.Calculus

/-!
# The two integrands of `λ` and their second-derivative bounds (`comp:lambda-derivatives`)

With `t = t(s) = √(p² + s²)`:

* the first integrand `q = V/s²`, `V(s) = f₀(t) - f₀(p)` (`Calibration.qq`): `V' = f₀'(t) s/t`,
  `V'' = f₀''(t)(s/t)² + f₀'(t) p²/t³`, `q' = V'/s² - 2V/s³`, `q'' = V''/s² - 4V'/s³ + 6V/s⁴` (`hasDerivAt_qq`,
  `hasDerivAt_qq1`); if `|f₀'| ≤ C`, `|f₀''| ≤ C'` on `[p, R₀]` then for `0 < s ≤ x₀`
  `|q''(s)| ≤ C'/p² + 8C/(p s²)` (`abs_qq2_le`, there multiplied by `p`);
* the second integrand `e(t)`: its derivative `Y₁ = e'(t) s/t` has the right derivative
  `E (s/t)² + e'(t) p²/t³` wherever `e'` has the right derivative `E` at `t` (`Y1_right_deriv`), so that
  `Y₁` is `(E' + E/p)`-Lipschitz on `[0, x₀]` if `|e'| ≤ E` and the right derivatives of `e'` are bounded by `E'`
  on `[p, R₀]` (`lip_Y1`).
-/

open Set Filter

public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Calibration

/-! ### `t(s)` -/

theorem tt_ne (s : ℝ) : tt p s ≠ 0 := (tt_pos p_pos).ne'

theorem s_le_tt {s : ℝ} (hs : 0 ≤ s) : s ≤ tt p s := by
  have h := tt_sq (d := p) (s := s) p_pos
  have := tt_pos (d := p) (s := s) p_pos
  nlinarith [p_pos]

theorem tt_le_R₀ {s : ℝ} (h0 : 0 ≤ s) (h : s ≤ x₀) : tt p s ≤ R₀ := by
  have := tt_mono h0 h; rwa [tt_p_x₀] at this

theorem tt_lt_R₀ {s : ℝ} (h0 : 0 ≤ s) (h : s < x₀) : tt p s < R₀ := by
  rw [← tt_p_x₀]
  unfold tt
  exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)

theorem tt_mem {s : ℝ} (h0 : 0 ≤ s) (h : s ≤ x₀) : tt p s ∈ Icc p R₀ := ⟨p_le_tt s, tt_le_R₀ h0 h⟩

theorem hasDerivAt_ratio (s : ℝ) : HasDerivAt (fun s => s / tt p s) (p ^ 2 / tt p s ^ 3) s := by
  have h := (hasDerivAt_id' s).div (hasDerivAt_tt_s p_pos s) (tt_ne s)
  refine h.congr_deriv ?_
  have ht := tt_sq (d := p) (s := s) p_pos
  have hne := tt_ne s
  field_simp
  linear_combination ht

theorem abs_ratio_le {s : ℝ} (hs : 0 ≤ s) : |s / tt p s| ≤ 1 := by
  rw [abs_div, abs_of_nonneg hs, abs_of_pos (tt_pos p_pos)]
  exact div_le_one_of_le₀ (s_le_tt hs) (tt_pos p_pos).le

theorem p2_div_tt3_le (s : ℝ) : p ^ 2 / tt p s ^ 3 ≤ 1 / p := by
  have hp := p_pos
  have ht := p_le_tt s
  rw [div_le_div_iff₀ (by have := tt_pos (d := p) (s := s) hp; positivity) hp]
  have : p ^ 3 ≤ tt p s ^ 3 := pow_le_pow_left₀ hp.le ht 3
  nlinarith

/-! ### The first integrand -/

/-- `V(s) = f₀(t) - f₀(p)`. -/
@[expose] noncomputable def V (s : ℝ) : ℝ := f₀ (tt p s) - f₀ p

/-- `V'(s) = f₀'(t) s/t`. -/
@[expose] noncomputable def V1 (s : ℝ) : ℝ := deriv f₀ (tt p s) * (s / tt p s)

/-- `V''(s) = f₀''(t) (s/t)² + f₀'(t) p²/t³`. -/
@[expose] noncomputable def V2 (s : ℝ) : ℝ :=
  deriv (deriv f₀) (tt p s) * (s / tt p s) ^ 2 + deriv f₀ (tt p s) * (p ^ 2 / tt p s ^ 3)

/-- `q' = V'/s² - 2V/s³`. -/
@[expose] noncomputable def qq1 (s : ℝ) : ℝ := V1 s / s ^ 2 - 2 * V s / s ^ 3

/-- `q'' = V''/s² - 4V'/s³ + 6V/s⁴`. -/
@[expose] noncomputable def qq2 (s : ℝ) : ℝ := V2 s / s ^ 2 - 4 * V1 s / s ^ 3 + 6 * V s / s ^ 4

theorem hasDerivAt_V (s : ℝ) : HasDerivAt V (V1 s) s := by
  have h := ((differentiableAt_f₀ (tt_pos (d := p) (s := s) p_pos)).hasDerivAt).comp s (hasDerivAt_tt_s p_pos s)
  exact h.sub_const (f₀ p)

theorem hasDerivAt_V1 (s : ℝ) : HasDerivAt V1 (V2 s) s := by
  have h := (Box.hasDerivAt_deriv_f₀ (tt_pos (d := p) (s := s) p_pos)).comp s (hasDerivAt_tt_s p_pos s)
  have h2 := h.mul (hasDerivAt_ratio s)
  refine h2.congr_deriv ?_
  unfold V2; simp only [Function.comp_def]; ring

theorem qq_eq : qq = fun s => V s / s ^ 2 := rfl

theorem hasDerivAt_qq {s : ℝ} (hs : s ≠ 0) : HasDerivAt qq (qq1 s) s := by
  rw [qq_eq]
  have h := (hasDerivAt_V s).div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs)
  refine h.congr_deriv ?_
  unfold qq1
  field_simp
  ring

theorem hasDerivAt_qq1 {s : ℝ} (hs : s ≠ 0) : HasDerivAt qq1 (qq2 s) s := by
  have h1 := (hasDerivAt_V1 s).div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs)
  have h2 := ((hasDerivAt_V s).const_mul 2).div (hasDerivAt_pow 3 s) (pow_ne_zero 3 hs)
  have h := h1.fun_sub h2
  have e : qq1 = fun s => V1 s / s ^ 2 - 2 * V s / s ^ 3 := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold qq2
  field_simp
  ring

theorem continuousOn_qq : ContinuousOn qq (Ioi 0) := fun _ hs =>
  (hasDerivAt_qq (ne_of_gt hs)).continuousAt.continuousWithinAt

/-- `|f₀(t) - f₀(p)| ≤ C (t - p)` from `|f₀'| ≤ C` on `[p, t]`. -/
theorem abs_V_le {C s : ℝ} (hC : ∀ t ∈ Icc p R₀, |deriv f₀ t| ≤ C) (h0 : 0 ≤ s) (hs : s ≤ x₀) :
    |V s| ≤ C * (tt p s - p) := by
  have hp := p_pos
  have ht := tt_mem h0 hs
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f₀) (f' := deriv f₀) (C := C) (a := p) (b := tt p s)
    (fun x hx => ((differentiableAt_f₀ (lt_of_lt_of_le hp hx.1)).hasDerivAt).hasDerivWithinAt)
    (fun x hx => by simpa using hC x ⟨hx.1, hx.2.le.trans ht.2⟩) (tt p s) ⟨ht.1, le_rfl⟩
  simpa [V, Real.norm_eq_abs] using this

theorem tt_sub_p_le (s : ℝ) : tt p s - p ≤ s ^ 2 / (2 * p) := by
  have hp := p_pos
  have h := tt_sub_mul (s := s)
  have h1 := p_le_tt s
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **`comp:lambda-derivatives`, first integrand**: `|q''(s)| ≤ C'/p² + 8C/(p s²)` on `(0, x₀]`. -/
theorem abs_qq2_le {C C' s : ℝ} (hC : ∀ t ∈ Icc p R₀, |deriv f₀ t| ≤ C)
    (hC' : ∀ t ∈ Icc p R₀, |deriv (deriv f₀) t| ≤ C') (hs : 0 < s) (hsx : s ≤ x₀) :
    |qq2 s| ≤ C' / p ^ 2 + 8 * C / (p * s ^ 2) := by
  have hp := p_pos
  have ht := tt_mem hs.le hsx
  have htp := tt_pos (d := p) (s := s) hp
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p ⟨le_rfl, p_lt_R₀.le⟩)
  have hd1 := hC (tt p s) ht
  have hd2 := hC' (tt p s) ht
  have hr : |s / tt p s| ≤ s / p := by
    rw [abs_div, abs_of_pos hs, abs_of_pos htp]
    exact div_le_div_of_nonneg_left hs.le hp ht.1
  have hr2 : (s / tt p s) ^ 2 ≤ s ^ 2 / p ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hp.le ht.1 2)
  -- the three pieces
  have bV : |V s| ≤ C * s ^ 2 / (2 * p) := by
    have := abs_V_le hC hs.le hsx
    calc |V s| ≤ C * (tt p s - p) := this
      _ ≤ C * (s ^ 2 / (2 * p)) := mul_le_mul_of_nonneg_left (tt_sub_p_le s) hC0
      _ = C * s ^ 2 / (2 * p) := by ring
  have bV1 : |V1 s| ≤ C * (s / p) := by
    unfold V1; rw [abs_mul]
    exact mul_le_mul hd1 hr (abs_nonneg _) hC0
  have bV2 : |V2 s| ≤ C' * (s ^ 2 / p ^ 2) + C * (1 / p) := by
    unfold V2
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (sq_nonneg (s / tt p s))]
      exact mul_le_mul hd2 hr2 (sq_nonneg _) ((abs_nonneg _).trans hd2)
    · rw [abs_mul, abs_of_pos (by positivity : 0 < p ^ 2 / tt p s ^ 3)]
      exact mul_le_mul hd1 (p2_div_tt3_le s) (by positivity) hC0
  have hs2 : 0 < s ^ 2 := by positivity
  have e1 : |V2 s / s ^ 2| ≤ C' / p ^ 2 + C / (p * s ^ 2) := by
    rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
    calc |V2 s| ≤ C' * (s ^ 2 / p ^ 2) + C * (1 / p) := bV2
      _ = (C' / p ^ 2 + C / (p * s ^ 2)) * s ^ 2 := by field_simp
  have e2 : |4 * V1 s / s ^ 3| ≤ 4 * C / (p * s ^ 2) := by
    have hs3 : 0 < s ^ 3 := by positivity
    rw [abs_div, abs_mul, abs_of_pos hs3, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ hs3]
    calc 4 * |V1 s| ≤ 4 * (C * (s / p)) := by linarith
      _ = 4 * C / (p * s ^ 2) * s ^ 3 := by field_simp
  have e3 : |6 * V s / s ^ 4| ≤ 3 * C / (p * s ^ 2) := by
    have hs4 : 0 < s ^ 4 := by positivity
    rw [abs_div, abs_mul, abs_of_pos hs4, abs_of_pos (by norm_num : (0 : ℝ) < 6), div_le_iff₀ hs4]
    calc 6 * |V s| ≤ 6 * (C * s ^ 2 / (2 * p)) := by linarith
      _ = 3 * C / (p * s ^ 2) * s ^ 4 := by field_simp; ring
  unfold qq2
  calc |V2 s / s ^ 2 - 4 * V1 s / s ^ 3 + 6 * V s / s ^ 4|
      ≤ |V2 s / s ^ 2| + |4 * V1 s / s ^ 3| + |6 * V s / s ^ 4| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ (C' / p ^ 2 + C / (p * s ^ 2)) + 4 * C / (p * s ^ 2) + 3 * C / (p * s ^ 2) := by gcongr
    _ = C' / p ^ 2 + 8 * C / (p * s ^ 2) := by ring

/-! ### The second integrand -/

/-- `(e ∘ t)'(s) = e'(t) s/t`. -/
@[expose] noncomputable def Y1 (s : ℝ) : ℝ := deriv e (tt p s) * (s / tt p s)

theorem hasDerivAt_eY (s : ℝ) : HasDerivAt (fun s => e (tt p s)) (Y1 s) s :=
  ((differentiableAt_e (tt_pos (d := p) (s := s) p_pos)).hasDerivAt).comp s (hasDerivAt_tt_s p_pos s)

theorem continuous_eY : Continuous fun s => e (tt p s) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_eY s).continuousAt

theorem continuous_Y1 : Continuous Y1 := by
  have h1 : Continuous fun s => deriv e (tt p s) :=
    continuousOn_deriv_e.comp_continuous (continuous_tt p) fun s => tt_pos p_pos
  have h2 : Continuous fun s => s / tt p s :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_ratio s).continuousAt
  exact h1.mul h2

/-- The right derivative of `Y₁` from a right derivative of `e'`. -/
theorem Y1_right_deriv {s E : ℝ} (hs : 0 ≤ s) (h : HasDerivWithinAt (deriv e) E (Ici (tt p s)) (tt p s)) :
    HasDerivWithinAt Y1 (E * (s / tt p s) ^ 2 + deriv e (tt p s) * (p ^ 2 / tt p s ^ 3)) (Ici s) s := by
  have hm : MapsTo (tt p) (Ici s) (Ici (tt p s)) := fun x hx => tt_mono hs hx
  have h1 := h.comp s (hasDerivAt_tt_s p_pos s).hasDerivWithinAt hm
  have h2 := h1.mul (hasDerivAt_ratio s).hasDerivWithinAt
  refine h2.congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- **`comp:lambda-derivatives`, second integrand**: `Y₁ = (e ∘ t)'` is `(E' + E/p)`-Lipschitz on `[u, v] ⊆ [0, x₀]`. -/
theorem lip_Y1 {E E' u v : ℝ} (hE : ∀ t ∈ Icc p R₀, |deriv e t| ≤ E)
    (hE' : ∀ t ∈ Ico p R₀, ∃ E₂, HasDerivWithinAt (deriv e) E₂ (Ici t) t ∧ |E₂| ≤ E') (hu : 0 ≤ u) (hv : v ≤ x₀) :
    ∀ x ∈ Icc u v, ∀ z ∈ Icc u v, |Y1 x - Y1 z| ≤ (E' + E / p) * |x - z| := by
  have hp := p_pos
  choose! E2 hE2 using hE'
  have hmem : ∀ x ∈ Ico u v, tt p x ∈ Ico p R₀ := fun x hx =>
    ⟨p_le_tt x, tt_lt_R₀ (hu.trans hx.1) (lt_of_lt_of_le hx.2 hv)⟩
  intro x hx z hz
  refine abs_sub_le_of_right_deriv (g := Y1)
    (g' := fun x => E2 (tt p x) * (x / tt p x) ^ 2 + deriv e (tt p x) * (p ^ 2 / tt p x ^ 3))
    continuous_Y1.continuousOn (fun y hy => Y1_right_deriv (hu.trans hy.1) (hE2 _ (hmem y hy)).1)
    (fun y hy => ?_) hx hz
  have hy0 : 0 ≤ y := hu.trans hy.1
  have hb1 := (hE2 _ (hmem y hy)).2
  have hb2 := hE (tt p y) ⟨(hmem y hy).1, (hmem y hy).2.le⟩
  have hr := abs_ratio_le hy0
  have hr2 : (y / tt p y) ^ 2 ≤ 1 := by
    have := sq_abs (y / tt p y); rw [← this]; nlinarith [abs_nonneg (y / tt p y)]
  have hE'0 : 0 ≤ E' := (abs_nonneg _).trans hb1
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (sq_nonneg (y / tt p y))]
    calc |E2 (tt p y)| * (y / tt p y) ^ 2 ≤ E' * 1 := mul_le_mul hb1 hr2 (sq_nonneg _) hE'0
      _ = E' := mul_one _
  · rw [abs_mul, abs_of_pos (by have := tt_pos (d := p) (s := y) hp; positivity : 0 < p ^ 2 / tt p y ^ 3)]
    calc |deriv e (tt p y)| * (p ^ 2 / tt p y ^ 3) ≤ E * (1 / p) :=
          mul_le_mul hb2 (p2_div_tt3_le y) (by have := tt_pos (d := p) (s := y) hp; positivity)
            ((abs_nonneg _).trans hb2)
      _ = E / p := by ring

end SandierSerfaty.Certificate.Lambda
