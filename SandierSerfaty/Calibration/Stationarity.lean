/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.FirstOrderRegularity

/-!
# `cal:stationarity`: the gradient of `g_d(x)` vanishes at the regular sector `(p, x₀)`

Paper Lemma `cal:stationarity`, with the differentiation under the integral sign that the paper leaves
implicit. For the constants `λ, μ` of `cal:constants` (`Cal.lam`, `Cal.mu`),
`∂_x g_p(x₀) = 0` and `∂_d g_d(x₀)|_{d = p} = 0` (`stationarity`).

Proof (as in the paper, but with the `d`-derivative taken directly instead of along the ray of fixed angle):

* `∂_x g_p = G(p, ·)` and `G(p, x₀) = 0` by the definition of `μ`, since `x₀² = p²/3` (`G_p_x₀_eq_zero`);
* `∂_d G = f'(t)/t - s² e'(t)/(d² t) - ∂_s (s G / d)` (`Gd_eq`, pointwise algebra with `t² = d² + s²`; only
  `f₀ ∈ C¹` and `e ∈ C¹` are used, the jump of `e''` plays no role);
* by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (the integrand `∂_d G` is continuous on a compact
  neighbourhood of `{p} × [0, x₀]`, `continuousOn_Gd`), `∂_d g_d(x₀) = ∫₀^{x₀} ∂_d G(p, s) ds`;
* `∫₀^{x₀} (f₀'(t)/t - s² e'(t)/(p² t) - λ) ds = 0` is the definition of `λ` after the two integrations by parts
  of the paper (`integral_df₀_div` with the removable singularity of `q(s) = (f₀(t) - f₀(p))/s²` at `s = 0`,
  `tendsto_f₀_quotient`; `integral_de_mul`); the boundary term `x₀ G(p, x₀)/p` vanishes.
-/

open Set Filter Topology MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

/-- `f'(t) = f₀'(t) - λ t`. -/
@[expose] noncomputable def df (t : ℝ) : ℝ := deriv f₀ t - lam * t

theorem hasDerivAt_f {t : ℝ} (ht : 0 < t) : HasDerivAt f (df t) t := by
  have h := ((differentiableAt_f₀ ht).hasDerivAt.sub (((hasDerivAt_pow 2 t).const_mul lam).div_const 2)).sub_const mu
  refine h.congr_deriv ?_
  unfold df; simp; ring

theorem hasDerivAt_tt_s {d : ℝ} (hd : 0 < d) (s : ℝ) : HasDerivAt (tt d) (s / tt d s) s := by
  have h := ((hasDerivAt_pow 2 s).const_add (d ^ 2)).sqrt (by positivity)
  have e : tt d s = √(d ^ 2 + s ^ 2) := rfl
  refine (h.congr_deriv ?_)
  rw [e]; have : 0 < √(d ^ 2 + s ^ 2) := by positivity
  field_simp
  norm_num

theorem hasDerivAt_tt_d {d : ℝ} (hd : 0 < d) (s : ℝ) : HasDerivAt (fun d => tt d s) (d / tt d s) d := by
  have h := ((hasDerivAt_pow 2 d).add_const (s ^ 2)).sqrt (by positivity)
  have e : tt d s = √(d ^ 2 + s ^ 2) := rfl
  refine (h.congr_deriv ?_)
  rw [e]; have : 0 < √(d ^ 2 + s ^ 2) := by positivity
  field_simp
  norm_num


/-- `∂_d G(d,s)`. -/
@[expose] noncomputable def Gd (d s : ℝ) : ℝ :=
  f (tt d s) / tt d s ^ 2 + d ^ 2 * df (tt d s) / tt d s ^ 3 - 2 * d ^ 2 * f (tt d s) / tt d s ^ 4
    + s ^ 2 * e (tt d s) / (d ^ 2 * tt d s ^ 2) - s ^ 2 * deriv e (tt d s) / tt d s ^ 3
    + 2 * s ^ 2 * e (tt d s) / tt d s ^ 4

/-- `∂_s G(d,s)`. -/
@[expose] noncomputable def Gs (d s : ℝ) : ℝ :=
  d * s * df (tt d s) / tt d s ^ 3 - 2 * d * s * f (tt d s) / tt d s ^ 4
    - (2 * s * e (tt d s) / tt d s ^ 2 + s ^ 3 * deriv e (tt d s) / tt d s ^ 3
        - 2 * s ^ 3 * e (tt d s) / tt d s ^ 4) / d

theorem hasDerivAt_G_d {d : ℝ} (hd : 0 < d) (s : ℝ) : HasDerivAt (fun d => G d s) (Gd d s) d := by
  have ht := tt_pos (s := s) hd
  have h1 := hasDerivAt_tt_d hd s
  have hf : HasDerivAt (fun d => f (tt d s)) (df (tt d s) * (d / tt d s)) d :=
    HasDerivAt.comp (h₂ := f) d (hasDerivAt_f ht) h1
  have he : HasDerivAt (fun d => e (tt d s)) (deriv e (tt d s) * (d / tt d s)) d :=
    HasDerivAt.comp (h₂ := e) d (differentiableAt_e ht).hasDerivAt h1
  have hT2 : HasDerivAt (fun d => tt d s ^ 2) (2 * tt d s * (d / tt d s)) d := by
    have := h1.fun_pow 2
    simpa using this
  have hne : tt d s ^ 2 ≠ 0 := by positivity
  have hne2 : d * tt d s ^ 2 ≠ 0 := by positivity
  have A : HasDerivAt (fun d => d / tt d s ^ 2 * f (tt d s))
      ((1 * tt d s ^ 2 - d * (2 * tt d s * (d / tt d s))) / (tt d s ^ 2) ^ 2 * f (tt d s)
        + d / tt d s ^ 2 * (df (tt d s) * (d / tt d s))) d :=
    ((hasDerivAt_id' d).fun_div hT2 hne).fun_mul hf
  have Bq : HasDerivAt (fun d => s ^ 2 / (d * tt d s ^ 2) * e (tt d s))
      ((0 * (d * tt d s ^ 2) - s ^ 2 * (1 * tt d s ^ 2 + d * (2 * tt d s * (d / tt d s))))
          / (d * tt d s ^ 2) ^ 2 * e (tt d s)
        + s ^ 2 / (d * tt d s ^ 2) * (deriv e (tt d s) * (d / tt d s))) d :=
    ((hasDerivAt_const d (s ^ 2)).fun_div ((hasDerivAt_id' d).fun_mul hT2) hne2).fun_mul he
  have := A.sub Bq
  refine (this.congr_deriv ?_)
  unfold Gd
  have h2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd
  field_simp
  ring


theorem hasDerivAt_G_s {d : ℝ} (hd : 0 < d) (s : ℝ) : HasDerivAt (G d) (Gs d s) s := by
  have ht := tt_pos (s := s) hd
  have h1 := hasDerivAt_tt_s hd s
  have hf : HasDerivAt (fun s => f (tt d s)) (df (tt d s) * (s / tt d s)) s :=
    HasDerivAt.comp (h₂ := f) s (hasDerivAt_f ht) h1
  have he : HasDerivAt (fun s => e (tt d s)) (deriv e (tt d s) * (s / tt d s)) s :=
    HasDerivAt.comp (h₂ := e) s (differentiableAt_e ht).hasDerivAt h1
  have hT2 : HasDerivAt (fun s => tt d s ^ 2) (2 * tt d s * (s / tt d s)) s := by
    have := h1.fun_pow 2
    simpa using this
  have hne : tt d s ^ 2 ≠ 0 := by positivity
  have hne2 : d * tt d s ^ 2 ≠ 0 := by positivity
  have A : HasDerivAt (fun s => d / tt d s ^ 2 * f (tt d s))
      ((0 * tt d s ^ 2 - d * (2 * tt d s * (s / tt d s))) / (tt d s ^ 2) ^ 2 * f (tt d s)
        + d / tt d s ^ 2 * (df (tt d s) * (s / tt d s))) s :=
    ((hasDerivAt_const s d).fun_div hT2 hne).fun_mul hf
  have hs2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_id' s).fun_pow 2
  have Bq : HasDerivAt (fun s => s ^ 2 / (d * tt d s ^ 2) * e (tt d s))
      (((2 * s) * (d * tt d s ^ 2) - s ^ 2 * (0 * tt d s ^ 2 + d * (2 * tt d s * (s / tt d s))))
          / (d * tt d s ^ 2) ^ 2 * e (tt d s)
        + s ^ 2 / (d * tt d s ^ 2) * (deriv e (tt d s) * (s / tt d s))) s :=
    (hs2.fun_div ((hasDerivAt_const s d).fun_mul hT2) hne2).fun_mul he
  have := A.sub Bq
  refine (this.congr_deriv ?_)
  unfold Gs
  have h2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd
  field_simp
  ring

/-- The integrand of the first integral: `A(d,s) = f'(t)/t - s² e'(t)/(d² t)`. -/
@[expose] noncomputable def Aint (d s : ℝ) : ℝ := df (tt d s) / tt d s - s ^ 2 * deriv e (tt d s) / (d ^ 2 * tt d s)

/-- The pointwise identity `∂_d G = A - ∂_s (s G / d)`. -/
theorem Gd_eq {d : ℝ} (hd : 0 < d) (s : ℝ) :
    Gd d s = Aint d s - (G d s / d + s / d * Gs d s) := by
  have ht := tt_pos (s := s) hd
  have h2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd
  unfold Gd Aint Gs G
  have hs : s ^ 2 = tt d s ^ 2 - d ^ 2 := by linarith
  generalize tt d s = t at *
  have hs'' := hs
  have hs' : s ^ 2 = t ^ 2 - d ^ 2 := hs
  field_simp
  rw [hs']
  ring


/-! ### The quotient `q(s) = (f₀(t(s)) - f₀(p))/s²` -/

/-- The first integrand of `lam`. -/
@[expose] noncomputable def qq (s : ℝ) : ℝ := (f₀ (tt p s) - f₀ p) / s ^ 2

theorem continuous_tt (d : ℝ) : Continuous (tt d) := by
  unfold tt; fun_prop

theorem continuousAt_qq {s : ℝ} (hs : s ≠ 0) : ContinuousAt qq s := by
  have hp := p_pos
  unfold qq
  have h1 : ContinuousAt (fun s => f₀ (tt p s)) s :=
    (continuousOn_f₀.continuousAt (Ioi_mem_nhds (tt_pos hp))).comp (continuous_tt p).continuousAt
  exact (h1.sub continuousAt_const).div (by fun_prop) (pow_ne_zero 2 hs)

theorem tendsto_qq : Tendsto qq (𝓝[≠] 0) (𝓝 (deriv f₀ p / (2 * p))) := by
  exact tendsto_f₀_quotient

/-- `qq` with the removable singularity filled. -/
@[expose] noncomputable def qq' : ℝ → ℝ := Function.update qq 0 (deriv f₀ p / (2 * p))

theorem continuous_qq' : Continuous qq' := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    exact continuousAt_update_same.2 tendsto_qq
  · have e : qq' =ᶠ[𝓝 s] qq := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs] with y hy
      simp only [qq', Function.update_of_ne hy]
    exact (continuousAt_qq hs).congr e.symm

theorem intervalIntegrable_qq {b : ℝ} (hb : 0 ≤ b) : IntervalIntegrable qq volume 0 b := by
  refine IntervalIntegrable.congr (f := qq') (fun s hs => ?_) (continuous_qq'.intervalIntegrable 0 b)
  rw [Set.uIoc_of_le hb] at hs
  simp only [qq', Function.update_of_ne hs.1.ne']

theorem continuous_df_comp : Continuous fun s => df (tt p s) := by
  have hp := p_pos
  unfold df
  have h1 : Continuous fun s => deriv f₀ (tt p s) :=
    continuousOn_deriv_f₀.comp_continuous (continuous_tt p) fun s => tt_pos hp
  exact h1.sub (continuous_const.mul (continuous_tt p))

theorem continuous_e_comp : Continuous fun s => e (tt p s) :=
  continuousOn_e.comp_continuous (continuous_tt p) fun _ => tt_pos p_pos

theorem continuous_de_comp : Continuous fun s => deriv e (tt p s) :=
  continuousOn_deriv_e.comp_continuous (continuous_tt p) fun _ => tt_pos p_pos

theorem continuous_df₀_comp : Continuous fun s => deriv f₀ (tt p s) :=
  continuousOn_deriv_f₀.comp_continuous (continuous_tt p) fun _ => tt_pos p_pos

/-- `∫₀ᵇ f₀'(t)/t ds = (f₀(t(b)) - f₀(p))/b + ∫₀ᵇ q` (`cal:stationarity`, first display). -/
theorem integral_df₀_div {b : ℝ} (hb : 0 < b) :
    ∫ s in (0 : ℝ)..b, deriv f₀ (tt p s) / tt p s
      = (f₀ (tt p b) - f₀ p) / b + ∫ s in (0 : ℝ)..b, qq s := by
  have hp := p_pos
  set W : ℝ → ℝ := fun s => s * qq s with hW
  have hWc : ContinuousOn W (Icc 0 b) := by
    intro s hs
    refine ContinuousAt.continuousWithinAt ?_
    by_cases h0 : s = 0
    · subst h0
      rw [continuousAt_iff_punctured_nhds]
      have h1 := (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := {0}ᶜ))).mul tendsto_qq
      simpa [hW, qq] using h1
    · exact continuousAt_id.mul (continuousAt_qq h0)
  have hd : ∀ s ∈ Ioo 0 b, HasDerivAt W (deriv f₀ (tt p s) / tt p s - qq s) s := by
    intro s hs
    have hs0 : s ≠ 0 := hs.1.ne'
    have ht := tt_pos (d := p) (s := s) hp
    have h1 := hasDerivAt_tt_s hp s
    have h2 : HasDerivAt (fun s => f₀ (tt p s) - f₀ p) (deriv f₀ (tt p s) * (s / tt p s)) s := by
      have := HasDerivAt.comp (h₂ := f₀) s (differentiableAt_f₀ ht).hasDerivAt h1
      exact this.sub_const _
    have h3 := h2.fun_div (hasDerivAt_id' s) hs0
    have e : W =ᶠ[𝓝 s] fun y => (f₀ (tt p y) - f₀ p) / y := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs0] with y hy
      simp only [hW, qq]
      field_simp
    refine (h3.congr_of_eventuallyEq e).congr_deriv ?_
    simp only [qq]
    field_simp
  have hi : IntervalIntegrable (fun s => deriv f₀ (tt p s) / tt p s - qq s) volume 0 b := by
    refine IntervalIntegrable.sub ?_ (intervalIntegrable_qq hb.le)
    exact (continuous_df₀_comp.div (continuous_tt p) fun s => (tt_pos hp).ne').intervalIntegrable 0 b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le hWc hd hi
  have hI1 : IntervalIntegrable (fun s => deriv f₀ (tt p s) / tt p s) volume 0 b :=
    (continuous_df₀_comp.div (continuous_tt p) fun s => (tt_pos hp).ne').intervalIntegrable 0 b
  rw [intervalIntegral.integral_sub hI1 (intervalIntegrable_qq hb.le)] at h
  simp only [hW, qq] at h
  have hb0 : b ≠ 0 := hb.ne'
  have : b * ((f₀ (tt p b) - f₀ p) / b ^ 2) - 0 * ((f₀ (tt p 0) - f₀ p) / 0 ^ 2)
      = (f₀ (tt p b) - f₀ p) / b := by field_simp; simp
  rw [this] at h
  simp only [qq]
  linarith


/-- `∫₀ᵇ s² e'(t)/t ds = b e(t(b)) - ∫₀ᵇ e(t) ds`. -/
theorem integral_de_mul {b : ℝ} :
    ∫ s in (0 : ℝ)..b, s ^ 2 * deriv e (tt p s) / tt p s
      = b * e (tt p b) - ∫ s in (0 : ℝ)..b, e (tt p s) := by
  have hp := p_pos
  have hd : ∀ s ∈ uIcc 0 b, HasDerivAt (fun s => s * e (tt p s))
      (e (tt p s) + s ^ 2 * deriv e (tt p s) / tt p s) s := by
    intro s _
    have ht := tt_pos (d := p) (s := s) hp
    have h1 := hasDerivAt_tt_s hp s
    have h2 : HasDerivAt (fun s => e (tt p s)) (deriv e (tt p s) * (s / tt p s)) s :=
      HasDerivAt.comp (h₂ := e) s (differentiableAt_e ht).hasDerivAt h1
    have := (hasDerivAt_id' s).fun_mul h2
    refine this.congr_deriv ?_
    field_simp
  have hc : Continuous fun s => e (tt p s) + s ^ 2 * deriv e (tt p s) / tt p s :=
    continuous_e_comp.add ((continuous_pow 2).mul continuous_de_comp |>.div (continuous_tt p)
      fun s => (tt_pos hp).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 b)
  have hI2 : IntervalIntegrable (fun s => s ^ 2 * deriv e (tt p s) / tt p s) volume 0 b :=
    ((continuous_pow 2).mul continuous_de_comp |>.div (continuous_tt p)
      fun s => (tt_pos hp).ne').intervalIntegrable 0 b
  rw [intervalIntegral.integral_add (continuous_e_comp.intervalIntegrable 0 b) hI2] at h
  simp only [zero_mul, sub_zero] at h
  linarith


/-- The defining relation of `λ` multiplied out: `λ x₀ = (f₀(R₀) - f₀(p))/x₀ - x₀ e(R₀)/p² +
∫ q + (1/p²) ∫ e(t)`. -/
theorem lam_mul_x₀ : lam * x₀ = (f₀ R₀ - f₀ p) / x₀ - x₀ * e R₀ / p ^ 2
    + (∫ s in (0 : ℝ)..x₀, qq s) + (∫ s in (0 : ℝ)..x₀, e (tt p s)) / p ^ 2 := by
  have hp := p_pos
  have hx := x₀_pos
  have key : lam = 1 / (p * x₀) * (p / x₀ * (f₀ R₀ - f₀ p) - x₀ / p * e R₀
      + p * (∫ s in (0 : ℝ)..x₀, qq s) + 1 / p * ∫ s in (0 : ℝ)..x₀, e (tt p s)) := by
    unfold lam; rfl
  rw [key]
  generalize (∫ s in (0 : ℝ)..x₀, qq s) = Iq
  generalize (∫ s in (0 : ℝ)..x₀, e (tt p s)) = Ie
  field_simp

theorem G_p_x₀_eq_zero : G p x₀ = 0 := by
  have hp := p_pos
  have hR := R₀_pos
  rw [G_at_p_x₀]
  have hf : f R₀ = e R₀ / 3 := by
    unfold f mu; ring
  rw [hf, x₀_sq]
  field_simp
  ring

/-- `∫₀^{x₀} A(p, s) ds = 0`: the integration by parts of the proof of `cal:stationarity`. -/
theorem integral_Aint_eq_zero : ∫ s in (0 : ℝ)..x₀, Aint p s = 0 := by
  have hp := p_pos
  have hx := x₀_pos
  have h1 := integral_df₀_div hx
  have h2 := integral_de_mul (b := x₀)
  rw [tt_p_x₀] at h1 h2
  have hI1 : IntervalIntegrable (fun s => deriv f₀ (tt p s) / tt p s) volume 0 x₀ :=
    (continuous_df₀_comp.div (continuous_tt p) fun s => (tt_pos hp).ne').intervalIntegrable 0 x₀
  have hI2 : IntervalIntegrable (fun s => s ^ 2 * deriv e (tt p s) / tt p s) volume 0 x₀ :=
    ((continuous_pow 2).mul continuous_de_comp |>.div (continuous_tt p)
      fun s => (tt_pos hp).ne').intervalIntegrable 0 x₀
  have e1 : ∀ s, Aint p s = (deriv f₀ (tt p s) / tt p s - lam)
      - (1 / p ^ 2) * (s ^ 2 * deriv e (tt p s) / tt p s) := by
    intro s
    have ht := tt_pos (d := p) (s := s) hp
    unfold Aint df
    field_simp
  simp_rw [e1]
  rw [intervalIntegral.integral_sub (hI1.sub intervalIntegrable_const) (hI2.const_mul _),
    intervalIntegral.integral_sub hI1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, h1, h2]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have := lam_mul_x₀
  linear_combination (-1 : ℝ) * this


theorem continuousOn_f : ContinuousOn f (Ioi 0) := by
  unfold f
  have := continuousOn_f₀
  fun_prop

theorem continuousOn_df : ContinuousOn df (Ioi 0) := by
  unfold df
  have := continuousOn_deriv_f₀
  fun_prop

theorem continuousOn_Gd : ContinuousOn (fun q : ℝ × ℝ => Gd q.1 q.2) (Ioi 0 ×ˢ univ) := by
  have hT : Continuous fun q : ℝ × ℝ => tt q.1 q.2 := by unfold tt; fun_prop
  have hTpos : MapsTo (fun q : ℝ × ℝ => tt q.1 q.2) (Ioi 0 ×ˢ univ) (Ioi 0) :=
    fun q hq => tt_pos hq.1
  have h1 := continuousOn_f.comp hT.continuousOn hTpos
  have h2 := continuousOn_df.comp hT.continuousOn hTpos
  have h3 := continuousOn_e.comp hT.continuousOn hTpos
  have h4 := continuousOn_deriv_e.comp hT.continuousOn hTpos
  have hne : ∀ q ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), tt q.1 q.2 ≠ 0 := fun q hq => (tt_pos hq.1).ne'
  have hd : ∀ q ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), q.1 ≠ 0 := fun q hq => hq.1.ne'
  have A := hT.continuousOn (s := (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)))
  have B : ContinuousOn (fun q : ℝ × ℝ => q.1) (Ioi 0 ×ˢ univ) := continuousOn_fst
  have C : ContinuousOn (fun q : ℝ × ℝ => q.2) (Ioi 0 ×ˢ univ) := continuousOn_snd
  have t1 := h1.div (A.pow 2) fun q hq => pow_ne_zero 2 (hne q hq)
  have t2 := ((B.pow 2).mul h2).div (A.pow 3) fun q hq => pow_ne_zero 3 (hne q hq)
  have t3 := ((continuousOn_const (c := (2 : ℝ))).mul (B.pow 2) |>.mul h1).div (A.pow 4)
    fun q hq => pow_ne_zero 4 (hne q hq)
  have t4 := ((C.pow 2).mul h3).div ((B.pow 2).mul (A.pow 2))
    fun q hq => mul_ne_zero (pow_ne_zero 2 (hd q hq)) (pow_ne_zero 2 (hne q hq))
  have t5 := ((C.pow 2).mul h4).div (A.pow 3) fun q hq => pow_ne_zero 3 (hne q hq)
  have t6 := ((continuousOn_const (c := (2 : ℝ))).mul (C.pow 2) |>.mul h3).div (A.pow 4)
    fun q hq => pow_ne_zero 4 (hne q hq)
  exact ((((t1.add t2).sub t3).add t4).sub t5).add t6


theorem continuous_G {d : ℝ} (hd : 0 < d) : Continuous (G d) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_G_s hd s).continuousAt

theorem continuous_Gd_p : Continuous (Gd p) := by
  have := continuousOn_Gd.comp_continuous (Continuous.prodMk continuous_const continuous_id)
    (fun s => (⟨p_pos, mem_univ s⟩ : (p, s) ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ))))
  exact this

theorem continuous_Aint_p : Continuous (Aint p) := by
  have hp := p_pos
  unfold Aint
  refine continuous_df_comp.div (continuous_tt p) (fun s => (tt_pos hp).ne') |>.sub ?_
  exact (((continuous_pow 2).mul continuous_de_comp).div (continuous_const.mul (continuous_tt p))
    fun s => (mul_pos (pow_pos hp 2) (tt_pos hp)).ne')

/-- `∫₀^{x₀} ∂_d G(p, s) ds = 0`. -/
theorem integral_Gd_eq_zero : ∫ s in (0 : ℝ)..x₀, Gd p s = 0 := by
  have hp := p_pos
  have hx := x₀_pos
  have hd : ∀ s ∈ uIcc (0 : ℝ) x₀, HasDerivAt (fun s => s * G p s / p)
      (Aint p s - Gd p s) s := by
    intro s _
    have h1 := (hasDerivAt_id' s).fun_mul (hasDerivAt_G_s hp s)
    have h2 := h1.div_const p
    refine h2.congr_deriv ?_
    rw [Gd_eq hp s]
    field_simp
    ring
  have hi : IntervalIntegrable (fun s => Aint p s - Gd p s) volume 0 x₀ :=
    (continuous_Aint_p.sub continuous_Gd_p).intervalIntegrable 0 x₀
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_sub (continuous_Aint_p.intervalIntegrable 0 x₀)
    (continuous_Gd_p.intervalIntegrable 0 x₀), integral_Aint_eq_zero, G_p_x₀_eq_zero] at h
  simp at h
  linarith

theorem hasDerivAt_g_d : HasDerivAt (fun d => g d x₀) (∫ s in (0 : ℝ)..x₀, Gd p s) p := by
  have hp := p_pos
  have hx := x₀_pos
  set S : Set (ℝ × ℝ) := Icc (p / 2) (2 * p) ×ˢ Icc 0 x₀ with hSdef
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSU : S ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨lt_of_lt_of_le (by positivity) hq.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (continuousOn_Gd.mono hSU)
  have hnhds : Ioo (p / 2) (2 * p) ∈ 𝓝 p := Ioo_mem_nhds (by linarith) (by linarith)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun d s => G d s)
    (F' := Gd) (bound := fun _ => M) hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Ioi_mem_nhds hp] with d hd
    exact (continuous_G hd).aestronglyMeasurable
  · exact (continuous_G hp).intervalIntegrable 0 x₀
  · exact continuous_Gd_p.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s hs x hx' => ?_
    rw [Set.uIoc_of_le hx.le] at hs
    exact hM (x, s) ⟨⟨hx'.1.le, hx'.2.le⟩, ⟨hs.1.le, hs.2⟩⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s _ x hx' =>
      hasDerivAt_G_d (lt_trans (by linarith) hx'.1) s

theorem hasDerivAt_g_x (x : ℝ) : HasDerivAt (g p) (G p x) x :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_G p_pos).intervalIntegrable 0 x)
    ((continuous_G p_pos).stronglyMeasurableAtFilter _ _) (continuous_G p_pos).continuousAt

/-- **`cal:stationarity`** (paper §5.5): `∇_{d,x} g_d(x) = 0` at `(p, x₀)`, as two partial derivatives. -/
theorem stationarity :
    HasDerivAt (fun d => g d x₀) 0 p ∧ HasDerivAt (g p) 0 x₀ := by
  refine ⟨?_, ?_⟩
  · have := hasDerivAt_g_d
    rwa [integral_Gd_eq_zero] at this
  · have := hasDerivAt_g_x x₀
    rwa [G_p_x₀_eq_zero] at this


end Calibration

end SandierSerfaty

end
