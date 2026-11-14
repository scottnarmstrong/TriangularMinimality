/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Stationarity
public import Mathlib.Analysis.Calculus.Taylor

/-!
# `comp:lambda-origin`: enclosing the first integral of `λ` at the removable singularity

paper `comp:lambda-origin`. With `t(s) = √(p² + s²)` and `s₀ > 0` the paper encloses
`p ∫₀^{s₀} (f₀(t(s)) - f₀(p))/s² ds` by

`f₀'(p) (s₀/2 - s₀³/(24 p²) + [0, s₀⁵/(80 p⁴)]) + (s₀³/6) [p/(√(p²+s₀²)+p)², 1/(4p)] · range_{[p, t(s₀)]} f₀''`.

`lambda_origin` states this as membership: there are `α, β, y` in the three sets of the display with the integral
equal to `f₀'(p)(s₀/2 - s₀³/(24 p²) + α) + (s₀³/6) β y` (`y` is a value of `f₀''` on `[p, t(s₀)]`; the range is
an interval, so the product of the bracket and the range is exactly the set of such products).

Proof: Lagrange's remainder for `f₀` at `p` (`taylor_f₀`; `f₀ ∈ C²` by `contDiffOn_f₀`) and `t - p = s²/(t + p)` give
`p q(s) = f₀'(p) c(s) + w(s) f₀''(ξ_s)` with `c = p/(t+p)`, `w = p s²/(2 (t+p)²)`; the bracket
`p/(t+p) = 1/2 - s²/(8p²) + [0, s⁴/(16p⁴)]` is the factorizations `(r-1)²(r+3)` and `(r-1)³(r²+4r+5)` in
`r = t/p` (`cc_bounds`); `∫ w` lies between `p s₀³/(6 (t₀+p)²)` and `s₀³/(24 p)` (`ww_bounds`); integrating
the sandwich `m w ≤ p q - f₀'(p) c ≤ M w` and the intermediate value theorem gives `y`.
-/

open Set Filter Topology MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

theorem continuousOn_deriv_deriv_f₀ : ContinuousOn (deriv (deriv f₀)) (Ioi 0) :=
  ((contDiffOn_f₀.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioi
    (m := 0) (by norm_num)).continuousOn

/-- Lagrange form of Taylor's formula for `f₀` at `p`. -/
theorem taylor_f₀ {t : ℝ} (ht : p < t) :
    ∃ ξ ∈ Ioo p t, f₀ t - f₀ p - deriv f₀ p * (t - p) = deriv (deriv f₀) ξ * (t - p) ^ 2 / 2 := by
  have hp := p_pos
  have hsub : uIcc p t ⊆ Ioi 0 := by
    rw [uIcc_of_le ht.le]; exact fun x hx => lt_of_lt_of_le hp hx.1
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := f₀) (n := 1) ht.ne
    (by have h2 := contDiffOn_f₀.mono hsub; convert h2 using 2; norm_num)
  rw [uIoo_of_le ht.le] at hξ
  refine ⟨ξ, hξ, ?_⟩
  rw [taylor_within_apply] at h
  have hu : UniqueDiffWithinAt ℝ (uIcc p t) p := by
    rw [uIcc_of_le ht.le]; exact uniqueDiffOn_Icc ht p ⟨le_rfl, ht.le⟩
  have hd1 : iteratedDerivWithin 1 f₀ (uIcc p t) p = deriv f₀ p := by
    rw [iteratedDerivWithin_one]
    exact (differentiableAt_f₀ hp).derivWithin hu
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
    inv_one, pow_zero, one_mul, iteratedDerivWithin_zero, Nat.factorial_one, pow_one,
    hd1, smul_eq_mul] at h
  have h2 : iteratedDeriv 2 f₀ ξ = deriv (deriv f₀) ξ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2] at h
  simp only [Nat.factorial] at h
  norm_num at h
  linarith


/-! ### The weights `c(s) = p/(t+p)` and `w(s) = p s²/(2 (t+p)²)` -/

@[expose] noncomputable def cc (s : ℝ) : ℝ := p / (tt p s + p)

@[expose] noncomputable def ww (s : ℝ) : ℝ := p * s ^ 2 / (2 * (tt p s + p) ^ 2)

theorem tt_add_p_pos (s : ℝ) : 0 < tt p s + p := by have := tt_pos (d := p) (s := s) p_pos; linarith [p_pos]

theorem continuous_cc : Continuous cc := by
  unfold cc
  exact continuous_const.div ((continuous_tt p).add continuous_const) fun s => (tt_add_p_pos s).ne'

theorem continuous_ww : Continuous ww := by
  unfold ww
  exact (continuous_const.mul (continuous_pow 2)).div
    (continuous_const.mul (((continuous_tt p).add continuous_const).pow 2))
    fun s => (mul_pos two_pos (pow_pos (tt_add_p_pos s) 2)).ne'

theorem tt_sub_mul {s : ℝ} : (tt p s - p) * (tt p s + p) = s ^ 2 := by
  have := tt_sq (d := p) (s := s) p_pos
  nlinarith

theorem p_lt_tt {s : ℝ} (hs : s ≠ 0) : p < tt p s := by
  have h1 := tt_sq (d := p) (s := s) p_pos
  have h2 := tt_pos (d := p) (s := s) p_pos
  have hs2 : 0 < s ^ 2 := by positivity
  by_contra h
  push Not at h
  nlinarith [p_pos]

theorem p_le_tt (s : ℝ) : p ≤ tt p s := by
  by_cases hs : s = 0
  · subst hs; simp [tt, Real.sqrt_sq p_pos.le]
  · exact (p_lt_tt hs).le

theorem tt_mono {s s' : ℝ} (h0 : 0 ≤ s) (h : s ≤ s') : tt p s ≤ tt p s' := by
  unfold tt
  exact Real.sqrt_le_sqrt (by nlinarith)

theorem aux_lo {r : ℝ} (hr : 1 ≤ r) : 1 / 2 - (r ^ 2 - 1) / 8 ≤ 1 / (1 + r) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sq_nonneg (r - 1)) (by linarith : (0 : ℝ) ≤ r + 3)]

theorem aux_hi {r : ℝ} (hr : 1 ≤ r) :
    1 / (1 + r) ≤ 1 / 2 - (r ^ 2 - 1) / 8 + (r ^ 2 - 1) ^ 2 / 16 := by
  rw [div_le_iff₀ (by linarith)]
  have h : 0 ≤ (r - 1) ^ 3 * (r ^ 2 + 4 * r + 5) := by
    have : 0 ≤ r - 1 := by linarith
    positivity
  nlinarith [h]

theorem cc_bounds (s : ℝ) :
    1 / 2 - s ^ 2 / (8 * p ^ 2) ≤ cc s ∧ cc s ≤ 1 / 2 - s ^ 2 / (8 * p ^ 2) + s ^ 4 / (16 * p ^ 4) := by
  have hp := p_pos
  have ht := tt_pos (d := p) (s := s) hp
  have hr : 1 ≤ tt p s / p := by rw [le_div_iff₀ hp]; linarith [p_le_tt s]
  have hr2 : (tt p s / p) ^ 2 - 1 = s ^ 2 / p ^ 2 := by
    rw [div_pow, tt_sq hp]; field_simp; ring
  have hc : cc s = 1 / (1 + tt p s / p) := by
    unfold cc; field_simp; ring
  have h1 := aux_lo hr
  have h2 := aux_hi hr
  rw [hr2] at h1 h2
  rw [hc]
  constructor
  · convert h1 using 2; field_simp
  · convert h2 using 2
    · field_simp
    · field_simp

theorem ww_bounds {s s₀ : ℝ} (h0 : 0 ≤ s) (h : s ≤ s₀) :
    p * s ^ 2 / (2 * (tt p s₀ + p) ^ 2) ≤ ww s ∧ ww s ≤ s ^ 2 / (8 * p) := by
  have hp := p_pos
  have hts := p_le_tt s
  have hts₀ := tt_mono h0 h
  unfold ww
  constructor
  · have := tt_add_p_pos s
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  · rw [div_le_div_iff₀ (by have := tt_add_p_pos s; positivity) (by positivity)]
    have : 4 * p ^ 2 ≤ (tt p s + p) ^ 2 := by nlinarith
    nlinarith [sq_nonneg s]

/-- The pointwise Taylor decomposition `p q(s) = f₀'(p) c(s) + w(s) f₀''(ξ)`. -/
theorem pointwise_decomp {s : ℝ} (hs : 0 < s) :
    ∃ ξ ∈ Ioo p (tt p s), p * qq s = deriv f₀ p * cc s + ww s * deriv (deriv f₀) ξ := by
  have hp := p_pos
  have hpt := p_lt_tt hs.ne'
  obtain ⟨ξ, hξ, h⟩ := taylor_f₀ hpt
  refine ⟨ξ, hξ, ?_⟩
  have hsq := tt_sub_mul (s := s)
  have htp := tt_add_p_pos s
  have hA : f₀ (tt p s) - f₀ p = deriv f₀ p * (tt p s - p) + deriv (deriv f₀) ξ * (tt p s - p) ^ 2 / 2 := by
    linarith
  unfold qq cc ww
  rw [hA, ← hsq]
  have : tt p s - p ≠ 0 := by linarith
  field_simp


theorem int_sq (c s₀ : ℝ) : ∫ s in (0 : ℝ)..s₀, c * s ^ 2 = c * s₀ ^ 3 / 3 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring

theorem int_pow4 (c s₀ : ℝ) : ∫ s in (0 : ℝ)..s₀, c * s ^ 4 = c * s₀ ^ 5 / 5 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring

/-- **`comp:lambda-origin`**: for every `s₀ > 0`, with `t(s) = √(p² + s²)`,
`p ∫₀^{s₀} (f₀(t(s)) - f₀(p))/s² ds = f₀'(p) (s₀/2 - s₀³/(24 p²) + [0, s₀⁵/(80 p⁴)])
  + (s₀³/6) [p/(t(s₀) + p)², 1/(4p)] · range_{[p, t(s₀)]} f₀''`, the bracketed sets being those
of the paper (the two intervals and the range are given by the witnesses `α, β, y`). -/
theorem lambda_origin {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ α β y : ℝ, α ∈ Icc 0 (s₀ ^ 5 / (80 * p ^ 4)) ∧
      β ∈ Icc (p / (√(p ^ 2 + s₀ ^ 2) + p) ^ 2) (1 / (4 * p)) ∧
      y ∈ deriv (deriv f₀) '' Icc p (√(p ^ 2 + s₀ ^ 2)) ∧
      p * ∫ s in (0 : ℝ)..s₀, (f₀ (√(p ^ 2 + s ^ 2)) - f₀ p) / s ^ 2
        = deriv f₀ p * (s₀ / 2 - s₀ ^ 3 / (24 * p ^ 2) + α) + s₀ ^ 3 / 6 * β * y := by
  have hp := p_pos
  set t₀ := tt p s₀ with ht₀
  have hpt₀ : p ≤ t₀ := p_le_tt s₀
  have ht₀p := tt_add_p_pos s₀
  have hKsub : Icc p t₀ ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hp hx.1
  have hKc : ContinuousOn (deriv (deriv f₀)) (Icc p t₀) := continuousOn_deriv_deriv_f₀.mono hKsub
  obtain ⟨a₁, ha₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hpt₀) hKc
  obtain ⟨a₂, ha₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpt₀) hKc
  set m := deriv (deriv f₀) a₁ with hm
  set M := deriv (deriv f₀) a₂ with hM
  have hmM : m ≤ M := hmin ha₂
  -- integrability
  have hqi := intervalIntegrable_qq hs₀.le
  have hci : IntervalIntegrable cc volume 0 s₀ := continuous_cc.intervalIntegrable 0 s₀
  have hwi : IntervalIntegrable ww volume 0 s₀ := continuous_ww.intervalIntegrable 0 s₀
  have hPi : IntervalIntegrable (fun s => p * qq s - deriv f₀ p * cc s) volume 0 s₀ :=
    (hqi.const_mul p).sub (hci.const_mul _)
  -- weights
  set ω := ∫ s in (0 : ℝ)..s₀, ww s with hω
  have hωlo : p / (2 * (t₀ + p) ^ 2) * s₀ ^ 3 / 3 ≤ ω := by
    have h1 : ∫ s in (0 : ℝ)..s₀, p / (2 * (t₀ + p) ^ 2) * s ^ 2 ≤ ω := by
      refine intervalIntegral.integral_mono_on hs₀.le
        ((continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 s₀) hwi fun s hs => ?_
      have := (ww_bounds hs.1 hs.2).1
      convert this using 1
      ring
    rwa [int_sq] at h1
  have hωhi : ω ≤ 1 / (8 * p) * s₀ ^ 3 / 3 := by
    have h1 : ω ≤ ∫ s in (0 : ℝ)..s₀, 1 / (8 * p) * s ^ 2 := by
      refine intervalIntegral.integral_mono_on hs₀.le hwi
        ((continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 s₀) fun s hs => ?_
      have := (ww_bounds hs.1 hs.2).2
      convert this using 1
      ring
    rwa [int_sq] at h1
  have hωpos : 0 < ω := by
    refine lt_of_lt_of_le ?_ hωlo
    positivity
  -- the Taylor remainder integral
  set IP := ∫ s in (0 : ℝ)..s₀, (p * qq s - deriv f₀ p * cc s) with hIP
  have hIP_eq : IP = p * (∫ s in (0 : ℝ)..s₀, qq s) - deriv f₀ p * ∫ s in (0 : ℝ)..s₀, cc s := by
    rw [hIP, intervalIntegral.integral_sub (hqi.const_mul p) (hci.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hpt : ∀ s ∈ Ioo 0 s₀, m * ww s ≤ p * qq s - deriv f₀ p * cc s ∧
      p * qq s - deriv f₀ p * cc s ≤ M * ww s := by
    intro s hs
    obtain ⟨ξ, hξ, h⟩ := pointwise_decomp hs.1
    have hξK : ξ ∈ Icc p t₀ := ⟨hξ.1.le, hξ.2.le.trans (tt_mono hs.1.le hs.2.le)⟩
    have hw : 0 ≤ ww s := by
      unfold ww; have := tt_add_p_pos s; positivity
    have e : p * qq s - deriv f₀ p * cc s = ww s * deriv (deriv f₀) ξ := by linarith
    rw [e]
    constructor
    · nlinarith [hmin hξK, mul_le_mul_of_nonneg_left (hmin hξK) hw]
    · nlinarith [hmax hξK, mul_le_mul_of_nonneg_left (hmax hξK) hw]
  have hIlo : m * ω ≤ IP := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo hs₀.le (hwi.const_mul m) hPi
      fun s hs => (hpt s hs).1
    rwa [intervalIntegral.integral_const_mul] at this
  have hIhi : IP ≤ M * ω := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo hs₀.le hPi (hwi.const_mul M)
      fun s hs => (hpt s hs).2
    rwa [intervalIntegral.integral_const_mul] at this
  set y := IP / ω with hy
  have hy1 : m ≤ y := by rw [hy, le_div_iff₀ hωpos]; exact hIlo
  have hy2 : y ≤ M := by rw [hy, div_le_iff₀ hωpos]; exact hIhi
  have hyim : y ∈ deriv (deriv f₀) '' Icc p t₀ := by
    have hsub : uIcc a₁ a₂ ⊆ Icc p t₀ := uIcc_subset_Icc ha₁ ha₂
    have h1 := intermediate_value_uIcc (hKc.mono hsub)
    have h2 : y ∈ uIcc m M := by rw [uIcc_of_le hmM]; exact ⟨hy1, hy2⟩
    exact image_mono hsub (h1 h2)
  -- the `c`-part
  have hhi : IntervalIntegrable (fun s : ℝ => 1 / 2 - 1 / (8 * p ^ 2) * s ^ 2) volume 0 s₀ :=
    (continuous_const.sub (continuous_const.mul (continuous_pow 2))).intervalIntegrable 0 s₀
  have hcb : ∀ s : ℝ, 1 / 2 - 1 / (8 * p ^ 2) * s ^ 2 = 1 / 2 - s ^ 2 / (8 * p ^ 2) := fun s => by
    field_simp
  set α := ∫ s in (0 : ℝ)..s₀, (cc s - (1 / 2 - 1 / (8 * p ^ 2) * s ^ 2)) with hα
  have hα0 : 0 ≤ α := by
    refine intervalIntegral.integral_nonneg hs₀.le fun s _ => ?_
    rw [hcb]; exact sub_nonneg.2 (cc_bounds s).1
  have hα1 : α ≤ s₀ ^ 5 / (80 * p ^ 4) := by
    have h1 : α ≤ ∫ s in (0 : ℝ)..s₀, 1 / (16 * p ^ 4) * s ^ 4 := by
      refine intervalIntegral.integral_mono_on hs₀.le (hci.sub hhi)
        ((continuous_const.mul (continuous_pow 4)).intervalIntegrable 0 s₀) fun s _ => ?_
      have := (cc_bounds s).2
      rw [hcb]
      have e : 1 / (16 * p ^ 4) * s ^ 4 = s ^ 4 / (16 * p ^ 4) := by ring
      rw [e]; linarith
    rw [int_pow4] at h1
    convert h1 using 1; field_simp; ring
  have hh : ∫ s in (0 : ℝ)..s₀, (1 / 2 - 1 / (8 * p ^ 2) * s ^ 2) = s₀ / 2 - 1 / (8 * p ^ 2) * s₀ ^ 3 / 3 := by
    have hq : IntervalIntegrable (fun s : ℝ => 1 / (8 * p ^ 2) * s ^ 2) volume 0 s₀ :=
      (continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 s₀
    rw [intervalIntegral.integral_sub intervalIntegrable_const hq, int_sq]
    simp
    ring
  have hcα : ∫ s in (0 : ℝ)..s₀, cc s = s₀ / 2 - s₀ ^ 3 / (24 * p ^ 2) + α := by
    have := intervalIntegral.integral_sub hci hhi
    rw [hh] at this
    rw [hα, this]
    field_simp
    ring
  -- the `β` part
  set β := ω / (s₀ ^ 3 / 6) with hβ
  have hs3 : 0 < s₀ ^ 3 / 6 := by positivity
  have hβ1 : p / (t₀ + p) ^ 2 ≤ β := by
    rw [hβ, le_div_iff₀ hs3]
    have : p / (t₀ + p) ^ 2 * (s₀ ^ 3 / 6) = p / (2 * (t₀ + p) ^ 2) * s₀ ^ 3 / 3 := by
      field_simp; ring
    rw [this]; exact hωlo
  have hβ2 : β ≤ 1 / (4 * p) := by
    rw [hβ, div_le_iff₀ hs3]
    have : 1 / (4 * p) * (s₀ ^ 3 / 6) = 1 / (8 * p) * s₀ ^ 3 / 3 := by
      field_simp; ring
    rw [this]; exact hωhi
  refine ⟨α, β, y, ⟨hα0, hα1⟩, ⟨hβ1, hβ2⟩, hyim, ?_⟩
  have hωβ : ω = s₀ ^ 3 / 6 * β := by rw [hβ]; field_simp
  have hIy : IP = ω * y := by rw [hy]; field_simp
  have := hIP_eq
  rw [hIy, hωβ, hcα] at this
  show p * ∫ s in (0 : ℝ)..s₀, qq s = _
  linarith

/-- The instance `s₀ = .01` of paper `comp:lambda-origin`. -/
theorem lambda_origin_hundredth :
    ∃ α β y : ℝ, α ∈ Icc 0 ((1 / 100 : ℝ) ^ 5 / (80 * p ^ 4)) ∧
      β ∈ Icc (p / (√(p ^ 2 + (1 / 100 : ℝ) ^ 2) + p) ^ 2) (1 / (4 * p)) ∧
      y ∈ deriv (deriv f₀) '' Icc p (√(p ^ 2 + (1 / 100 : ℝ) ^ 2)) ∧
      p * ∫ s in (0 : ℝ)..(1 / 100 : ℝ), (f₀ (√(p ^ 2 + s ^ 2)) - f₀ p) / s ^ 2
        = deriv f₀ p * ((1 / 100 : ℝ) / 2 - (1 / 100 : ℝ) ^ 3 / (24 * p ^ 2) + α)
          + (1 / 100 : ℝ) ^ 3 / 6 * β * y :=
  lambda_origin (by norm_num)

end Calibration

end SandierSerfaty

end
