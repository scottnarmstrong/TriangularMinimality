/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Stationarity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The sector primitive `g_d` and the angle substitution (`cal:sector-primitive`)

paper `cal:primitive`, `cal:sector-primitive`. With `G(d, s) = d f(t)/t² - s² e(t)/(d t²)`, `t = √(d² + s²)`, and the angle density
`F_d(φ) = f₀(d sec φ) - tan²φ e(d sec φ)` of `cal:angle-density`, the substitution `s = d tan φ` gives

* `integral_G_eq`: `g_d(d tan β) = ∫₀^β (f(d sec φ) - tan²φ e(d sec φ)) dφ` for `|β| < π/2`
  (`f = f₀ - λ t²/2 - μ`), for *signed* `β`;
* `angleDensity_sub_eq`: `∫_{-α}^β F_d - λ A - μ θ = g_d(d tan α) + g_d(d tan β)` with `A = d²(tan α + tan β)/2`,
  `θ = α + β`, for `|α|, |β| < π/2` (the identity holds for signed endpoint angles, paper §5.5).
-/

open Set MeasureTheory intervalIntegral Real

public section

namespace SandierSerfaty

namespace Calibration

/-- The angle density `F_d(φ) = f₀(d sec φ) - tan²φ e(d sec φ)` of `cal:angle-density`. -/
@[expose] noncomputable def angleDensity (d φ : ℝ) : ℝ :=
  f₀ (d / Real.cos φ) - Real.tan φ ^ 2 * e (d / Real.cos φ)

theorem tt_d_tan {d φ : ℝ} (hd : 0 < d) (hφ : |φ| < π / 2) : tt d (d * Real.tan φ) = d / Real.cos φ := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (abs_lt.1 hφ)
  unfold tt
  rw [Real.tan_eq_sin_div_cos]
  have : d ^ 2 + (d * (Real.sin φ / Real.cos φ)) ^ 2 = (d / Real.cos φ) ^ 2 := by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq φ]
  rw [this, Real.sqrt_sq (by positivity)]

theorem G_comp_tan_mul {d φ : ℝ} (hd : 0 < d) (hφ : |φ| < π / 2) :
    G d (d * Real.tan φ) * (d / Real.cos φ ^ 2) = f (d / Real.cos φ) - Real.tan φ ^ 2 * e (d / Real.cos φ) := by
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo (abs_lt.1 hφ)
  unfold G
  rw [tt_d_tan hd hφ, Real.tan_eq_sin_div_cos]
  field_simp

/-- **The angle substitution** `s = d tan φ`: `g_d(d tan β) = ∫₀^β (f - tan² e)(d sec φ) dφ`, signed `β`. -/
theorem integral_G_eq {d β : ℝ} (hd : 0 < d) (hβ : |β| < π / 2) :
    g d (d * Real.tan β) =
      ∫ φ in (0 : ℝ)..β, (f (d / Real.cos φ) - Real.tan φ ^ 2 * e (d / Real.cos φ)) := by
  have hcos : ∀ φ ∈ uIcc (0 : ℝ) β, Real.cos φ ≠ 0 := fun φ hφ => by
    have : |φ| < π / 2 := by
      rcases le_total 0 β with h | h
      · rw [uIcc_of_le h] at hφ
        rw [abs_of_nonneg hφ.1]; exact lt_of_le_of_lt hφ.2 (by rwa [abs_of_nonneg h] at hβ)
      · rw [uIcc_of_ge h] at hφ
        rw [abs_of_nonpos hφ.2]
        have := abs_lt.1 hβ
        linarith [hφ.1]
    exact (Real.cos_pos_of_mem_Ioo (abs_lt.1 this)).ne'
  have hder : ∀ φ ∈ uIcc (0 : ℝ) β, HasDerivAt (fun φ => d * Real.tan φ) (d / Real.cos φ ^ 2) φ := by
    intro φ hφ
    have := (Real.hasDerivAt_tan (hcos φ hφ)).const_mul d
    simpa [div_eq_mul_inv] using this
  have hcont : ContinuousOn (fun φ => d / Real.cos φ ^ 2) (uIcc 0 β) :=
    continuousOn_const.div (Real.continuous_cos.pow 2).continuousOn fun φ hφ => pow_ne_zero 2 (hcos φ hφ)
  have h := integral_comp_mul_deriv hder hcont (continuous_G hd)
  have e0 : d * Real.tan 0 = 0 := by simp
  rw [e0] at h
  unfold g
  rw [← h]
  refine integral_congr fun φ hφ => ?_
  have hφ' : |φ| < π / 2 := by
    have := hcos φ hφ
    rcases le_total 0 β with hb | hb
    · rw [uIcc_of_le hb] at hφ
      rw [abs_of_nonneg hφ.1]; exact lt_of_le_of_lt hφ.2 (by rwa [abs_of_nonneg hb] at hβ)
    · rw [uIcc_of_ge hb] at hφ
      rw [abs_of_nonpos hφ.2]
      have := abs_lt.1 hβ
      linarith [hφ.1]
  simp only [Function.comp]
  exact G_comp_tan_mul hd hφ'

/-- **The derivative of the sector primitive**: `∂ₓ g_d(x) = G(d, x)` (paper `cal:primitive`). -/
theorem hasDerivAt_g {d : ℝ} (hd : 0 < d) (x : ℝ) : HasDerivAt (g d) (G d x) x :=
  ((continuous_G hd).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem uIcc_subset_Ioo {α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    uIcc (-α) β ⊆ Ioo (-(π / 2)) (π / 2) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hα
  obtain ⟨h3, h4⟩ := abs_lt.1 hβ
  intro x hx
  rcases le_total (-α) β with h | h
  · rw [uIcc_of_le h] at hx; constructor <;> linarith [hx.1, hx.2]
  · rw [uIcc_of_ge h] at hx; constructor <;> linarith [hx.1, hx.2]

theorem continuousOn_angleDensity {d : ℝ} (hd : 0 < d) :
    ContinuousOn (angleDensity d) (Ioo (-(π / 2)) (π / 2)) := by
  have hcos : ∀ φ ∈ Ioo (-(π / 2)) (π / 2), 0 < Real.cos φ := fun φ hφ => Real.cos_pos_of_mem_Ioo hφ
  have ht : ContinuousOn (fun φ => d / Real.cos φ) (Ioo (-(π / 2)) (π / 2)) :=
    continuousOn_const.div Real.continuous_cos.continuousOn fun φ hφ => (hcos φ hφ).ne'
  have hmaps : MapsTo (fun φ => d / Real.cos φ) (Ioo (-(π / 2)) (π / 2)) (Ioi 0) :=
    fun φ hφ => div_pos hd (hcos φ hφ)
  unfold angleDensity
  exact (continuousOn_f₀.comp ht hmaps).sub
    ((Real.continuousOn_tan.mono fun φ hφ => (hcos φ hφ).ne').pow 2 |>.mul (continuousOn_e.comp ht hmaps))

/-- **`cal:sector-primitive`**: `∫_{-α}^β F_d - λ A - μ θ = g_d(d tan α) + g_d(d tan β)`,
for signed endpoint angles. -/
theorem integral_angleDensity_sub {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    (∫ φ in (-α)..β, angleDensity d φ) - lam * (d ^ 2 * (Real.tan α + Real.tan β) / 2) - mu * (α + β) =
      g d (d * Real.tan α) + g d (d * Real.tan β) := by
  have hsub := uIcc_subset_Ioo hα hβ
  have hcos : ∀ φ ∈ uIcc (-α) β, 0 < Real.cos φ := fun φ hφ => Real.cos_pos_of_mem_Ioo (hsub hφ)
  have hΦ : ∀ x : ℝ, |x| < π / 2 → ContinuousOn (fun φ => f (d / Real.cos φ) -
      Real.tan φ ^ 2 * e (d / Real.cos φ)) (uIcc 0 x) := by
    intro x hx
    have h0 : (0 : ℝ) ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hsub' : uIcc 0 x ⊆ Ioo (-(π / 2)) (π / 2) := by
      have := uIcc_subset_Ioo (α := 0) (β := x) (by simpa using (by linarith [pi_pos] : |(0:ℝ)| < π / 2)) hx
      simpa using this
    have hc := (continuousOn_angleDensity hd).mono hsub'
    have hl : ContinuousOn (fun φ => lam * (d / Real.cos φ) ^ 2 / 2 + mu) (uIcc 0 x) := by
      refine ContinuousOn.add (ContinuousOn.div_const (continuousOn_const.mul ?_) 2) continuousOn_const
      exact (continuousOn_const.div Real.continuous_cos.continuousOn fun φ hφ =>
        (Real.cos_pos_of_mem_Ioo (hsub' hφ)).ne').pow 2
    refine (hc.sub hl).congr fun φ hφ => ?_
    simp only [Pi.sub_apply, angleDensity, f]
    ring
  set Φ : ℝ → ℝ := fun φ => f (d / Real.cos φ) - Real.tan φ ^ 2 * e (d / Real.cos φ) with hΦdef
  have hint : ∀ x : ℝ, |x| < π / 2 → IntervalIntegrable Φ volume 0 x := fun x hx =>
    (hΦ x hx).intervalIntegrable
  have hαneg : |-α| < π / 2 := by rwa [abs_neg]
  have h1 := integral_G_eq hd hβ
  have h2 := integral_G_eq hd hαneg
  have hsplit : ∫ φ in (-α)..β, Φ φ = (∫ φ in (0 : ℝ)..β, Φ φ) - ∫ φ in (0 : ℝ)..(-α), Φ φ := by
    rw [← integral_add_adjacent_intervals (a := -α) (b := 0) (c := β)]
    · rw [integral_symm (a := 0) (b := -α)]; ring
    · exact (hint (-α) hαneg).symm
    · exact hint β hβ
  have h2' : g d (d * Real.tan (-α)) = ∫ φ in (0 : ℝ)..(-α), Φ φ := h2
  have e1 : g d (d * Real.tan (-α)) = -g d (d * Real.tan α) := by rw [Real.tan_neg, mul_neg, g_neg]
  have hgα : g d (d * Real.tan α) = -∫ φ in (0 : ℝ)..(-α), Φ φ := by linarith
  have hgβ : g d (d * Real.tan β) = ∫ φ in (0 : ℝ)..β, Φ φ := h1
  -- the area and angle part
  set L : ℝ → ℝ := fun φ => lam * (d / Real.cos φ) ^ 2 / 2 + mu with hL
  have hLint : ∫ φ in (-α)..β, L φ = lam * (d ^ 2 * (Real.tan α + Real.tan β) / 2) + mu * (α + β) := by
    have hder : ∀ φ ∈ uIcc (-α) β, HasDerivAt (fun φ => lam * d ^ 2 / 2 * Real.tan φ + mu * φ) (L φ) φ := by
      intro φ hφ
      have hc := (hcos φ hφ).ne'
      have := (((Real.hasDerivAt_tan hc).const_mul (lam * d ^ 2 / 2)).add ((hasDerivAt_id φ).const_mul mu))
      refine this.congr_deriv ?_
      simp only [hL]
      field_simp
    have hLc : ContinuousOn L (uIcc (-α) β) := by
      refine ContinuousOn.add (ContinuousOn.div_const (continuousOn_const.mul ?_) 2) continuousOn_const
      exact (continuousOn_const.div Real.continuous_cos.continuousOn fun φ hφ => (hcos φ hφ).ne').pow 2
    rw [integral_eq_sub_of_hasDerivAt hder (hLc.intervalIntegrable)]
    simp only [Real.tan_neg]
    ring
  have hΦint : IntervalIntegrable Φ volume (-α) β := by
    have : ContinuousOn Φ (uIcc (-α) β) := by
      have hc := (continuousOn_angleDensity hd).mono hsub
      have hl : ContinuousOn L (uIcc (-α) β) := by
        refine ContinuousOn.add (ContinuousOn.div_const (continuousOn_const.mul ?_) 2) continuousOn_const
        exact (continuousOn_const.div Real.continuous_cos.continuousOn fun φ hφ => (hcos φ hφ).ne').pow 2
      refine (hc.sub hl).congr fun φ hφ => ?_
      simp only [Pi.sub_apply, angleDensity, f, hL, hΦdef]
      ring
    exact this.intervalIntegrable
  have hLi : IntervalIntegrable L volume (-α) β := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.add (ContinuousOn.div_const (continuousOn_const.mul ?_) 2) continuousOn_const
    exact (continuousOn_const.div Real.continuous_cos.continuousOn fun φ hφ => (hcos φ hφ).ne').pow 2
  have hsum : ∫ φ in (-α)..β, angleDensity d φ = (∫ φ in (-α)..β, Φ φ) + ∫ φ in (-α)..β, L φ := by
    rw [← integral_add hΦint hLi]
    refine integral_congr fun φ hφ => ?_
    simp only [angleDensity, f, hL, hΦdef]
    ring
  rw [hsum, hLint, hsplit, hgα, hgβ]
  ring

end Calibration

end SandierSerfaty

end
