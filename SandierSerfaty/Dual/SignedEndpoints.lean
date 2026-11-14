/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Signed endpoint parameters (paper Lemma `dual:signed-endpoints`)

For an even locally integrable `G : ℝ → ℝ` with primitive `g x = ∫₀ˣ G`, suppose
`K ≤ 2 g x` for `x ≥ 0` and `∫₀^∞ max {0, -G} ≤ -K`. Then
`K ≤ g (d tan α) + g (d tan β)` for `d > 0`, `|α|, |β| < π/2`, `α + β > 0`.

* `primitive0 G x = ∫₀ˣ G`;
* `primitive0_add_ge`: the real-variable form, `K ≤ g x + g y` whenever `0 < x + y`;
* `signed_endpoints`: the lemma, for a family `G : ℝ → ℝ → ℝ` indexed by `d ≥ d₀`
  (`d₀ > 0`; `G d` is the function `G(d, ·)`).

The integral `∫₀^∞ max {0, -G}` is the Lebesgue integral of a nonnegative function, formalized as a
`lintegral` (so that the value `+∞` is excluded by the hypothesis, as in the paper). The paper states
`K < 0` in the lemma and `K ≤ 0` in the proposition; the proof needs no sign
of `K` (the hypotheses at `x = 0` already give `K ≤ 0`), so no sign hypothesis appears here.
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty

namespace Dual

/-- The primitive `g x = ∫₀ˣ G` of `G` (the paper's `g_d`). -/
@[expose] noncomputable def primitive0 (G : ℝ → ℝ) (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, G s

variable {G : ℝ → ℝ}

theorem primitive0_zero (G : ℝ → ℝ) : primitive0 G 0 = 0 := by simp [primitive0]

/-- Evenness of `G` makes `g` odd. -/
theorem primitive0_neg (hG : ∀ s, G (-s) = G s) (x : ℝ) : primitive0 G (-x) = -primitive0 G x := by
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) (fun s => G s)
  simp only [hG, neg_zero] at h
  unfold primitive0
  rw [h]
  exact intervalIntegral.integral_symm (-x) 0

theorem intervalIntegrable_of_locallyIntegrable (hGi : LocallyIntegrable G) (a b : ℝ) :
    IntervalIntegrable G volume a b := by
  rw [intervalIntegrable_iff]
  exact (hGi.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc

theorem primitive0_sub (hGi : LocallyIntegrable G) (u v : ℝ) :
    primitive0 G v - primitive0 G u = ∫ s in u..v, G s :=
  intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_locallyIntegrable hGi _ _)
    (intervalIntegrable_of_locallyIntegrable hGi _ _)

/-- `∫_u^v G ≥ -∫_{(0,∞)} max {0, -G} ≥ K` for `0 ≤ u ≤ v`. -/
theorem le_intervalIntegral_of_lintegral_le {K : ℝ} (hGi : LocallyIntegrable G) (hK : K ≤ 0)
    (h2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max 0 (-G s)) ≤ ENNReal.ofReal (-K))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : K ≤ ∫ s in u..v, G s := by
  set f : ℝ → ℝ := fun s => max 0 (-G s) with hf
  have hGint : IntegrableOn G (Icc u v) := hGi.integrableOn_isCompact isCompact_Icc
  have hfint : IntegrableOn f (Icc u v) := by
    have : IntegrableOn (fun s => max (-G s) 0) (Icc u v) := hGint.neg.pos_part
    exact this.congr_fun (fun s _ => max_comm _ _) measurableSet_Icc
  have hfIoc : IntegrableOn f (Ioc u v) := hfint.mono_set Ioc_subset_Icc_self
  have hGIoc : IntegrableOn G (Ioc u v) := hGint.mono_set Ioc_subset_Icc_self
  have hnn : ∀ s, 0 ≤ f s := fun s => le_max_left _ _
  -- the integral of `f` over `(u, v]` is at most `-K`
  have h3 : ∫ s in Ioc u v, f s ≤ -K := by
    have hle : ENNReal.ofReal (∫ s in Ioc u v, f s) ≤ ENNReal.ofReal (-K) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfIoc (Filter.Eventually.of_forall hnn)]
      exact (lintegral_mono_set (fun s hs => (lt_of_le_of_lt hu hs.1 : (0 : ℝ) < s))).trans h2
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hle
  -- `G + f = max G 0 ≥ 0`
  have h4 : 0 ≤ ∫ s in Ioc u v, (G s + f s) := by
    refine setIntegral_nonneg measurableSet_Ioc fun s _ => ?_
    simp only [hf]
    rcases le_total 0 (G s) with h | h
    · rw [max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith)]; linarith
  rw [integral_add hGIoc hfIoc] at h4
  rw [intervalIntegral.integral_of_le huv]
  linarith

/-- **Real-variable form of the signed endpoint bound**: `K ≤ g x + g y` whenever `x + y > 0`. -/
theorem primitive0_add_ge (hGe : ∀ s, G (-s) = G s) (hGi : LocallyIntegrable G) {K : ℝ}
    (h1 : ∀ x, 0 ≤ x → K ≤ 2 * primitive0 G x)
    (h2 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max 0 (-G s)) ≤ ENNReal.ofReal (-K))
    {x y : ℝ} (hxy : 0 < x + y) : K ≤ primitive0 G x + primitive0 G y := by
  have hK : K ≤ 0 := by have := h1 0 le_rfl; rw [primitive0_zero] at this; linarith
  have key : ∀ x y : ℝ, x < 0 → 0 < x + y → K ≤ primitive0 G x + primitive0 G y := by
    intro x y hx hxy
    have hodd : primitive0 G x = -primitive0 G (-x) := by
      have := primitive0_neg hGe (-x); rwa [neg_neg] at this
    have := le_intervalIntegral_of_lintegral_le hGi hK h2 (u := -x) (v := y) (by linarith)
      (by linarith)
    rw [← primitive0_sub hGi] at this
    linarith
  rcases lt_or_ge x 0 with hx | hx
  · exact key x y hx hxy
  rcases lt_or_ge y 0 with hy | hy
  · rw [add_comm]; exact key y x hy (by linarith)
  · linarith [h1 x hx, h1 y hy]

/-- **Lemma `dual:signed-endpoints`.** For `d₀ > 0` and each `d ≥ d₀` let `G d` be an even locally
integrable function with `K ≤ 2 g_d x` (`x ≥ 0`) and `∫₀^∞ max {0, -G d} ≤ -K`, where `g_d` is the
primitive of `G d`. Then `K ≤ g_d (d tan α) + g_d (d tan β)` for every `d ≥ d₀` and all `|α|, |β| < π/2`
with `α + β > 0`. -/
theorem signed_endpoints {d₀ K : ℝ} (hd₀ : 0 < d₀) (G : ℝ → ℝ → ℝ)
    (hGe : ∀ d, d₀ ≤ d → ∀ s, G d (-s) = G d s)
    (hGi : ∀ d, d₀ ≤ d → LocallyIntegrable (G d))
    (h1 : ∀ d, d₀ ≤ d → ∀ x, 0 ≤ x → K ≤ 2 * primitive0 (G d) x)
    (h2 : ∀ d, d₀ ≤ d →
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max 0 (-G d s)) ≤ ENNReal.ofReal (-K))
    {d : ℝ} (hd : d₀ ≤ d) {α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) (hαβ : 0 < α + β) :
    K ≤ primitive0 (G d) (d * Real.tan α) + primitive0 (G d) (d * Real.tan β) := by
  have hdpos : 0 < d := lt_of_lt_of_le hd₀ hd
  have hmem : ∀ γ : ℝ, |γ| < π / 2 → γ ∈ Ioo (-(π / 2)) (π / 2) := fun γ h =>
    ⟨by linarith [(abs_lt.1 h).1], (abs_lt.1 h).2⟩
  have hlt : -α < β := by linarith
  have htan : Real.tan (-α) < Real.tan β := by
    refine Real.strictMonoOn_tan ?_ (hmem β hβ) hlt
    exact ⟨by linarith [(abs_lt.1 hα).2], by linarith [(abs_lt.1 hα).1]⟩
  rw [Real.tan_neg] at htan
  refine primitive0_add_ge (hGe d hd) (hGi d hd) (h1 d hd) (h2 d hd) ?_
  nlinarith

end Dual

end SandierSerfaty

end
