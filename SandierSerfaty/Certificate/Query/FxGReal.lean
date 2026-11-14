/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The real error calculus of the value-`G` evaluation

Pure real statements behind `Query.FxGSound`: the rounding errors of the operations of `Query.FxG` (each below
one ulp `u = 2^-128`) propagate through `V = (A - B)/T2` to an error of at most `2^40 u` beyond the
propagated input errors `(ρF + ρE)/b`.

* `abs_sqrt_sub_sqrt_le`: `|√x - √y| ≤ |x - y|/√y`;
* `combine_error`: the final bound for `V` against `(d f - (s²/d) e)/t²`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

theorem abs_sqrt_sub_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / Real.sqrt y := by
  have hy' : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hx' : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    have := Real.sq_sqrt hx
    have := Real.sq_sqrt hy.le
    nlinarith
  rw [le_div_iff₀ hy']
  have h2 : |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) = |x - y| := by
    rw [← abs_of_pos (show 0 < Real.sqrt x + Real.sqrt y by linarith), ← abs_mul, h]
  nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]

/-- **The final bound of the value-`G` evaluation.** `A ≈ d·fa`, `q ≈ s²/d`, `B ≈ q·ev`, `V ≈ (A - B)/T2` with
rounding errors `≤ u`, `T2 ≈ t²` within `2u`, and `fa ≈ f`, `ev ≈ e` within the propagated radii `ρF`, `ρE ≤ 1`
(the computed `fa`, `ev` have magnitude `≤ 2^23`); then `V` is within `(ρF + ρE)/b + 2^40 u` of
`G = (d f - (s²/d) e)/t²`. -/
theorem combine_error {u dv sv t f e T2 A q Bq fa ev V bb ρF ρE : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 100)
    (hbb : 1 / 4 ≤ bb) (hd : bb ≤ dv) (hdt : dv ≤ t) (ht7 : t ≤ 7 / 10) (ht2 : t ^ 2 = dv ^ 2 + sv ^ 2)
    (hT2 : |T2 - t ^ 2| ≤ 2 * u) (hfa : |fa - f| ≤ ρF) (hev : |ev - e| ≤ ρE) (hρF1 : ρF ≤ 1)
    (hρE1 : ρE ≤ 1) (hfaM : |fa| ≤ 2 ^ 23) (hevM : |ev| ≤ 2 ^ 23) (hA : |A - dv * fa| ≤ u)
    (hq : |q - sv ^ 2 / dv| ≤ 5 * u) (hB : |Bq - q * ev| ≤ u) (hV : |V - (A - Bq) / T2| ≤ u) :
    |V - (dv * f - sv ^ 2 / dv * e) / t ^ 2| ≤ (ρF + ρE) / bb + 2 ^ 40 * u := by
  have hρF0 : 0 ≤ ρF := (abs_nonneg _).trans hfa
  have hρE0 : 0 ≤ ρE := (abs_nonneg _).trans hev
  have hu1 : u ≤ 1 / 1000 := hu.trans (by norm_num)
  have hdpos : 0 < dv := by linarith
  have hτ : t ^ 2 = dv ^ 2 + sv ^ 2 := ht2
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = t ^ 2 := ⟨_, rfl⟩
  rw [← hτdef] at hT2 hτ ⊢
  have hτlo : dv ^ 2 ≤ τ := by rw [hτ]; nlinarith [sq_nonneg sv]
  have hτ16 : 1 / 16 ≤ τ := by nlinarith
  have hτhi : τ ≤ 49 / 100 := by nlinarith
  have hτpos : 0 < τ := by linarith
  have hsv : sv ^ 2 ≤ τ := by rw [hτ]; nlinarith [sq_nonneg dv]
  obtain ⟨g1, hg1⟩ : ∃ g1, g1 = sv ^ 2 / dv := ⟨_, rfl⟩
  rw [← hg1] at hq
  have hg1nn : 0 ≤ g1 := by rw [hg1]; positivity
  have hg1le : g1 ≤ 2 := by
    rw [hg1, div_le_iff₀ hdpos]; nlinarith
  have hT2lo : 1 / 20 ≤ T2 := by
    have := (abs_le.1 hT2).1
    linarith
  have hT2pos : 0 < T2 := by linarith
  -- the exact numerator
  obtain ⟨num, hnum⟩ : ∃ num, num = A - Bq := ⟨_, rfl⟩
  obtain ⟨numS, hnumS⟩ : ∃ numS, numS = dv * f - g1 * e := ⟨_, rfl⟩
  rw [← hnum] at hV
  have e1 : |A - dv * f| ≤ u + dv * ρF := by
    have : A - dv * f = (A - dv * fa) + dv * (fa - f) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add hA ?_)
    rw [abs_mul, abs_of_pos hdpos]
    exact mul_le_mul_of_nonneg_left hfa hdpos.le
  have e2 : |Bq - g1 * e| ≤ u + 5 * u * 2 ^ 23 + g1 * ρE := by
    have : Bq - g1 * e = (Bq - q * ev) + (q - g1) * ev + g1 * (ev - e) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hB ?_)) ?_)
    · rw [abs_mul]
      exact mul_le_mul hq hevM (abs_nonneg _) (by positivity)
    · rw [abs_mul, abs_of_nonneg hg1nn]
      exact mul_le_mul_of_nonneg_left hev hg1nn
  have e3 : |num - numS| ≤ dv * ρF + g1 * ρE + (2 + 5 * 2 ^ 23) * u := by
    have : num - numS = (A - dv * f) - (Bq - g1 * e) := by rw [hnum, hnumS]; ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    nlinarith [e1, e2]
  have e3' : |num - numS| ≤ 4 := by
    have h1 : dv * ρF ≤ 7 / 10 * 1 := mul_le_mul (hdt.trans ht7) hρF1 hρF0 (by norm_num)
    have h2 : g1 * ρE ≤ 2 * 1 := mul_le_mul hg1le hρE1 hρE0 (by norm_num)
    have h3 : (2 + 5 * 2 ^ 23 : ℝ) * u ≤ (2 + 5 * 2 ^ 23) * (1 / 2 ^ 100) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    have h4 : (2 + 5 * 2 ^ 23 : ℝ) * (1 / 2 ^ 100) ≤ 1 / 100 := by norm_num
    linarith
  -- magnitudes
  have hAm : |A| ≤ 2 ^ 23 + 1 := by
    have h1 : |dv * fa| ≤ 2 ^ 23 := by
      rw [abs_mul, abs_of_pos hdpos]
      calc dv * |fa| ≤ 1 * 2 ^ 23 := mul_le_mul (by linarith) hfaM (abs_nonneg _) (by norm_num)
        _ = 2 ^ 23 := one_mul _
    have h2 := abs_sub_abs_le_abs_sub A (dv * fa)
    linarith [hA]
  have hqm : |q| ≤ 3 := by
    have h1 : |g1| ≤ 2 := by rw [abs_of_nonneg hg1nn]; exact hg1le
    have h2 := abs_sub_abs_le_abs_sub q g1
    have h3 : 5 * u ≤ 1 := by linarith
    linarith [hq]
  have hBm : |Bq| ≤ 3 * 2 ^ 23 + 1 := by
    have h1 : |q * ev| ≤ 3 * 2 ^ 23 := by
      rw [abs_mul]
      exact mul_le_mul hqm hevM (abs_nonneg _) (by norm_num)
    have h2 := abs_sub_abs_le_abs_sub Bq (q * ev)
    linarith [hB]
  have hnumm : |num| ≤ 2 ^ 26 := by
    have := abs_sub (A) (Bq)
    have h5 : |A - Bq| ≤ |A| + |Bq| := abs_sub _ _
    rw [hnum]
    have : (2:ℝ) ^ 26 = 2 ^ 23 * 8 := by norm_num
    linarith
  have hnumSm : |numS| ≤ 2 ^ 27 := by
    have h := abs_sub_abs_le_abs_sub numS num
    rw [abs_sub_comm numS num] at h
    have : (2:ℝ) ^ 27 = 2 * 2 ^ 26 := by norm_num
    linarith
  -- the reciprocals
  have hrec : |1 / T2 - 1 / τ| ≤ 640 * u := by
    have : 1 / T2 - 1 / τ = (τ - T2) / (T2 * τ) := by field_simp
    rw [this, abs_div, abs_of_pos (mul_pos hT2pos hτpos), div_le_iff₀ (mul_pos hT2pos hτpos)]
    have h1 : |τ - T2| ≤ 2 * u := by rw [abs_sub_comm]; exact hT2
    have h2 : 1 / 20 * (1 / 16) ≤ T2 * τ := mul_le_mul hT2lo hτ16 (by norm_num) hT2pos.le
    have h3 : 640 * u * (1 / 20 * (1 / 16)) ≤ 640 * u * (T2 * τ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith only [h1, h3]
  -- assemble
  have hdecomp : V - numS / τ = (V - num / T2) + (num - numS) / τ + (num - numS) * (1 / T2 - 1 / τ) +
      numS * (1 / T2 - 1 / τ) := by
    field_simp
    ring
  have hG : (dv * f - sv ^ 2 / dv * e) / τ = numS / τ := by rw [hnumS, hg1]
  rw [hG, hdecomp]
  have t1 : |(num - numS) * (1 / T2 - 1 / τ)| ≤ 4 * (640 * u) := by
    rw [abs_mul]
    exact mul_le_mul e3' hrec (abs_nonneg _) (by norm_num)
  have t2 : |numS * (1 / T2 - 1 / τ)| ≤ 2 ^ 27 * (640 * u) := by
    rw [abs_mul]
    exact mul_le_mul hnumSm hrec (abs_nonneg _) (by positivity)
  have t3 : |(num - numS) / τ| ≤ (ρF + ρE) / bb + 16 * (2 + 5 * 2 ^ 23) * u := by
    rw [abs_div, abs_of_pos hτpos]
    have hbpos : 0 < bb := by linarith
    have k1 : dv * bb ≤ τ :=
      calc dv * bb ≤ dv * dv := mul_le_mul_of_nonneg_left hd hdpos.le
        _ = dv ^ 2 := by ring
        _ ≤ τ := hτlo
    have h1 : dv * ρF / τ ≤ ρF / bb := by
      rw [div_le_div_iff₀ hτpos hbpos]
      calc dv * ρF * bb = ρF * (dv * bb) := by ring
        _ ≤ ρF * τ := mul_le_mul_of_nonneg_left k1 hρF0
    have k2 : g1 * bb ≤ τ :=
      calc g1 * bb ≤ g1 * dv := mul_le_mul_of_nonneg_left hd hg1nn
        _ = sv ^ 2 := by rw [hg1]; field_simp
        _ ≤ τ := hsv
    have h2 : g1 * ρE / τ ≤ ρE / bb := by
      rw [div_le_div_iff₀ hτpos hbpos]
      calc g1 * ρE * bb = ρE * (g1 * bb) := by ring
        _ ≤ ρE * τ := mul_le_mul_of_nonneg_left k2 hρE0
    have h3 : (2 + 5 * 2 ^ 23 : ℝ) * u / τ ≤ 16 * (2 + 5 * 2 ^ 23) * u := by
      rw [div_le_iff₀ hτpos]
      have h16 : 1 ≤ 16 * τ := by linarith
      have hK : (0:ℝ) ≤ (2 + 5 * 2 ^ 23) * u := by positivity
      calc (2 + 5 * 2 ^ 23 : ℝ) * u = (2 + 5 * 2 ^ 23) * u * 1 := by ring
        _ ≤ (2 + 5 * 2 ^ 23) * u * (16 * τ) := mul_le_mul_of_nonneg_left h16 hK
        _ = 16 * (2 + 5 * 2 ^ 23) * u * τ := by ring
    calc |num - numS| / τ ≤ (dv * ρF + g1 * ρE + (2 + 5 * 2 ^ 23) * u) / τ :=
          div_le_div_of_nonneg_right e3 hτpos.le
      _ = dv * ρF / τ + g1 * ρE / τ + (2 + 5 * 2 ^ 23) * u / τ := by ring
      _ ≤ _ := by
          have : (ρF + ρE) / bb = ρF / bb + ρE / bb := by ring
          linarith
  have hsum : u + 4 * (640 * u) + 2 ^ 27 * (640 * u) + 16 * (2 + 5 * 2 ^ 23) * u ≤ 2 ^ 40 * u := by
    have : (u + 4 * (640 * u) + 2 ^ 27 * (640 * u) + 16 * (2 + 5 * 2 ^ 23) * u : ℝ) =
        (1 + 4 * 640 + 2 ^ 27 * 640 + 16 * (2 + 5 * 2 ^ 23)) * u := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by norm_num) hu0.le
  calc _ ≤ |V - num / T2| + |(num - numS) / τ| + |(num - numS) * (1 / T2 - 1 / τ)| +
        |numS * (1 / T2 - 1 / τ)| :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ u + ((ρF + ρE) / bb + 16 * (2 + 5 * 2 ^ 23) * u) + 4 * (640 * u) + 2 ^ 27 * (640 * u) := by
        gcongr
    _ ≤ (ρF + ρE) / bb + 2 ^ 40 * u := by linarith

end SandierSerfaty.Certificate.Query
