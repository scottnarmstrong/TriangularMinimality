/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropF
public import SandierSerfaty.Tails.PropEKnot
public import SandierSerfaty.Tails.ConstRegion

/-!
# `tail:uniform-error`

**Conditional on the finite-core premise** `FiniteCore` (`tail:finite-core-premise`: the estimates of Section 6 are
conditional; the premise is supplied by the finite interval verification of Section 7), for every
`t ∈ [b, l]` the six truncation errors `f₀ - f̃₀`, `e - ẽ`, `f₀' - f̃₀'`, `e' - ẽ'`, `f₀'' - f̃₀''`, `e'' - ẽ''` are
below `10⁻¹¹` in absolute value (`uniform_error_of_finiteCore`); in fact the two second-derivative errors are
below `2.4·10⁻¹³` and `1.3·10⁻¹³` (the second is `e_second_error_lt`).

The derivative `e''` jumps at the spline knots (the splines are `C²` but only piecewise `C³`), so `e''` means the
derivative of `e'` relative to the closed segment `seg j ∋ t` (`derivWithin`, which is the classical `e''` in the
interior of the segment), as in paper §6.2. The statement for `e''` is therefore per segment.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The truncation tolerance `10⁻¹¹` of `tail:uniform-error`. -/
@[expose] noncomputable def epsTail : ℝ := 1 / 10 ^ 11

theorem f_error_numeric : 60000000 * aa < 12 / 10 ^ 14 := by
  have := aa_lt
  nlinarith

theorem e_error_numeric : 16 * (2 * 10 ^ 6) * aa + 32 * aa ^ 2 < 65 / 10 ^ 15 := by
  have h1 := aa_lt
  have h2 := aa_nonneg
  nlinarith [mul_nonneg h2 h2, mul_nonneg h2 (sub_nonneg.2 h1.le)]

/-- `tail:uniform-error` for `f₀`: the three errors `f₀ - f̃₀`, `f₀' - f̃₀'`, `f₀'' - f̃₀''` on `[b, l]`;
the second one below `2.4·10⁻¹³` (paper §6.5). -/
theorem f_errors_lt (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc b l) :
    |f₀ t - Trunc.f₀ t| < 12 / 10 ^ 14 ∧ |deriv f₀ t - deriv Trunc.f₀ t| < 12 / 10 ^ 14 ∧
      |deriv (deriv f₀) t - deriv (deriv Trunc.f₀) t| < 24 / 10 ^ 14 := by
  have h := f_error hc ht
  have hn := f_error_numeric
  have a0 := abs_nonneg (f₀ t - Trunc.f₀ t)
  have a1 := abs_nonneg (deriv f₀ t - deriv Trunc.f₀ t)
  have a2 := abs_nonneg (deriv (deriv f₀) t - deriv (deriv Trunc.f₀) t)
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The error `e - ẽ` and `e' - ẽ'` on `[b, l]`, and the explicit piece formula of `e'' - ẽ''` on `seg j`. -/
theorem e_errors_lt (hc : FiniteCore) {j : ℕ} (hj : j ≤ 5) {t : ℝ} (hts : t ∈ seg j) (ht : t ∈ Icc b l) :
    |e t - Trunc.e t| < 65 / 10 ^ 15 ∧ |deriv e t - deriv Trunc.e t| < 65 / 10 ^ 15 ∧
      |Ee2 j t| < 13 / 10 ^ 14 := by
  have h := e_error_bound hc hj hts ht.1 ht.2
  have hn := e_error_numeric
  have htd : t ∈ dom := Icc_subset_dom ht
  rw [e_sub_eq hj hts htd, deriv_e_sub_eq hj hts htd]
  have a0 := abs_nonneg (Ee0 j t)
  have a1 := abs_nonneg (Ee1 j t)
  have a2 := abs_nonneg (Ee2 j t)
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **The second derivative of `e - ẽ`**: relative to the closed segment `seg j ∋ t` (paper §6.2),
`e'' - ẽ'' = Ee2 j` at every `t ∈ seg j ∩ [b, l]`, including the spline knots. -/
theorem e_second_error_eq {j : ℕ} (hj : j ≤ 5) {t : ℝ} (hts : t ∈ seg j) (ht : t ∈ Icc b l) :
    derivWithin (deriv e) (seg j) t - derivWithin (deriv Trunc.e) (seg j) t = Ee2 j t := by
  have htd : t ∈ dom := Icc_subset_dom ht
  have ht0 : 0 < t := dom_subset_Ioi htd
  have htS : t ∈ Sg j := ⟨hts, by have := b_pos; linarith [htd.1], htd.2.le⟩
  have hnb : Sg j ∈ nhdsWithin t (seg j) :=
    mem_nhdsWithin.2 ⟨Ioo (b / 2) 1, isOpen_Ioo, htd, fun y hy => ⟨hy.2, hy.1.1.le, hy.1.2.le⟩⟩
  have hU : UniqueDiffWithinAt ℝ (seg j) t := uniqueDiffOn_seg (by omega : j ≤ 6) t hts
  -- `ẽ'` on `seg j`
  have hT : HasDerivWithinAt (deriv Trunc.e) (TT2 j t) (seg j) t := by
    refine ((hasDerivAt_TT1 j ht0).hasDerivWithinAt (s := seg j)).congr (fun y hy => ?_) ?_
    · rw [(hasDerivAt_Trunc_e (seg_subset_Ioi hy)).deriv, sTe1_eq hj hy]
    · rw [(hasDerivAt_Trunc_e ht0).deriv, sTe1_eq hj hts]
  -- `e'` on `Sg j`
  have hE : HasDerivWithinAt (deriv e) (TT2 j t + Ee2 j t) (Sg j) t := by
    have h1 := ((hasDerivAt_TT1 j ht0).hasDerivWithinAt (s := Sg j)).add (hasDerivWithinAt_Ee1 hj htS)
    refine h1.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (isOpen_dom.mem_nhds htd),
        self_mem_nhdsWithin] with y hy hyS
      rw [(hasDerivAt_e hy).deriv, sTe1_eq hj hyS.1]
      unfold Ee1
      congr 2
      exact tsum_congr fun ij => (sR_eq_rP hj ij hyS.1).2
    · rw [(hasDerivAt_e htd).deriv, sTe1_eq hj hts]
      unfold Ee1
      congr 2
      exact tsum_congr fun ij => (sR_eq_rP hj ij hts).2
  have hE' : HasDerivWithinAt (deriv e) (TT2 j t + Ee2 j t) (seg j) t := hE.mono_of_mem_nhdsWithin hnb
  rw [hE'.derivWithin hU, hT.derivWithin hU]
  ring

/-- **`tail:uniform-error`, `e''`** (paper §6.5): at every `t ∈ seg j ∩ [b, l]` (the second derivative
relative to the closed segment), `|e'' - ẽ''| < 1.3·10⁻¹³`. -/
theorem e_second_error_lt (hc : FiniteCore) {j : ℕ} (hj : j ≤ 5) {t : ℝ} (hts : t ∈ seg j)
    (ht : t ∈ Icc b l) :
    |derivWithin (deriv e) (seg j) t - derivWithin (deriv Trunc.e) (seg j) t| < 13 / 10 ^ 14 := by
  rw [e_second_error_eq hj hts ht]
  exact (e_errors_lt hc hj hts ht).2.2

/-- **`tail:uniform-error`**, conditional on the finite-core premise `FiniteCore`
(paper `tail:finite-core-premise`). For every `t ∈ [b, l]`:
`|f₀ - f̃₀|`, `|e - ẽ|`, `|f₀' - f̃₀'|`, `|e' - ẽ'|`, `|f₀'' - f̃₀''|`, and `|e'' - ẽ''| < 10⁻¹¹`, where `e''`
is the second derivative relative to the closed segment `seg j ∋ t` (`derivWithin`; at the spline knots, where
`e''` jumps, both one-sided values). -/
theorem uniform_error_of_finiteCore (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc b l) :
    |f₀ t - Trunc.f₀ t| < epsTail ∧ |e t - Trunc.e t| < epsTail ∧
      |deriv f₀ t - deriv Trunc.f₀ t| < epsTail ∧ |deriv e t - deriv Trunc.e t| < epsTail ∧
      |deriv (deriv f₀) t - deriv (deriv Trunc.f₀) t| < epsTail ∧
      ∀ j, j ≤ 5 → t ∈ seg j →
        |derivWithin (deriv e) (seg j) t - derivWithin (deriv Trunc.e) (seg j) t| < epsTail := by
  obtain ⟨j₀, hj₀, hts₀⟩ := exists_seg_of_Icc ht
  obtain ⟨f0, f1, f2⟩ := f_errors_lt hc ht
  obtain ⟨e0, e1, -⟩ := e_errors_lt hc hj₀ hts₀ ht
  unfold epsTail
  refine ⟨by linarith [(by norm_num : (12 : ℝ) / 10 ^ 14 < 1 / 10 ^ 11)], ?_, ?_, ?_, ?_, fun j hj hts => ?_⟩
  · linarith [(by norm_num : (65 : ℝ) / 10 ^ 15 < 1 / 10 ^ 11)]
  · linarith [(by norm_num : (12 : ℝ) / 10 ^ 14 < 1 / 10 ^ 11)]
  · linarith [(by norm_num : (65 : ℝ) / 10 ^ 15 < 1 / 10 ^ 11)]
  · linarith [(by norm_num : (24 : ℝ) / 10 ^ 14 < 1 / 10 ^ 11)]
  · exact (e_second_error_lt hc hj hts ht).trans (by norm_num)

end Tails

end SandierSerfaty

end
