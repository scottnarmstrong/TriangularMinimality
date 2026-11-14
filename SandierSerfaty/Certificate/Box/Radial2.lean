/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Uniform
public import SandierSerfaty.Calibration.Exterior
public import SandierSerfaty.Calibration.Stationarity

/-!
# One-sided second derivatives of the exact radial functions

The calibration functions `f₀` (class `C²`) and `e` (class `C¹`; `e''` jumps at the spline knots) are the exact
objects of the finite assertions of paper §7. The second-order quantities `G_dd`, `G_ss` of
`comp:G-derivatives` need, at every `t ≥ b`:

* `hasDerivAt_deriv_f₀`: `(f₀')' = f₀''` exists (two-sided);
* `exists_e_right_deriv`: for `t ∈ [b, l)` and a right derivative `E` of the truncated `ẽ'` at `t`, the exact `e'`
  has a right derivative `E'` with `|E' - E| < 10⁻¹¹` (`Tails.uniform_error_of_finiteCore`, the right segment of `t`);
* the exterior: for `t ≥ l`, `e' = 0` on `[l, ∞)` (right derivative `0`) and `f₀'' = -2π B(l)`.
-/

open Set Filter Topology

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Calibration SandierSerfaty.Tails

theorem hasDerivAt_deriv_f₀ {t : ℝ} (ht : 0 < t) : HasDerivAt (deriv f₀) (deriv (deriv f₀) t) t := by
  have h1 : ContDiffOn ℝ 1 (deriv f₀) (Ioi 0) := contDiffOn_f₀.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((h1.differentiableOn (by norm_num) t ht).differentiableAt (Ioi_mem_nhds ht)).hasDerivAt

/-- **The one-sided second derivatives of `ẽ'` and `e'` on a segment** (`e_second_error_eq`, as `HasDerivWithinAt`). -/
theorem hasDerivWithinAt_e'_seg {j : ℕ} (hj : j ≤ 5) {t : ℝ} (hts : t ∈ seg j) (ht : t ∈ Icc b l) :
    HasDerivWithinAt (deriv Trunc.e) (TT2 j t) (seg j) t ∧
      HasDerivWithinAt (deriv e) (TT2 j t + Ee2 j t) (seg j) t := by
  have htd : t ∈ dom := Icc_subset_dom ht
  have ht0 : 0 < t := dom_subset_Ioi htd
  have htS : t ∈ Sg j := ⟨hts, by have := b_pos; linarith [htd.1], htd.2.le⟩
  have hnb : Sg j ∈ nhdsWithin t (seg j) :=
    mem_nhdsWithin.2 ⟨Ioo (b / 2) 1, isOpen_Ioo, htd, fun y hy => ⟨hy.2, hy.1.1.le, hy.1.2.le⟩⟩
  have hT : HasDerivWithinAt (deriv Trunc.e) (TT2 j t) (seg j) t := by
    refine ((hasDerivAt_TT1 j ht0).hasDerivWithinAt (s := seg j)).congr (fun y hy => ?_) ?_
    · rw [(hasDerivAt_Trunc_e (seg_subset_Ioi hy)).deriv, sTe1_eq hj hy]
    · rw [(hasDerivAt_Trunc_e ht0).deriv, sTe1_eq hj hts]
  refine ⟨hT, ?_⟩
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
  exact hE.mono_of_mem_nhdsWithin hnb

/-- Every `t ∈ [b, l)` has a segment `seg j` (`j ≤ 5`) containing a right neighbourhood `[t, r]`. -/
theorem exists_right_seg {t : ℝ} (ht : t ∈ Ico b l) : ∃ j, j ≤ 5 ∧ t ∈ seg j ∧ ∃ r, t < r ∧ Icc t r ⊆ seg j := by
  have h1 := b_lt_p_sub_c
  have h2 := c_pos
  have h3 := p_lt_R₀
  have h4 := hs_pos
  have h5 := R₀_add_hs_lt_l
  have h6 := R₀_add_thousandth_lt_R₀_add_hs
  have hb := b_pos
  by_cases a1 : t < p - c
  · refine ⟨0, by norm_num, ⟨by linarith [ht.1], a1.le⟩, p - c, a1, fun y hy => ⟨by linarith [ht.1, hy.1], hy.2⟩⟩
  by_cases a2 : t < p
  · refine ⟨1, by norm_num, ⟨not_lt.1 a1, a2.le⟩, p, a2, fun y hy => ⟨by linarith [hy.1], hy.2⟩⟩
  by_cases a3 : t < R₀
  · refine ⟨2, by norm_num, ⟨not_lt.1 a2, a3.le⟩, R₀, a3, fun y hy => ⟨by linarith [hy.1], hy.2⟩⟩
  by_cases a4 : t < R₀ + 1 / 1000
  · refine ⟨3, by norm_num, ⟨not_lt.1 a3, a4.le⟩, R₀ + 1 / 1000, a4, fun y hy => ⟨by linarith [hy.1], hy.2⟩⟩
  by_cases a5 : t < R₀ + hs
  · refine ⟨4, by norm_num, ⟨not_lt.1 a4, a5.le⟩, R₀ + hs, a5, fun y hy => ⟨by linarith [hy.1], hy.2⟩⟩
  · exact ⟨5, by norm_num, ⟨not_lt.1 a5, ht.2.le⟩, l, ht.2, fun y hy => ⟨by linarith [hy.1], hy.2⟩⟩

/-- **The right second derivative of the exact `e'`** from that of the truncated `ẽ'`:
`|e'' - ẽ''| < 10⁻¹¹` on `[b, l)`. -/
theorem exists_e_right_deriv (hc : FiniteCore) {t : ℝ} (ht : t ∈ Ico b l) {E : ℝ}
    (hE : HasDerivWithinAt (deriv Trunc.e) E (Ici t) t) :
    ∃ E', HasDerivWithinAt (deriv e) E' (Ici t) t ∧ |E' - E| < epsTail := by
  obtain ⟨j, hj, hts, r, htr, hr⟩ := exists_right_seg ht
  have htIcc : t ∈ Icc b l := ⟨ht.1, ht.2.le⟩
  obtain ⟨hT, hEx⟩ := hasDerivWithinAt_e'_seg hj hts htIcc
  have hnb : seg j ∈ 𝓝[Ici t] t := mem_of_superset (Icc_mem_nhdsGE htr) hr
  have hT' := hT.mono_of_mem_nhdsWithin hnb
  have hEq : E = TT2 j t := (uniqueDiffWithinAt_Ici t).eq_deriv _ hE hT'
  refine ⟨TT2 j t + Ee2 j t, hEx.mono_of_mem_nhdsWithin hnb, ?_⟩
  rw [hEq]
  have := (e_errors_lt hc hj hts htIcc).2.2
  have h2 : (13 : ℝ) / 10 ^ 14 ≤ epsTail := by unfold epsTail; norm_num
  rw [add_sub_cancel_left]
  exact lt_of_lt_of_le this h2

/-! ### The exterior `t ≥ l` -/

theorem deriv_e_of_ge {t : ℝ} (ht : l ≤ t) : deriv e t = 0 := by
  have hl := l_pos'
  have ht0 : 0 < t := lt_of_lt_of_le hl ht
  have h1 : HasDerivAt e (deriv e t) t := (differentiableAt_e ht0).hasDerivAt
  have h2 : HasDerivWithinAt e (deriv e t) (Ici l) t := h1.hasDerivWithinAt
  have h3 : HasDerivWithinAt e 0 (Ici l) t := (hasDerivWithinAt_const t (Ici l) (0 : ℝ)).congr
    (fun x hx => e_of_ge hx) (e_of_ge ht)
  exact (uniqueDiffOn_Ici l t ht).eq_deriv _ h2 h3

theorem e_right_deriv_ext {t : ℝ} (ht : l ≤ t) : HasDerivWithinAt (deriv e) 0 (Ici t) t := by
  refine (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr (fun x hx => deriv_e_of_ge (ht.trans hx))
    (deriv_e_of_ge ht)

theorem deriv_f₀_of_ge {t : ℝ} (ht : l ≤ t) : deriv f₀ t = -(Real.pi * B l * (2 * t)) := by
  have hl := l_pos'
  set g : ℝ → ℝ := fun t => f₀ l - Real.pi * B l * (t ^ 2 - l ^ 2) with hg
  have hgc : ContDiffOn ℝ 2 g (Ioi 0) := by
    have : ContDiff ℝ 2 g := by rw [hg]; fun_prop
    exact this.contDiffOn
  have key := deriv_deriv_eq_of_eqOn (f := f₀) (g := g) (s := Ici l) (U := Ioi 0) (uniqueDiffOn_Ici l) isOpen_Ioi
    (fun x hx => lt_of_lt_of_le hl hx) (fun x hx => f₀_of_ge hx) contDiffOn_f₀ hgc
  have hg1 : deriv g t = -(Real.pi * B l * (2 * t)) := by
    have : HasDerivAt g (-(Real.pi * B l * (2 * t))) t := by
      have := ((((hasDerivAt_pow 2 t).sub_const (l ^ 2)).const_mul (Real.pi * B l)).const_sub (f₀ l))
      simpa using this
    exact this.deriv
  rw [key.1 ht, hg1]

theorem f₀_second_ext {t : ℝ} (ht : l ≤ t) : HasDerivAt (deriv f₀) (-(2 * Real.pi * B l)) t := by
  have hl := l_pos'
  have ht0 : 0 < t := lt_of_lt_of_le hl ht
  have h1 := hasDerivAt_deriv_f₀ ht0
  have h2 : HasDerivWithinAt (deriv f₀) (-(2 * Real.pi * B l)) (Ici l) t := by
    have : HasDerivAt (fun t : ℝ => -(Real.pi * B l * (2 * t))) (-(2 * Real.pi * B l)) t := by
      have := (((hasDerivAt_id t).const_mul 2).const_mul (Real.pi * B l)).fun_neg
      refine this.congr_deriv ?_
      simp; ring
    exact this.hasDerivWithinAt.congr (fun x hx => deriv_f₀_of_ge hx) (deriv_f₀_of_ge ht)
  have h3 := (uniqueDiffOn_Ici l t ht).eq_deriv _ h1.hasDerivWithinAt h2
  rw [h3] at h1
  exact h1

end SandierSerfaty.Certificate.Box
