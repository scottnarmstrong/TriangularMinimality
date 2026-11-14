/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropE
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# The second derivative of `e - ẽ` at the spline knots (paper §6.2, `tail:e-estimate`, `tail:uniform-error`)

`e''` jumps at the spline knots, so `e''` and `ẽ''` at a knot mean the one-sided derivatives of the
`C¹` functions `e'`, `ẽ'` relative to the closed segment `seg j` (paper §6.2: "at spline knots these inequalities
mean both one-sided derivatives"). On the closed segment `Sg j = [lo j, κ_{j+1}]` the error series `Ee1 j`
(`= e' - ẽ'`) and its termwise derivative `Ee2 j` are continuous (uniform summable bounds), and `Ee1 j` is
differentiable with derivative `Ee2 j` on the interior (`PropE`); hence `Ee2 j t` is the derivative of `Ee1 j`
within the closed segment at every `t` of it (`hasDerivWithinAt_Icc_of_jet`, Mathlib's one-sided extension).
-/

open Set Filter Topology

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- A function that is differentiable on the open interval `(a, c)` with derivative `f₁`, and such that `f` and
`f₁` extend continuously to `[a, c]`, has derivative `f₁ t` within `[a, c]` at every `t ∈ [a, c]`. -/
theorem hasDerivWithinAt_Icc_of_jet {f f₁ : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hd : ∀ x ∈ Ioo a c, HasDerivAt f (f₁ x) x) (hf : ContinuousOn f (Icc a c))
    (hf₁ : ContinuousOn f₁ (Icc a c)) : ∀ t ∈ Icc a c, HasDerivWithinAt f (f₁ t) (Icc a c) t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · have hta : t = a := h.symm
    subst hta
    have hdiff : DifferentiableOn ℝ f (Ioo t c) := fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    have hlim : ContinuousWithinAt f (Ioo t c) t := (hf t ht).mono Ioo_subset_Icc_self
    have hs : Ioo t c ∈ 𝓝[>] t := Ioo_mem_nhdsGT hac
    have hcont : ContinuousWithinAt f₁ (Ioi t) t :=
      (hf₁ t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hac)
    have hlim' : Tendsto (fun x => deriv f x) (𝓝[>] t) (𝓝 (f₁ t)) := by
      refine hcont.tendsto.congr' ?_
      filter_upwards [hs] with x hx using (hd x hx).deriv.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hlim hs hlim').mono Icc_subset_Ici_self
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · subst h'
    have hdiff : DifferentiableOn ℝ f (Ioo a t) := fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    have hlim : ContinuousWithinAt f (Ioo a t) t := (hf t ht).mono Ioo_subset_Icc_self
    have hs : Ioo a t ∈ 𝓝[<] t := Ioo_mem_nhdsLT hac
    have hcont : ContinuousWithinAt f₁ (Iio t) t :=
      (hf₁ t ht).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hac)
    have hlim' : Tendsto (fun x => deriv f x) (𝓝[<] t) (𝓝 (f₁ t)) := by
      refine hcont.tendsto.congr' ?_
      filter_upwards [hs] with x hx using (hd x hx).deriv.symm
    exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hlim hs hlim').mono Icc_subset_Iic_self
  · exact (hd t ⟨h, h'⟩).hasDerivWithinAt

/-! ### The segments as intervals -/

/-- `Sg j` and `Vg j` are the closed and open intervals between the knots (cut at `b/2` for `j = 0`). -/
theorem exists_Sg_eq {j : ℕ} (hj : j ≤ 5) :
    ∃ a c : ℝ, a < c ∧ Sg j = Icc a c ∧ Vg j = Ioo a c := by
  have h1 := b_lt_p_sub_c
  have h2 := p_lt_R₀
  have h3 := R₀_add_thousandth_lt_R₀_add_hs
  have h4 := R₀_add_hs_lt_l
  have h5 := l_lt
  have h6 := b_pos
  have h7 := R₀_pos
  have h8 := hs_pos
  have h9 := c_pos
  have h10 := p_pos
  interval_cases j
  · refine ⟨b / 2, p - c, by linarith, ?_, ?_⟩
    · ext t; simp only [Sg, seg, mem_inter_iff, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨⟨_, h⟩, h', _⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨by linarith, h'⟩, h, by linarith⟩
    · ext t; simp only [Vg, seg, interior_Ioc, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨⟨_, h⟩, h', _⟩; exact ⟨h', h⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨by linarith, h'⟩, h, by linarith⟩
  · refine ⟨p - c, p, by linarith, ?_, ?_⟩
    · ext t; simp only [Sg, seg, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
    · ext t; simp only [Vg, seg, interior_Icc, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
  · refine ⟨p, R₀, h2, ?_, ?_⟩
    · ext t; simp only [Sg, seg, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
    · ext t; simp only [Vg, seg, interior_Icc, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
  · refine ⟨R₀, R₀ + 1 / 1000, by linarith, ?_, ?_⟩
    · ext t; simp only [Sg, seg, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
    · ext t; simp only [Vg, seg, interior_Icc, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
  · refine ⟨R₀ + 1 / 1000, R₀ + hs, h3, ?_, ?_⟩
    · ext t; simp only [Sg, seg, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
    · ext t; simp only [Vg, seg, interior_Icc, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
  · refine ⟨R₀ + hs, l, h4, ?_, ?_⟩
    · ext t; simp only [Sg, seg, mem_inter_iff, mem_Icc]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩
    · ext t; simp only [Vg, seg, interior_Icc, mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h, h'⟩; exact ⟨⟨h, h'⟩, by linarith, by linarith⟩

/-! ### Continuity of the error series on the closed segment -/

theorem continuousOn_qP (i j : ℕ) :
    ContinuousOn (qP0 i j) (Ioi 0) ∧ ContinuousOn (qP1 i j) (Ioi 0) ∧ ContinuousOn (qP2 i j) (Ioi 0) := by
  have h3 := contDiffOn_PD i j 3
  have h2 : ContDiffOn ℝ 2 (deriv (Piece.D i j)) (Ioi 0) := h3.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ContDiffOn ℝ 1 (deriv (deriv (Piece.D i j))) (Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h0 : ContDiffOn ℝ 0 (deriv (deriv (deriv (Piece.D i j)))) (Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have c0 := h3.continuousOn
  have c1 := h2.continuousOn
  have c2 := h1.continuousOn
  have c3 := h0.continuousOn
  have cid : ContinuousOn (fun t : ℝ => t) (Ioi 0) := continuousOn_id
  unfold qP0 qP1 qP2
  simp only [iteratedDeriv_one, iter2_eq, iter3_eq]
  exact ⟨(cid.mul c1).sub (continuousOn_const.mul c0), (cid.mul c2).add (continuousOn_const.mul c1),
    (cid.mul c3).add (continuousOn_const.mul c2)⟩

theorem continuousOn_rP (j : ℕ) (ij : ℕ × ℕ) :
    ContinuousOn (rP1 j ij) (Ioi 0) ∧ ContinuousOn (rP2 j ij) (Ioi 0) := by
  obtain ⟨a0, a1, a2⟩ := continuousOn_qP ij.1 j
  obtain ⟨b0, b1, b2⟩ := continuousOn_qP ij.2 j
  by_cases h : ij.1 < 39 ∧ ij.2 < 39
  · have e1 : rP1 j ij = fun _ => 0 := by funext t; simp [rP1, h]
    have e2 : rP2 j ij = fun _ => 0 := by funext t; simp [rP2, h]
    rw [e1, e2]
    exact ⟨continuousOn_const, continuousOn_const⟩
  · have e1 : rP1 j ij = tP1 j ij := by funext t; simp [rP1, h]
    have e2 : rP2 j ij = tP2 j ij := by funext t; simp [rP2, h]
    rw [e1, e2]
    unfold tP1 tP2 mul₁ mul₂
    exact ⟨continuousOn_const.mul ((a1.mul b0).add (a0.mul b1)),
      continuousOn_const.mul (((a2.mul b0).add (a1.mul b1)).add ((a1.mul b1).add (a0.mul b2)))⟩

theorem continuousOn_Ee {j : ℕ} (hj : j ≤ 5) :
    ContinuousOn (Ee1 j) (Sg j) ∧ ContinuousOn (Ee2 j) (Sg j) := by
  have hI := Sg_subset_Ioc j
  have hI' : Sg j ⊆ Ioi 0 := fun t ht => (hI ht).1
  have hb : ∀ ij t, t ∈ Sg j → jn (rP0 j ij) (rP1 j ij) (rP2 j ij) t ≤ rest (mq3 j) ij := fun ij t ht =>
    ((je_rP j ij).bd t (hI ht)).trans (rest_mono (qb_nonneg j t) (qb_le_mq3 hj ht) ij)
  have hu := summable_rest (mq3_nonneg j) (summable_mq3 j)
  refine ⟨continuousOn_const.mul (continuousOn_tsum (u := rest (mq3 j)) (fun ij => (continuousOn_rP j ij).1.mono hI')
      hu fun ij t ht => ?_), continuousOn_const.mul (continuousOn_tsum (u := fun ij => 2 * rest (mq3 j) ij)
      (fun ij => (continuousOn_rP j ij).2.mono hI') (hu.mul_left 2) fun ij t ht => ?_)⟩
  · rw [Real.norm_eq_abs]
    have := hb ij t ht; unfold jn at this
    linarith [abs_nonneg (rP0 j ij t), abs_nonneg (rP2 j ij t)]
  · rw [Real.norm_eq_abs]
    have := hb ij t ht; unfold jn at this
    linarith [abs_nonneg (rP0 j ij t), abs_nonneg (rP1 j ij t)]

/-- **The one-sided derivative of the error at the knots**: `Ee2 j t` is the derivative of `Ee1 j = e' - ẽ'`
within the closed segment `Sg j` at every one of its points. -/
theorem hasDerivWithinAt_Ee1 {j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ Sg j) :
    HasDerivWithinAt (Ee1 j) (Ee2 j t) (Sg j) t := by
  obtain ⟨a, c, hac, hS, hV⟩ := exists_Sg_eq hj
  obtain ⟨c1, c2⟩ := continuousOn_Ee hj
  rw [hS] at c1 c2 ⊢
  rw [hS] at ht
  refine hasDerivWithinAt_Icc_of_jet hac (fun x hx => ?_) c1 c2 t ht
  have hxV : x ∈ Vg j := by rw [hV]; exact hx
  exact ((je_rP_tsum j hj).jet.d1 x hxV).const_mul (1 / 2)

end Tails

end SandierSerfaty

end
