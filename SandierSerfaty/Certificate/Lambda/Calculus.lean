/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Taylor bounds from one-sided second derivatives, and the midpoint rule with a Lipschitz derivative

The radial function `e` is only `C¹` at the knots, with one-sided second derivatives on the segments
(`Box.Radial2`); the table encloses these right derivatives (`Box.Encl2.e2`). The fine `λ` quadrature therefore
uses the second-order expansions and the midpoint rule in a form that only needs *right* derivatives of the first
derivative:

* `abs_sub_le_of_right_deriv`: a continuous function whose right derivatives are bounded by `r` on `[lo, hi)` is
  `r`-Lipschitz on `[lo, hi]` (Mathlib's `norm_image_sub_le_of_norm_deriv_right_le_segment`);
* `exists_first_order`, `exists_second_order`: if the right derivatives of `F₁ = F'` lie in `[m, M]` on
  `[lo, hi)`, then for `y, t ∈ [lo, hi]`
  `F₁ t = F₁ y + θ (t - y)` and `F t = F y + F₁ y (t - y) + θ' (t - y)²/2` with `θ, θ' ∈ [m, M]`;
* `abs_integral_sub_midpoint_le_of_lip`: the midpoint rule `|∫_a^b f - (b - a) f((a+b)/2)| ≤ (b - a)³ M/24` for
  `f` with a derivative `f₁` that is `M`-Lipschitz on `[a, b]` (the proof of `Table.abs_sub_midpoint_le`, with
  the mean value step replaced by the Lipschitz bound).
-/

open Set Filter

public section

namespace SandierSerfaty.Certificate.Lambda

/-- **Lipschitz from bounded right derivatives.** -/
theorem abs_sub_le_of_right_deriv {g g' : ℝ → ℝ} {lo hi r : ℝ} (hc : ContinuousOn g (Icc lo hi))
    (hd : ∀ x ∈ Ico lo hi, HasDerivWithinAt g (g' x) (Ici x) x) (hb : ∀ x ∈ Ico lo hi, |g' x| ≤ r)
    {x z : ℝ} (hx : x ∈ Icc lo hi) (hz : z ∈ Icc lo hi) : |g x - g z| ≤ r * |x - z| := by
  have key : ∀ {u v : ℝ}, u ∈ Icc lo hi → v ∈ Icc lo hi → u ≤ v → |g v - g u| ≤ r * (v - u) := by
    intro u v hu hv huv
    have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := g) (f' := g') (C := r) (a := u) (b := hi)
      (hc.mono (Icc_subset_Icc hu.1 le_rfl)) (fun y hy => hd y ⟨hu.1.trans hy.1, hy.2⟩)
      (fun y hy => by simpa using hb y ⟨hu.1.trans hy.1, hy.2⟩) v ⟨huv, hv.2⟩
    simpa [Real.norm_eq_abs] using this
  rcases le_total z x with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact key hz hx h
  · rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.2 h), neg_sub]; exact key hx hz h

/-- Right derivatives in `[m, M]` give `|g x - g z - c (x - z)| ≤ r |x - z|`, `c = (m + M)/2`, `r = (M - m)/2`. -/
theorem abs_sub_sub_le_of_right_deriv {F₁ : ℝ → ℝ} {lo hi m M : ℝ} (hc : ContinuousOn F₁ (Icc lo hi))
    (hd : ∀ x ∈ Ico lo hi, ∃ E, HasDerivWithinAt F₁ E (Ici x) x ∧ m ≤ E ∧ E ≤ M) {x z : ℝ}
    (hx : x ∈ Icc lo hi) (hz : z ∈ Icc lo hi) :
    |F₁ x - F₁ z - (m + M) / 2 * (x - z)| ≤ (M - m) / 2 * |x - z| := by
  choose! E hE using hd
  have hg : ContinuousOn (fun u => F₁ u - (m + M) / 2 * u) (Icc lo hi) :=
    hc.sub (continuousOn_const.mul continuousOn_id)
  have hgd : ∀ u ∈ Ico lo hi, HasDerivWithinAt (fun u => F₁ u - (m + M) / 2 * u) (E u - (m + M) / 2) (Ici u) u :=
    fun u hu => by
      have := (hE u hu).1.fun_sub ((hasDerivAt_id' u).const_mul ((m + M) / 2)).hasDerivWithinAt
      simpa using this
  have hgb : ∀ u ∈ Ico lo hi, |E u - (m + M) / 2| ≤ (M - m) / 2 := fun u hu => by
    obtain ⟨-, h1, h2⟩ := hE u hu
    rw [abs_le]; constructor <;> linarith
  have := abs_sub_le_of_right_deriv hg hgd hgb hx hz
  convert this using 2; ring

theorem exists_mem_of_abs_le {v w m M : ℝ} (h : |v - (m + M) / 2 * w| ≤ (M - m) / 2 * w) (hw : 0 < w) :
    m ≤ v / w ∧ v / w ≤ M := by
  rw [abs_le] at h
  constructor
  · rw [le_div_iff₀ hw]; nlinarith [h.1]
  · rw [div_le_iff₀ hw]; nlinarith [h.2]

/-- **First-order expansion with a derivative range.** -/
theorem exists_first_order {F₁ : ℝ → ℝ} {lo hi m M y t : ℝ} (hc : ContinuousOn F₁ (Icc lo hi))
    (hd : ∀ x ∈ Ico lo hi, ∃ E, HasDerivWithinAt F₁ E (Ici x) x ∧ m ≤ E ∧ E ≤ M) (hmM : m ≤ M)
    (hy : y ∈ Icc lo hi) (ht : t ∈ Icc lo hi) :
    ∃ θ, m ≤ θ ∧ θ ≤ M ∧ F₁ t = F₁ y + θ * (t - y) := by
  by_cases hty : t = y
  · exact ⟨m, le_rfl, hmM, by rw [hty]; ring⟩
  have hw : 0 < |t - y| := abs_pos.2 (sub_ne_zero.2 hty)
  have h := abs_sub_sub_le_of_right_deriv hc hd ht hy
  refine ⟨(F₁ t - F₁ y) / (t - y), ?_, ?_, by field_simp [sub_ne_zero.2 hty]; ring⟩
  · rcases lt_or_gt_of_ne (sub_ne_zero.2 hty) with hn | hp
    · have h' : |-(F₁ t - F₁ y) - (m + M) / 2 * (-(t - y))| ≤ (M - m) / 2 * (-(t - y)) := by
        rw [abs_of_neg hn] at h; rw [show -(F₁ t - F₁ y) - (m + M) / 2 * (-(t - y)) =
          -(F₁ t - F₁ y - (m + M) / 2 * (t - y)) by ring, abs_neg]; exact h
      have := (exists_mem_of_abs_le h' (by linarith)).1
      rwa [neg_div_neg_eq] at this
    · rw [abs_of_pos hp] at h; exact (exists_mem_of_abs_le h hp).1
  · rcases lt_or_gt_of_ne (sub_ne_zero.2 hty) with hn | hp
    · have h' : |-(F₁ t - F₁ y) - (m + M) / 2 * (-(t - y))| ≤ (M - m) / 2 * (-(t - y)) := by
        rw [abs_of_neg hn] at h; rw [show -(F₁ t - F₁ y) - (m + M) / 2 * (-(t - y)) =
          -(F₁ t - F₁ y - (m + M) / 2 * (t - y)) by ring, abs_neg]; exact h
      have := (exists_mem_of_abs_le h' (by linarith)).2
      rwa [neg_div_neg_eq] at this
    · rw [abs_of_pos hp] at h; exact (exists_mem_of_abs_le h hp).2

/-- The one-sided step of the second-order bound: `G y = 0`, `G' = g` on `[y, t]` with `|g x| ≤ r (x - y)`. -/
theorem abs_le_of_deriv_le_right {G g : ℝ → ℝ} {y t r : ℝ} (hyt : y ≤ t)
    (hG : ∀ x ∈ Icc y t, HasDerivAt G (g x) x) (hG0 : G y = 0) (hg : ∀ x ∈ Icc y t, |g x| ≤ r * (x - y)) :
    |G t| ≤ r * (t - y) ^ 2 / 2 := by
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := y) (b := t) (f := G) (f' := g)
    (B := fun x => r * (x - y) ^ 2 / 2) (B' := fun x => r * (x - y))
    (fun x hx => (hG x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hG x (Ico_subset_Icc_self hx)).hasDerivWithinAt) (by simp [hG0])
    (fun x => by
      have := (((hasDerivAt_id' x).sub_const y).pow 2).const_mul r |>.div_const 2
      convert this using 1; push_cast; ring)
    (fun x hx => by simpa using hg x (Ico_subset_Icc_self hx)) ⟨hyt, le_rfl⟩
  simpa using this

/-- **Second-order expansion with a range of right derivatives of `F₁ = F'`.** -/
theorem exists_second_order {F F₁ : ℝ → ℝ} {lo hi m M y t : ℝ} (hF : ∀ x ∈ Icc lo hi, HasDerivAt F (F₁ x) x)
    (hc : ContinuousOn F₁ (Icc lo hi))
    (hd : ∀ x ∈ Ico lo hi, ∃ E, HasDerivWithinAt F₁ E (Ici x) x ∧ m ≤ E ∧ E ≤ M) (hmM : m ≤ M)
    (hy : y ∈ Icc lo hi) (ht : t ∈ Icc lo hi) :
    ∃ θ, m ≤ θ ∧ θ ≤ M ∧ F t = F y + F₁ y * (t - y) + θ * (t - y) ^ 2 / 2 := by
  set c := (m + M) / 2 with hcdef
  set r := (M - m) / 2 with hrdef
  set G : ℝ → ℝ := fun x => F x - F y - F₁ y * (x - y) - c * (x - y) ^ 2 / 2 with hGdef
  set g : ℝ → ℝ := fun x => F₁ x - F₁ y - c * (x - y) with hgdef
  have hGd : ∀ x ∈ Icc lo hi, HasDerivAt G (g x) x := fun x hx => by
    have h1 := (((hF x hx).sub_const (F y)).fun_sub (((hasDerivAt_id' x).sub_const y).const_mul (F₁ y))).fun_sub
      ((((hasDerivAt_id' x).sub_const y).pow 2).const_mul c |>.div_const 2)
    convert h1 using 1; push_cast; simp only [hgdef]; ring
  have hgb : ∀ x ∈ Icc lo hi, |g x| ≤ r * |x - y| := fun x hx => abs_sub_sub_le_of_right_deriv hc hd hx hy
  have hG0 : G y = 0 := by simp [hGdef]
  have hGt : |G t| ≤ r * (t - y) ^ 2 / 2 := by
    rcases le_total y t with hyt | hty
    · have hsub : Icc y t ⊆ Icc lo hi := Icc_subset_Icc hy.1 ht.2
      refine abs_le_of_deriv_le_right hyt (fun x hx => hGd x (hsub hx)) hG0 fun x hx => ?_
      have := hgb x (hsub hx); rwa [abs_of_nonneg (sub_nonneg.2 hx.1)] at this
    · have hsub : Icc t y ⊆ Icc lo hi := Icc_subset_Icc ht.1 hy.2
      have h := abs_le_of_deriv_le_right (G := fun u => G (y - u)) (g := fun u => -g (y - u)) (y := 0)
        (t := y - t) (r := r) (by linarith) (fun u hu => by
          have hm : y - u ∈ Icc lo hi := hsub ⟨by linarith [hu.2], by linarith [hu.1]⟩
          have := (hGd (y - u) hm).comp u ((hasDerivAt_id u).const_sub y)
          simpa [Function.comp_def] using this) (by simp [hG0]) (fun u hu => by
          have hm : y - u ∈ Icc lo hi := hsub ⟨by linarith [hu.2], by linarith [hu.1]⟩
          have := hgb (y - u) hm
          rw [abs_neg, sub_zero]
          rwa [show y - u - y = -u by ring, abs_neg, abs_of_nonneg hu.1] at this)
      simp only [sub_sub_cancel, sub_zero] at h
      rwa [show (y - t) ^ 2 = (t - y) ^ 2 by ring] at h
  by_cases hty : t = y
  · exact ⟨m, le_rfl, hmM, by rw [hty]; ring⟩
  have hw : 0 < (t - y) ^ 2 / 2 := by have := sub_ne_zero.2 hty; positivity
  have hG' : |(F t - F y - F₁ y * (t - y)) - (m + M) / 2 * ((t - y) ^ 2 / 2)| ≤ (M - m) / 2 * ((t - y) ^ 2 / 2) := by
    have e : G t = (F t - F y - F₁ y * (t - y)) - (m + M) / 2 * ((t - y) ^ 2 / 2) := by
      simp only [hGdef, hcdef]; ring
    rw [← e]; simpa [hrdef, mul_div_assoc] using hGt
  obtain ⟨h1, h2⟩ := exists_mem_of_abs_le hG' hw
  refine ⟨(F t - F y - F₁ y * (t - y)) / ((t - y) ^ 2 / 2), h1, h2, ?_⟩
  field_simp
  ring

/-! ### The midpoint rule with a Lipschitz derivative -/

/-- **The midpoint rule**, antiderivative form, for `f` with an `M`-Lipschitz derivative `f₁` on `[a, b]`. -/
theorem abs_sub_midpoint_le_of_lip {F f f₁ : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (hL : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, |f₁ x - f₁ z| ≤ M * |x - z|) :
    |F b - F a - (b - a) * f ((a + b) / 2)| ≤ (b - a) ^ 3 / 24 * M := by
  set m := (a + b) / 2 with hm
  set h := (b - a) / 2 with hh
  have h0 : 0 ≤ h := by rw [hh]; linarith
  have hp : ∀ s ∈ Icc 0 h, m + s ∈ Icc a b := fun s hs => by
    constructor <;> [skip; skip] <;> (have := hs.1; have := hs.2; rw [hm]; rw [hh] at *; linarith)
  have hn : ∀ s ∈ Icc 0 h, m - s ∈ Icc a b := fun s hs => by
    constructor <;> [skip; skip] <;> (have := hs.1; have := hs.2; rw [hm]; rw [hh] at *; linarith)
  have dP : ∀ {g g' : ℝ → ℝ}, (∀ x ∈ Icc a b, HasDerivAt g (g' x) x) → ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => g (m + s)) (g' (m + s)) s := fun hg s hs => by
    have := (hg (m + s) (hp s hs)).comp s ((hasDerivAt_id s).const_add m)
    simpa [Function.comp_def] using this
  have dN : ∀ {g g' : ℝ → ℝ}, (∀ x ∈ Icc a b, HasDerivAt g (g' x) x) → ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => g (m - s)) (-g' (m - s)) s := fun hg s hs => by
    have := (hg (m - s) (hn s hs)).comp s ((hasDerivAt_id s).const_sub m)
    simpa [Function.comp_def] using this
  have hχ : ∀ s ∈ Icc 0 h, |f₁ (m + s) - f₁ (m - s)| ≤ 2 * M * s := by
    intro s hs
    have := hL (m + s) (hp s hs) (m - s) (hn s hs)
    rw [show m + s - (m - s) = 2 * s by ring, abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ 2 * s)] at this
    linarith
  have hψ : ∀ s ∈ Icc 0 h, |f (m + s) + f (m - s) - 2 * f m| ≤ M * s ^ 2 := by
    have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => f (m + s) + f (m - s) - 2 * f m)
        (f₁ (m + s) - f₁ (m - s)) s := fun s hs => by
      have := ((dP hf s hs).add (dN hf s hs)).sub_const (2 * f m)
      simpa [sub_eq_add_neg] using this
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
      (f := fun s => f (m + s) + f (m - s) - 2 * f m) (f' := fun s => f₁ (m + s) - f₁ (m - s))
      (B := fun s => M * s ^ 2) (B' := fun s => 2 * M * s)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp; ring_nf)
      (fun s => by
        have := ((hasDerivAt_pow 2 s).const_mul M)
        convert this using 1; push_cast; ring)
      (fun s hs => by simpa using hχ s (Ico_subset_Icc_self hs))
    intro s hs
    simpa using this hs
  have hφ : ∀ s ∈ Icc 0 h, |F (m + s) - F (m - s) - 2 * s * f m| ≤ M * s ^ 3 / 3 := by
    have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => F (m + s) - F (m - s) - 2 * s * f m)
        (f (m + s) + f (m - s) - 2 * f m) s := fun s hs => by
      have h2 : HasDerivAt (fun s : ℝ => 2 * s * f m) (2 * f m) s := by
        simpa using ((hasDerivAt_id s).const_mul 2).mul_const (f m)
      have := ((dP hF s hs).sub (dN hF s hs)).sub h2
      convert this using 1; ring
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
      (f := fun s => F (m + s) - F (m - s) - 2 * s * f m) (f' := fun s => f (m + s) + f (m - s) - 2 * f m)
      (B := fun s => M * s ^ 3 / 3) (B' := fun s => M * s ^ 2)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp)
      (fun s => by
        have := ((hasDerivAt_pow 3 s).const_mul M).div_const 3
        convert this using 1; push_cast; ring)
      (fun s hs => by simpa using hψ s (Ico_subset_Icc_self hs))
    intro s hs
    simpa using this hs
  have key := hφ h ⟨h0, le_rfl⟩
  have e1 : m + h = b := by rw [hm, hh]; ring
  have e2 : m - h = a := by rw [hm, hh]; ring
  rw [e1, e2] at key
  have e3 : 2 * h = b - a := by rw [hh]; ring
  rw [e3] at key
  calc |F b - F a - (b - a) * f ((a + b) / 2)| ≤ M * h ^ 3 / 3 := key
    _ = (b - a) ^ 3 / 24 * M := by rw [hh]; ring

/-- **The midpoint rule**, integral form, for `f` continuous on an open `U ⊇ [a, b]` with an `M`-Lipschitz
derivative `f₁` on `[a, b]`. -/
theorem abs_integral_sub_midpoint_le_of_lip {f f₁ : ℝ → ℝ} {a b M : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hab : a ≤ b) (hsub : Icc a b ⊆ U) (hcont : ContinuousOn f U) (hf : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (hL : ∀ x ∈ Icc a b, ∀ z ∈ Icc a b, |f₁ x - f₁ z| ≤ M * |x - z|) :
    |(∫ x in a..b, f x) - (b - a) * f ((a + b) / 2)| ≤ (b - a) ^ 3 / 24 * M := by
  have hint : ∀ x ∈ Icc a b, IntervalIntegrable f MeasureTheory.volume a x := fun x hx =>
    (hcont.mono (fun y hy => hsub ?_)).intervalIntegrable
  · have hF : ∀ x ∈ Icc a b, HasDerivAt (fun u => ∫ y in a..u, f y) (f x) x := fun x hx =>
      intervalIntegral.integral_hasDerivAt_right (hint x hx)
        (hcont.stronglyMeasurableAtFilter hU x (hsub hx)) (hcont.continuousAt (hU.mem_nhds (hsub hx)))
    have := abs_sub_midpoint_le_of_lip hab hF hf hL
    simpa using this
  · rw [uIcc_of_le hx.1] at hy
    exact ⟨hy.1, hy.2.trans hx.2⟩

end SandierSerfaty.Certificate.Lambda
