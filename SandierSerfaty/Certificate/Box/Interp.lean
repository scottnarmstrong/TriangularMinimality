/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# One-variable tools of the box assertions

Certificate-free real analysis used by the outer, negative-part and Hessian arguments of paper §7
(`comp:outer-grid`, `comp:negative-part`, `comp:hessian`). Everything is stated for
functions with *right* derivatives (`HasDerivWithinAt f f' (Ici x) x`): the radial functions of the calibration
have second derivatives that jump at spline knots, so the second-order quantities `G_dd`, `G_ss` exist only
one-sidedly there; the mean-value inequalities below only use right derivatives.

* `sub_le_of_right_deriv`, `le_sub_of_right_deriv`, `abs_sub_le_of_right_deriv`, `lip_of_right_deriv`:
  increments of a continuous function with a bounded right derivative;
* `taylor_lip`: `|ψ y - ψ x - ψ' x (y - x)| ≤ M (y - x)²/2` if `ψ'` is `M`-Lipschitz;
* `interp_ge`: `ψ x ≥ min (ψ a) (ψ b) - M (b - a)²/8` if `ψ'` is `M`-Lipschitz (the 1-D interpolation step of
  `comp:outer-errors`);
* `midpoint_err`: `|∫_a^b G - (b - a) G((a + b)/2)| ≤ M (b - a)³/24` if `G'` is `M`-Lipschitz;
* `midpoint_err_lip`: `|∫_a^b Φ - (b - a) Φ((a + b)/2)| ≤ M (b - a)²/4` if `Φ` is `M`-Lipschitz (the negative
  part, `.65 S_h L₂/4` of `comp:negative-assertion`).
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Box

/-! ### Increments from right derivatives -/

theorem sub_le_of_right_deriv {f f' : ℝ → ℝ} {a b hi : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (hb : ∀ x ∈ Ico a b, f' x ≤ hi) :
    f b - f a ≤ hi * (b - a) := by
  have hB : ∀ x ∈ Ico a b, HasDerivWithinAt (fun x => f a + hi * (x - a)) hi (Ici x) x := fun x _ => by
    have := (((hasDerivAt_id x).sub_const a).const_mul hi).const_add (f a)
    simpa using this.hasDerivWithinAt
  have := image_le_of_deriv_right_le_deriv_boundary hc hd (B := fun x => f a + hi * (x - a)) (B' := fun _ => hi)
    (by simp) (by fun_prop) hB hb (x := b) ⟨hab, le_rfl⟩
  linarith

theorem le_sub_of_right_deriv {f f' : ℝ → ℝ} {a b lo : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (hb : ∀ x ∈ Ico a b, lo ≤ f' x) :
    lo * (b - a) ≤ f b - f a := by
  have := sub_le_of_right_deriv (f := fun x => -f x) (f' := fun x => -f' x) (hi := -lo) hab hc.neg
    (fun x hx => (hd x hx).neg) (fun x hx => by linarith [hb x hx])
  linarith

theorem abs_sub_le_of_right_deriv {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (hb : ∀ x ∈ Ico a b, |f' x| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  have h1 := sub_le_of_right_deriv hab hc hd (fun x hx => (abs_le.1 (hb x hx)).2)
  have h2 := le_sub_of_right_deriv (lo := -C) hab hc hd (fun x hx => (abs_le.1 (hb x hx)).1)
  rw [abs_le]; constructor <;> linarith

/-- A continuous function with a right derivative bounded by `C` on `[a, b]` is `C`-Lipschitz there. -/
theorem lip_of_right_deriv {f f' : ℝ → ℝ} {a b C : ℝ} (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) (hb : ∀ x ∈ Ico a b, |f' x| ≤ C) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ C * |x - y| := by
  have key : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ C * (y - x) := by
    intro x hx y hy hxy
    exact abs_sub_le_of_right_deriv hxy (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun z hz => (hd z ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩))
      (fun z hz => hb z ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩)
  intro x hx y hy
  rcases le_total x y with h | h
  · have := key x hx y hy h
    rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.2 h : 0 ≤ y - x)]
    exact this
  · have := key y hy x hx h
    rw [abs_of_nonneg (sub_nonneg.2 h : 0 ≤ x - y)]
    exact this

/-! ### Taylor and interpolation with a Lipschitz derivative -/

theorem taylor_aux {χ χ' : ℝ → ℝ} {h M : ℝ} (h0 : 0 ≤ h) (hd : ∀ s ∈ Icc 0 h, HasDerivAt χ (χ' s) s)
    (hl : ∀ s ∈ Icc 0 h, |χ' s - χ' 0| ≤ M * s) : |χ h - χ 0 - χ' 0 * h| ≤ M * h ^ 2 / 2 := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := h)
    (f := fun s => χ s - χ 0 - χ' 0 * s) (f' := fun s => χ' s - χ' 0)
    (B := fun s => M * s ^ 2 / 2) (B' := fun s => M * s)
    (fun s hs => (((hd s hs).sub_const (χ 0)).fun_sub ((hasDerivAt_id s).const_mul (χ' 0))).continuousAt.continuousWithinAt)
    (fun s hs => by
      have := ((hd s (Ico_subset_Icc_self hs)).sub_const (χ 0)).fun_sub ((hasDerivAt_id s).const_mul (χ' 0))
      exact (this.congr_deriv (by ring)).hasDerivWithinAt)
    (by simp)
    (fun s => by
      have := ((hasDerivAt_pow 2 s).const_mul M).div_const 2
      convert this using 1; push_cast; ring)
    (fun s hs => by simpa [Real.norm_eq_abs] using hl s (Ico_subset_Icc_self hs))
  have := key (show h ∈ Icc 0 h from ⟨h0, le_rfl⟩)
  simpa [Real.norm_eq_abs] using this

/-- **Taylor bound with a Lipschitz derivative**: `|ψ y - ψ x - ψ' x (y - x)| ≤ M (y - x)²/2`. -/
theorem taylor_lip {ψ ψ' : ℝ → ℝ} {a b M : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt ψ (ψ' x) x)
    (hl : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |ψ' x - ψ' y| ≤ M * |x - y|) {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) : |ψ y - ψ x - ψ' x * (y - x)| ≤ M * (y - x) ^ 2 / 2 := by
  rcases le_total x y with h | h
  · have := taylor_aux (χ := fun s => ψ (x + s)) (χ' := fun s => ψ' (x + s)) (h := y - x) (M := M)
      (by linarith)
      (fun s hs => by
        have hm : x + s ∈ Icc a b := ⟨by linarith [hx.1, hs.1], by linarith [hy.2, hs.2]⟩
        have := (hd (x + s) hm).comp s ((hasDerivAt_id s).const_add x)
        simpa [Function.comp_def] using this)
      (fun s hs => by
        have hm : x + s ∈ Icc a b := ⟨by linarith [hx.1, hs.1], by linarith [hy.2, hs.2]⟩
        have := hl _ hm x hx
        have e : |x + s - x| = s := by rw [show x + s - x = s by ring]; exact abs_of_nonneg hs.1
        rw [e] at this
        simpa using this)
    simpa using this
  · have := taylor_aux (χ := fun s => ψ (x - s)) (χ' := fun s => -ψ' (x - s)) (h := x - y) (M := M)
      (by linarith)
      (fun s hs => by
        have hm : x - s ∈ Icc a b := ⟨by linarith [hy.1, hs.2], by linarith [hx.2, hs.1]⟩
        have := (hd (x - s) hm).comp s ((hasDerivAt_id s).const_sub x)
        simpa [Function.comp_def] using this)
      (fun s hs => by
        have hm : x - s ∈ Icc a b := ⟨by linarith [hy.1, hs.2], by linarith [hx.2, hs.1]⟩
        have := hl _ hm x hx
        have e : |x - s - x| = s := by rw [show x - s - x = -s by ring, abs_neg]; exact abs_of_nonneg hs.1
        rw [e] at this
        show |-ψ' (x - s) - -ψ' (x - 0)| ≤ M * s
        rw [show -ψ' (x - s) - -ψ' (x - 0) = -(ψ' (x - s) - ψ' x) by rw [sub_zero]; ring, abs_neg]
        exact this)
    simp only [sub_sub_cancel] at this
    have e : ψ y - ψ x - ψ' x * (y - x) = ψ y - ψ x + ψ' x * (x - y) := by ring
    rw [e]
    have e2 : (y - x) ^ 2 = (x - y) ^ 2 := by ring
    rw [e2]
    convert this using 2
    ring_nf

/-- **The 1-D interpolation step** (`comp:outer-errors`): if `ψ'` is `M`-Lipschitz on `[a, b]`, then
`ψ x ≥ min (ψ a) (ψ b) - M (b - a)²/8` on `[a, b]`. -/
theorem interp_ge {ψ ψ' : ℝ → ℝ} {a b M : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt ψ (ψ' x) x)
    (hl : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |ψ' x - ψ' y| ≤ M * |x - y|) {x : ℝ} (hx : x ∈ Icc a b) :
    min (ψ a) (ψ b) - M * (b - a) ^ 2 / 8 ≤ ψ x := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hx.1.trans hx.2⟩
  have hb : b ∈ Icc a b := ⟨hx.1.trans hx.2, le_rfl⟩
  rcases eq_or_lt_of_le (hx.1.trans hx.2 : a ≤ b) with hab | hab
  · have h1 : x = a := le_antisymm (by linarith [hx.2]) hx.1
    subst h1
    subst hab
    simp
  · have hM : 0 ≤ M := by
      have h3 := hl a ha b hb
      have h4 : 0 < |a - b| := abs_pos.2 (by linarith)
      by_contra hneg
      push Not at hneg
      nlinarith [abs_nonneg (ψ' a - ψ' b), mul_neg_of_neg_of_pos hneg h4]
    have A := (abs_le.1 (taylor_lip hd hl hx ha)).2
    have B := (abs_le.1 (taylor_lip hd hl hx hb)).2
    obtain ⟨m, hm⟩ : ∃ m, m = min (ψ a) (ψ b) := ⟨_, rfl⟩
    have m1 : m ≤ ψ a := hm ▸ min_le_left _ _
    have m2 : m ≤ ψ b := hm ▸ min_le_right _ _
    rw [← hm]
    obtain ⟨u, hu⟩ : ∃ u, u = x - a := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, v = b - x := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by rw [hu]; linarith [hx.1]
    have hv0 : 0 ≤ v := by rw [hv]; linarith [hx.2]
    have huv : 0 < u + v := by rw [hu, hv]; linarith
    have e1 : a - x = -u := by rw [hu]; ring
    have e2 : b - x = v := by rw [hv]
    have e3 : b - a = u + v := by rw [hu, hv]; ring
    rw [e1] at A
    rw [e2] at B
    rw [e3]
    have A' : ψ a + ψ' x * u - M * u ^ 2 / 2 ≤ ψ x := by nlinarith
    have B' : ψ b - ψ' x * v - M * v ^ 2 / 2 ≤ ψ x := by nlinarith
    have hvA := mul_le_mul_of_nonneg_left A' hv0
    have huB := mul_le_mul_of_nonneg_left B' hu0
    have hfin : (u + v) * (m - M * (u + v) ^ 2 / 8) ≤ (u + v) * ψ x := by
      nlinarith [mul_nonneg hv0 (sub_nonneg.2 m1), mul_nonneg hu0 (sub_nonneg.2 m2),
        mul_nonneg hM (sq_nonneg (u - v)), mul_nonneg (mul_nonneg hM (add_nonneg hu0 hv0)) (sq_nonneg (u - v))]
    exact le_of_mul_le_mul_left hfin huv

/-! ### The midpoint rule -/

theorem integral_midpoint_sq (a b : ℝ) :
    ∫ s in a..b, (s - (a + b) / 2) ^ 2 = (b - a) ^ 3 / 12 := by
  have := intervalIntegral.integral_comp_sub_right (fun s : ℝ => s ^ 2) (a := a) (b := b) ((a + b) / 2)
  rw [this, integral_pow]
  ring

theorem integral_midpoint_lin (a b c k : ℝ) :
    ∫ s in a..b, (c + k * (s - (a + b) / 2)) = (b - a) * c := by
  have h1 : ∀ x ∈ uIcc a b, HasDerivAt (fun s => c * s + k * ((s - (a + b) / 2) ^ 2 / 2))
      (c + k * (x - (a + b) / 2)) x := fun x _ => by
    have h2 : HasDerivAt (fun s : ℝ => c * s) c x := by simpa using (hasDerivAt_id x).const_mul c
    have h3 : HasDerivAt (fun s : ℝ => (s - (a + b) / 2) ^ 2 / 2) (x - (a + b) / 2) x := by
      have := (((hasDerivAt_id x).sub_const ((a + b) / 2)).fun_pow 2).div_const 2
      exact this.congr_deriv (by simp)
    exact h2.fun_add (h3.const_mul k)
  have h4 : IntervalIntegrable (fun s : ℝ => c + k * (s - (a + b) / 2)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h4]
  ring

/-- **The midpoint rule** with a Lipschitz derivative: `|∫_a^b G - (b - a) G((a + b)/2)| ≤ M (b - a)³/24`. -/
theorem midpoint_err {G G' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hd : ∀ x ∈ Icc a b, HasDerivAt G (G' x) x)
    (hl : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |G' x - G' y| ≤ M * |x - y|) :
    |(∫ s in a..b, G s) - (b - a) * G ((a + b) / 2)| ≤ M * (b - a) ^ 3 / 24 := by
  have hmI : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hGc : ContinuousOn G (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hRc : ContinuousOn (fun s => G s - G ((a + b) / 2) - G' ((a + b) / 2) * (s - (a + b) / 2)) (Icc a b) := by
    fun_prop
  have hRi : IntervalIntegrable (fun s => G s - G ((a + b) / 2) - G' ((a + b) / 2) * (s - (a + b) / 2)) volume a b :=
    (hRc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hLi : IntervalIntegrable (fun s : ℝ => G ((a + b) / 2) + G' ((a + b) / 2) * (s - (a + b) / 2)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hsplit : (∫ s in a..b, G s) = (∫ s in a..b, (G ((a + b) / 2) + G' ((a + b) / 2) * (s - (a + b) / 2))) +
      ∫ s in a..b, (G s - G ((a + b) / 2) - G' ((a + b) / 2) * (s - (a + b) / 2)) := by
    rw [← intervalIntegral.integral_add hLi hRi]
    congr 1; funext s; ring
  rw [hsplit, integral_midpoint_lin, add_sub_cancel_left]
  have hb : ‖∫ s in a..b, (G s - G ((a + b) / 2) - G' ((a + b) / 2) * (s - (a + b) / 2))‖ ≤
      ∫ s in a..b, M / 2 * (s - (a + b) / 2) ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall fun s hs => ?_) ?_
    · have := taylor_lip hd hl hmI (Ioc_subset_Icc_self hs)
      rw [Real.norm_eq_abs]
      calc _ ≤ M * (s - (a + b) / 2) ^ 2 / 2 := this
        _ = _ := by ring
    · apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_const_mul, integral_midpoint_sq] at hb
  rw [Real.norm_eq_abs] at hb
  calc _ ≤ M / 2 * ((b - a) ^ 3 / 12) := hb
    _ = _ := by ring

theorem integral_abs_midpoint {a b : ℝ} (hab : a ≤ b) : ∫ s in a..b, |s - (a + b) / 2| = (b - a) ^ 2 / 4 := by
  have hm : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (a + b) / 2)
    (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : ∫ s in a..(a + b) / 2, |s - (a + b) / 2| = ∫ s in a..(a + b) / 2, ((a + b) / 2 - s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hm.1] at hs
    show |s - (a + b) / 2| = (a + b) / 2 - s
    rw [abs_of_nonpos (by linarith [hs.2])]; ring
  have h2 : ∫ s in (a + b) / 2..b, |s - (a + b) / 2| = ∫ s in (a + b) / 2..b, (s - (a + b) / 2) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hm.2] at hs
    show |s - (a + b) / 2| = s - (a + b) / 2
    rw [abs_of_nonneg (by linarith [hs.1])]
  rw [h1, h2]
  have h3 : ∫ s in a..(a + b) / 2, ((a + b) / 2 - s) = ((b - a) / 2) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [integral_id]; ring_nf
  have h4 : ∫ s in (a + b) / 2..b, (s - (a + b) / 2) = ((b - a) / 2) ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [integral_id]; ring_nf
  rw [h3, h4]; ring

/-- **The midpoint rule for a Lipschitz integrand**: `|∫_a^b Φ - (b - a) Φ((a + b)/2)| ≤ M (b - a)²/4`. -/
theorem midpoint_err_lip {Φ : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hc : ContinuousOn Φ (Icc a b))
    (hl : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |Φ x - Φ y| ≤ M * |x - y|) :
    |(∫ s in a..b, Φ s) - (b - a) * Φ ((a + b) / 2)| ≤ M * (b - a) ^ 2 / 4 := by
  have hmI : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hΦi : IntervalIntegrable Φ volume a b := (hc.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hc' : (∫ s in a..b, Φ s) - (b - a) * Φ ((a + b) / 2) = ∫ s in a..b, (Φ s - Φ ((a + b) / 2)) := by
    rw [intervalIntegral.integral_sub hΦi intervalIntegrable_const]
    simp
  rw [hc']
  have hb : ‖∫ s in a..b, (Φ s - Φ ((a + b) / 2))‖ ≤ ∫ s in a..b, M * |s - (a + b) / 2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab (Filter.Eventually.of_forall fun s hs => ?_) ?_
    · have := hl s (Ioc_subset_Icc_self hs) _ hmI
      rw [Real.norm_eq_abs]; exact this
    · apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_const_mul, integral_abs_midpoint hab, Real.norm_eq_abs] at hb
  calc _ ≤ _ := hb
    _ = _ := by ring

end SandierSerfaty.Certificate.Box
