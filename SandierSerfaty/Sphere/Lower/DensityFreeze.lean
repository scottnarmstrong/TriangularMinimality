/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.BlowupLaplacian
public import SandierSerfaty.Sphere.ChartLaplacian
public import SandierSerfaty.Analysis.WeylCalculus

/-!
# The density freeze (sphere note, Lemma 6.6, explicit form)

On a square `Q` about `q`, the blown-up density `m(x) = m₊ / (1 + |x|²/s²)²` (`m₊ = 1/(π κ²)`, `s = s_n`) is replaced by
its mean `m̄`: we need `v` with `Δ v = 2π (m - m̄)` and `|∇ v| = O(t² / s + t |m(q) - m̄|)` on `Q`.

**Deviation from the sphere note** (which asks for a weak Neumann problem): for the
radial density `m` the correction is explicit.  With `P(x) = (π c s² / 2) log (1 + |x|²/s²)` (so `Δ P = 2π m`) put
`v = P - (second-order Taylor polynomial of P at q) + (π/2)(m(q) - m̄)|x - q|²`.  Then `Δ v = 2π (m - m̄)` exactly
(`Lower.laplacian_fz`) and `∇ v` is the second-order Taylor remainder of `∇ P = π c x / (1 + |x|²/s²)` plus
`π (m(q) - m̄)(x - q)`, bounded by `7π c |x - q|² / s + π |m(q) - m̄| |x - q|` (`Lower.norm_fzGrad_le`), from the
algebraic estimate `Lower.taylor_grad_bound`.  No Neumann problem, Poincaré inequality or Newtonian potential is needed.
-/

open Laplacian
open scoped RealInnerProductSpace ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem taylor_aux (u w : ℂ) (N p e : ℝ) (hN : N ≠ 0) (hN' : N + 2 * p + e ≠ 0) :
    (1 / (N + 2 * p + e)) • (u + w) - (1 / N) • u - ((1 / N) • w - (2 * p / N ^ 2) • u) =
      (-(2 * p + e) / (N * (N + 2 * p + e))) • w -
        ((e * N - 2 * p * (2 * p + e)) / (N ^ 2 * (N + 2 * p + e))) • u := by
  match_scalars <;> field_simp <;> ring

theorem taylor_grad_identity (q η : ℂ) :
    (1 / (1 + ‖q + η‖ ^ 2)) • (q + η) - (1 / (1 + ‖q‖ ^ 2)) • q -
        ((1 / (1 + ‖q‖ ^ 2)) • η - (2 * inner ℝ q η / (1 + ‖q‖ ^ 2) ^ 2) • q) =
      (-(2 * inner ℝ q η + ‖η‖ ^ 2) / ((1 + ‖q‖ ^ 2) * (1 + ‖q + η‖ ^ 2))) • η -
        ((‖η‖ ^ 2 * (1 + ‖q‖ ^ 2) - 2 * inner ℝ q η * (2 * inner ℝ q η + ‖η‖ ^ 2)) /
          ((1 + ‖q‖ ^ 2) ^ 2 * (1 + ‖q + η‖ ^ 2))) • q := by
  have h2 : 1 + ‖q + η‖ ^ 2 = (1 + ‖q‖ ^ 2) + 2 * inner ℝ q η + ‖η‖ ^ 2 := by
    rw [norm_add_sq_real]; ring
  rw [h2]
  exact taylor_aux q η (1 + ‖q‖ ^ 2) (inner ℝ q η) (‖η‖ ^ 2) (by positivity) (by rw [← h2]; positivity)

theorem taylor_grad_bound (q η : ℂ) :
    ‖(1 / (1 + ‖q + η‖ ^ 2)) • (q + η) - (1 / (1 + ‖q‖ ^ 2)) • q -
        ((1 / (1 + ‖q‖ ^ 2)) • η - (2 * inner ℝ q η / (1 + ‖q‖ ^ 2) ^ 2) • q)‖ ≤ 7 * ‖η‖ ^ 2 := by
  rw [taylor_grad_identity]
  set a := ‖q‖ with ha
  set e := ‖η‖ with he
  set N := 1 + a ^ 2 with hN
  set N' := 1 + ‖q + η‖ ^ 2 with hN'
  set p := inner ℝ q η with hp
  have ha0 : 0 ≤ a := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  have hNp : 0 < N := by positivity
  have hN'p : 0 < N' := by positivity
  have hN1 : 1 ≤ N := by linarith [sq_nonneg a]
  have hN'1 : 1 ≤ N' := by linarith [sq_nonneg ‖q + η‖]
  have hpa : |p| ≤ a * e := abs_real_inner_le_norm q η
  have h2a : 2 * a ≤ N := by linarith [sq_nonneg (a - 1)]
  have h2b : 2 * ‖q + η‖ ≤ N' := by linarith [sq_nonneg (‖q + η‖ - 1)]
  have heq : e ≤ ‖q + η‖ + a := by
    have := norm_sub_le (q + η) q
    simpa [he, ha] using this
  have hx1 : a / N ≤ 1 / 2 := by rw [div_le_iff₀ hNp]; linarith
  have hx2 : 1 / N' ≤ 1 := by rw [div_le_one hN'p]; exact hN'1
  have hx4 : a ^ 2 / N ≤ 1 := by rw [div_le_one hNp]; linarith
  have hx3 : e / (N * N') ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [mul_nonneg (sub_nonneg.2 hN1) (sub_nonneg.2 hN'1)]
  set T := 2 * p + e ^ 2 with hT
  have hTa : |T| ≤ 2 * a * e + e ^ 2 := by
    rw [hT]
    calc |2 * p + e ^ 2| ≤ |2 * p| + |e ^ 2| := abs_add_le _ _
      _ ≤ 2 * (a * e) + e ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg e)]
        linarith
      _ = 2 * a * e + e ^ 2 := by ring
  set X := e ^ 2 * N - 2 * p * T with hX
  have hXa : |X| ≤ e ^ 2 * N + 2 * (a * e) * (2 * a * e + e ^ 2) := by
    rw [hX]
    calc |e ^ 2 * N - 2 * p * T| ≤ |e ^ 2 * N| + |2 * p * T| := abs_sub _ _
      _ ≤ _ := by
        have h1 : |e ^ 2 * N| = e ^ 2 * N := abs_of_nonneg (by positivity)
        have h2 : |2 * p * T| ≤ 2 * (a * e) * (2 * a * e + e ^ 2) := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have := mul_le_mul hpa hTa (abs_nonneg _) (by positivity)
          linarith
        linarith
  calc ‖(-T / (N * N')) • η - (X / (N ^ 2 * N')) • q‖
      ≤ ‖(-T / (N * N')) • η‖ + ‖(X / (N ^ 2 * N')) • q‖ := norm_sub_le _ _
    _ = |T| / (N * N') * e + |X| / (N ^ 2 * N') * a := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div, abs_neg,
          abs_of_pos (by positivity : 0 < N * N'), abs_of_pos (by positivity : 0 < N ^ 2 * N')]
    _ ≤ (2 * a * e + e ^ 2) / (N * N') * e +
          (e ^ 2 * N + 2 * (a * e) * (2 * a * e + e ^ 2)) / (N ^ 2 * N') * a := by
        gcongr
    _ = e ^ 2 * ((2 * (a / N) * (1 / N') + e / (N * N')) + (a / N) * (1 / N') +
          2 * (a ^ 2 / N) * (2 * (a / N) * (1 / N') + e / (N * N'))) := by
        field_simp
        ring
    _ ≤ e ^ 2 * 7 := by
        gcongr
        have hxx : (a / N) * (1 / N') ≤ 1 / 2 := by
          calc (a / N) * (1 / N') ≤ (1 / 2) * 1 := mul_le_mul hx1 hx2 (by positivity) (by norm_num)
            _ = 1 / 2 := by norm_num
        have hs : 2 * (a / N) * (1 / N') + e / (N * N') ≤ 2 := by linarith
        have h4 : 0 ≤ a ^ 2 / N := by positivity
        linarith [mul_le_mul hx4 hs (by positivity) (by norm_num : (0 : ℝ) ≤ 1)]
    _ = 7 * e ^ 2 := by ring

/-- `N_s(x) = 1 + |x|²/s²`. -/
noncomputable def dN (s : ℝ) (x : ℂ) : ℝ := 1 + ‖x‖ ^ 2 / s ^ 2

theorem dN_pos (s : ℝ) (x : ℂ) : 0 < dN s x := by unfold dN; positivity

theorem one_le_dN (s : ℝ) (x : ℂ) : 1 ≤ dN s x := by
  unfold dN; have : 0 ≤ ‖x‖ ^ 2 / s ^ 2 := by positivity
  linarith

/-- The explicit freeze potential. -/
noncomputable def fz (c s : ℝ) (q : ℂ) (A B : ℝ) (x : ℂ) : ℝ :=
  Real.pi * c * s ^ 2 / 2 * (potV (s⁻¹ • x) - potV (s⁻¹ • q)) -
    Real.pi * c / dN s q * inner ℝ q (x - q) -
    (1 / 2) * (A * ‖x - q‖ ^ 2 + B * inner ℝ q (x - q) ^ 2)

/-- Its gradient. -/
noncomputable def fzGrad (c s : ℝ) (q : ℂ) (A B : ℝ) (x : ℂ) : ℂ :=
  (Real.pi * c / dN s x) • x - (Real.pi * c / dN s q) • q - A • (x - q) -
    (B * inner ℝ q (x - q)) • q

theorem hasFDerivAt_potV' (y : ℂ) :
    HasFDerivAt potV ((2 / (1 + ‖y‖ ^ 2)) • innerSL ℝ y) y := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ y) y := by
    simpa using ((hasFDerivAt_id y).norm_sq).const_add 1
  have h2 := h1.log (by positivity)
  refine h2.congr_fderiv ?_
  ext h
  simp [two_smul, div_eq_inv_mul]
  ring

theorem hasFDerivAt_fz {c s : ℝ} (hs : s ≠ 0) (q : ℂ) (A B : ℝ) (x : ℂ) :
    HasFDerivAt (fz c s q A B) (innerSL ℝ (fzGrad c s q A B x)) x := by
  have hP : HasFDerivAt (fun x : ℂ => potV (s⁻¹ • x))
      (((2 / (1 + ‖s⁻¹ • x‖ ^ 2)) • innerSL ℝ (s⁻¹ • x)).comp (s⁻¹ • (ContinuousLinearMap.id ℝ ℂ))) x :=
    (hasFDerivAt_potV' (s⁻¹ • x)).comp x ((hasFDerivAt_id x).const_smul s⁻¹)
  have hQ1 := Weyl.hasFDerivAt_inner_sub q q x
  have hQ2 := Weyl.hasFDerivAt_normSq_sub q x
  have hQ3 := hQ1.pow 2
  have := ((hP.sub_const (potV (s⁻¹ • q))).const_mul (Real.pi * c * s ^ 2 / 2)).sub
    (hQ1.const_mul (Real.pi * c / dN s q)) |>.sub (((hQ2.const_mul A).add (hQ3.const_mul B)).const_mul (1 / 2 : ℝ))
  refine this.congr_fderiv ?_
  ext h
  simp only [fzGrad, dN, innerSL_apply_apply, FunLike.coe_sub, Pi.sub_apply,
    smul_apply, add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, two_smul]
  have hn : ‖s⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / s ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, div_eq_inv_mul]
  simp only [hn, inner_sub_left, real_inner_smul_left, real_inner_smul_right, pow_one, Nat.add_one_sub_one]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have h1 : (1 + ‖x‖ ^ 2 / s ^ 2) ≠ 0 := by positivity
  field_simp
  ring


theorem pd_fz {c s : ℝ} (hs : s ≠ 0) (q : ℂ) (A B : ℝ) (v x : ℂ) :
    Weyl.pd v (fz c s q A B) x = inner ℝ (fzGrad c s q A B x) v := by
  unfold Weyl.pd
  rw [(hasFDerivAt_fz hs q A B x).fderiv]
  rfl

theorem pd_pd_fz {c s : ℝ} (hs : s ≠ 0) (q : ℂ) (A B : ℝ) (v x : ℂ) :
    Weyl.pd v (Weyl.pd v (fz c s q A B)) x =
      Real.pi * c / dN s x * inner ℝ v v -
        Real.pi * c / dN s x ^ 2 * (2 * inner ℝ x v / s ^ 2) * inner ℝ x v -
        A * inner ℝ v v - B * inner ℝ q v * inner ℝ q v := by
  have e : Weyl.pd v (fz c s q A B) = fun y => inner ℝ (fzGrad c s q A B y) v := by
    funext y; exact pd_fz hs q A B v y
  rw [e]
  unfold fzGrad
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hd : HasFDerivAt (fun y : ℂ => dN s y) ((2 / s ^ 2) • innerSL ℝ x) x := by
    have h0 : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
      simpa using (hasFDerivAt_id x).norm_sq
    have h1 := (h0.const_mul (s ^ 2)⁻¹).const_add 1
    have e : (fun y : ℂ => dN s y) = fun y => 1 + (s ^ 2)⁻¹ * ‖y‖ ^ 2 := by
      funext y; simp [dN, div_eq_inv_mul]
    rw [e]
    refine h1.congr_fderiv ?_
    ext h
    simp [two_smul]
    ring
  have hinv : HasFDerivAt (fun y : ℂ => Real.pi * c / dN s y)
      ((-(Real.pi * c) / dN s x ^ 2) • ((2 / s ^ 2) • innerSL ℝ x)) x := by
    have := (hasDerivAt_inv (dN_pos s x).ne').comp_hasFDerivAt x hd |>.const_mul (Real.pi * c)
    refine this.congr_fderiv ?_
    ext h
    simp [div_eq_mul_inv]
    ring
  have hxv : HasFDerivAt (fun y : ℂ => inner ℝ y v) (innerSL ℝ v) x := by
    have := (innerSL ℝ v).hasFDerivAt (x := x)
    refine this.congr_fderiv rfl |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y => by simp [real_inner_comm]
  have hq1 := Weyl.hasFDerivAt_inner_sub q q x
  have hall := (((hinv.mul hxv).sub_const (Real.pi * c / dN s q * inner ℝ q v)).sub
    ((hxv.sub_const (inner ℝ q v)).const_mul A)).sub (hq1.mul_const (B * inner ℝ q v))
  have hall' : HasFDerivAt (fun y : ℂ => inner ℝ ((Real.pi * c / dN s y) • y -
      (Real.pi * c / dN s q) • q - A • (y - q) - (B * inner ℝ q (y - q)) • q) v) _ x :=
    hall.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
      simp only [Pi.sub_apply, Pi.mul_apply, inner_sub_left, real_inner_smul_left]
      ring)
  unfold Weyl.pd
  rw [hall'.fderiv]
  simp only [sub_apply, add_apply, smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

theorem contDiff_fz (c s : ℝ) (q : ℂ) (A B : ℝ) : ContDiff ℝ ∞ (fz c s q A B) := by
  unfold fz
  have h1 : ContDiff ℝ ∞ fun x : ℂ => potV (s⁻¹ • x) :=
    contDiff_potV.comp (contDiff_const_smul _)
  have h2 : ContDiff ℝ ∞ fun x : ℂ => inner ℝ q (x - q) :=
    contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)
  have h3 : ContDiff ℝ ∞ fun x : ℂ => ‖x - q‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  exact (contDiff_const.mul (h1.sub contDiff_const)).sub (contDiff_const.mul h2) |>.sub
    (contDiff_const.mul ((contDiff_const.mul h3).add (contDiff_const.mul (h2.pow 2))))

/-- `Δ fz = 2π c / N² - (2A + B |q|²)`. -/
theorem laplacian_fz {c s : ℝ} (hs : s ≠ 0) (q : ℂ) (A B : ℝ) (x : ℂ) :
    Δ (fz c s q A B) x = 2 * Real.pi * c / dN s x ^ 2 - (2 * A + B * ‖q‖ ^ 2) := by
  have hc : ContDiffAt ℝ 2 (fz c s q A B) x :=
    ((contDiff_fz c s q A B).of_le (by norm_cast)).contDiffAt
  rw [Weyl.lap_eq_pd hc, pd_pd_fz hs, pd_pd_fz hs]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hd := dN_pos s x
  have hn : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hdx : dN s x = 1 + ‖x‖ ^ 2 / s ^ 2 := rfl
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im]
  rw [hdx] at hd ⊢
  rw [hn x, hn q] at *
  field_simp
  ring

/-- The coefficient `A` of the quadratic part of the freeze potential. -/
@[expose] noncomputable def Afz (c s : ℝ) (q : ℂ) (mb : ℝ) : ℝ :=
  Real.pi * c / dN s q - Real.pi * (c / dN s q ^ 2 - mb)

/-- The coefficient `B` of the quadratic part of the freeze potential. -/
@[expose] noncomputable def Bfz (c s : ℝ) (q : ℂ) : ℝ := -(2 * Real.pi * c) / (s ^ 2 * dN s q ^ 2)

theorem norm_smul_inv_sq {s : ℝ} (y : ℂ) : ‖s⁻¹ • y‖ ^ 2 = ‖y‖ ^ 2 / s ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, div_eq_inv_mul]

theorem one_add_norm_smul_inv_sq (s : ℝ) (y : ℂ) : 1 + ‖s⁻¹ • y‖ ^ 2 = dN s y := by
  rw [norm_smul_inv_sq]; rfl

theorem fzGrad_eq {c s : ℝ} (hs : s ≠ 0) (q : ℂ) (mb : ℝ) (x : ℂ) :
    fzGrad c s q (Afz c s q mb) (Bfz c s q) x =
      (Real.pi * c * s) •
          ((1 / (1 + ‖s⁻¹ • q + s⁻¹ • (x - q)‖ ^ 2)) • (s⁻¹ • q + s⁻¹ • (x - q)) -
            (1 / (1 + ‖s⁻¹ • q‖ ^ 2)) • (s⁻¹ • q) -
            ((1 / (1 + ‖s⁻¹ • q‖ ^ 2)) • (s⁻¹ • (x - q)) -
              (2 * inner ℝ (s⁻¹ • q) (s⁻¹ • (x - q)) / (1 + ‖s⁻¹ • q‖ ^ 2) ^ 2) • (s⁻¹ • q))) +
        (Real.pi * (c / dN s q ^ 2 - mb)) • (x - q) := by
  have hsum : s⁻¹ • q + s⁻¹ • (x - q) = s⁻¹ • x := by rw [← smul_add]; congr 1; abel
  rw [hsum, one_add_norm_smul_inv_sq, one_add_norm_smul_inv_sq, real_inner_smul_left,
    real_inner_smul_right]
  unfold fzGrad Afz Bfz
  have hN := (dN_pos s q).ne'
  have hN' := (dN_pos s x).ne'
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hxq : x - q = x - q := rfl
  match_scalars <;> field_simp <;> ring

/-- **The gradient of the freeze potential is a second-order Taylor remainder.** -/
theorem norm_fzGrad_le {c s : ℝ} (hc : 0 ≤ c) (hs : 0 < s) (q : ℂ) (mb : ℝ) (x : ℂ) :
    ‖fzGrad c s q (Afz c s q mb) (Bfz c s q) x‖ ≤
      7 * Real.pi * c * ‖x - q‖ ^ 2 / s + Real.pi * |c / dN s q ^ 2 - mb| * ‖x - q‖ := by
  rw [fzGrad_eq hs.ne']
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h := taylor_grad_bound (s⁻¹ • q) (s⁻¹ • (x - q))
    have h2 : ‖s⁻¹ • (x - q)‖ ^ 2 = ‖x - q‖ ^ 2 / s ^ 2 := norm_smul_inv_sq _
    rw [h2] at h
    calc Real.pi * c * s * _ ≤ Real.pi * c * s * (7 * (‖x - q‖ ^ 2 / s ^ 2)) := by gcongr
      _ = 7 * Real.pi * c * ‖x - q‖ ^ 2 / s := by field_simp
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]

/-- **Lemma 6.6, explicit form.** For every `q`, `m̄` and `n ≥ 1` there is a smooth `v` with
`Δ v = 2π (m - m̄)` on `ℂ` (`m = blowupDens n`) and `‖∇ v (x)‖ ≤ 7π m₊ ‖x - q‖² / s_n + π |m(q) - m̄| ‖x - q‖`. -/
theorem exists_density_freeze {n : ℕ} (hn : 0 < n) (q : ℂ) (mb : ℝ) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - mb)) ∧
      ∀ x, ‖gradient v x‖ ≤ 7 * Real.pi * mPlus * ‖x - q‖ ^ 2 / blowupScale n +
        Real.pi * |blowupDens n q - mb| * ‖x - q‖ := by
  have hs := blowupScale_pos hn
  have hdens : ∀ x, blowupDens n x = mPlus / dN (blowupScale n) x ^ 2 := by
    intro x
    unfold blowupDens lam mPlus dN
    have hk := blowupKappa_pos
    have hp := Real.pi_pos
    rw [norm_smul_inv_sq]
    field_simp
    norm_num
  refine ⟨fz mPlus (blowupScale n) q (Afz mPlus (blowupScale n) q mb) (Bfz mPlus (blowupScale n) q),
    contDiff_fz _ _ _ _ _, fun x => ?_, fun x => ?_⟩
  · rw [laplacian_fz hs.ne', hdens x]
    unfold Afz Bfz
    have hN := (dN_pos (blowupScale n) x).ne'
    have hNq := (dN_pos (blowupScale n) q).ne'
    have hs2 : blowupScale n ^ 2 ≠ 0 := pow_ne_zero 2 hs.ne'
    have hq : ‖q‖ ^ 2 = (dN (blowupScale n) q - 1) * blowupScale n ^ 2 := by
      unfold dN; field_simp; ring
    rw [hq]
    field_simp
    ring
  · have hg : gradient (fz mPlus (blowupScale n) q (Afz mPlus (blowupScale n) q mb)
        (Bfz mPlus (blowupScale n) q)) x =
        fzGrad mPlus (blowupScale n) q (Afz mPlus (blowupScale n) q mb) (Bfz mPlus (blowupScale n) q) x :=
      (HasGradientAt.gradient (by
        have := hasFDerivAt_fz hs.ne' (c := mPlus) q (Afz mPlus (blowupScale n) q mb)
          (Bfz mPlus (blowupScale n) q) x
        exact this))
    rw [hg]
    have := norm_fzGrad_le mPlus_pos.le hs q mb x
    rw [← hdens q] at this
    exact this

theorem blowupDens_eq_dN {n : ℕ} (x : ℂ) :
    blowupDens n x = mPlus / dN (blowupScale n) x ^ 2 := by
  unfold blowupDens lam mPlus dN
  have hk := blowupKappa_pos
  have hp := Real.pi_pos
  rw [norm_smul_inv_sq]
  field_simp
  norm_num

/-- The blown-up density is Lipschitz with constant `2 m₊ / s_n`. -/
theorem abs_blowupDens_sub_le {n : ℕ} (hn : 0 < n) (x y : ℂ) :
    |blowupDens n x - blowupDens n y| ≤ 2 * mPlus * ‖x - y‖ / blowupScale n := by
  have hs := blowupScale_pos hn
  set s := blowupScale n
  rw [blowupDens_eq_dN, blowupDens_eq_dN]
  have hNx : 1 ≤ dN s x := by unfold dN; have : 0 ≤ ‖x‖ ^ 2 / s ^ 2 := by positivity
                              linarith
  have hNy : 1 ≤ dN s y := by unfold dN; have : 0 ≤ ‖y‖ ^ 2 / s ^ 2 := by positivity
                              linarith
  have hx2 : ‖x‖ / s ≤ dN s x / 2 := by
    unfold dN; nlinarith [sq_nonneg (‖x‖ / s - 1), div_pow ‖x‖ s 2]
  have hy2 : ‖y‖ / s ≤ dN s y / 2 := by
    unfold dN; nlinarith [sq_nonneg (‖y‖ / s - 1), div_pow ‖y‖ s 2]
  have hdiff : |1 / dN s x - 1 / dN s y| ≤ ‖x - y‖ / s := by
    have hxy : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
    have hNxy : dN s y - dN s x = (‖y‖ - ‖x‖) * ((‖y‖ + ‖x‖) / s ^ 2) := by unfold dN; ring
    rw [div_sub_div _ _ (by positivity) (by positivity), abs_div, abs_of_pos (by positivity : 0 < dN s x * dN s y)]
    rw [div_le_div_iff₀ (by positivity) hs]
    have : |1 * dN s y - dN s x * 1| = |‖y‖ - ‖x‖| * ((‖y‖ + ‖x‖) / s ^ 2) := by
      rw [one_mul, mul_one, hNxy, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (‖y‖ + ‖x‖) / s ^ 2)]
    rw [this]
    have h1 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by rw [abs_sub_comm]; exact hxy
    have h2 : (‖y‖ + ‖x‖) / s ^ 2 * s ≤ dN s x * dN s y := by
      have : (‖y‖ + ‖x‖) / s ^ 2 * s = ‖y‖ / s + ‖x‖ / s := by field_simp
      rw [this]; nlinarith
    calc |‖y‖ - ‖x‖| * ((‖y‖ + ‖x‖) / s ^ 2) * s ≤ ‖x - y‖ * ((‖y‖ + ‖x‖) / s ^ 2 * s) := by
          rw [mul_assoc]; gcongr
      _ ≤ ‖x - y‖ * (dN s x * dN s y) := by gcongr
  have hsq : |1 / dN s x ^ 2 - 1 / dN s y ^ 2| ≤ 2 * (‖x - y‖ / s) := by
    have e : 1 / dN s x ^ 2 - 1 / dN s y ^ 2 =
        (1 / dN s x - 1 / dN s y) * (1 / dN s x + 1 / dN s y) := by ring
    rw [e, abs_mul]
    have h1 : |1 / dN s x + 1 / dN s y| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      have a1 : 1 / dN s x ≤ 1 := by rw [div_le_one (by positivity)]; exact hNx
      have a2 : 1 / dN s y ≤ 1 := by rw [div_le_one (by positivity)]; exact hNy
      linarith
    calc |1 / dN s x - 1 / dN s y| * |1 / dN s x + 1 / dN s y| ≤ ‖x - y‖ / s * 2 :=
          mul_le_mul hdiff h1 (abs_nonneg _) (by positivity)
      _ = 2 * (‖x - y‖ / s) := by ring
  calc |mPlus / dN s x ^ 2 - mPlus / dN s y ^ 2| = mPlus * |1 / dN s x ^ 2 - 1 / dN s y ^ 2| := by
        rw [← abs_of_pos mPlus_pos, ← abs_mul, abs_of_pos mPlus_pos]; congr 1; ring
    _ ≤ mPlus * (2 * (‖x - y‖ / s)) := by gcongr; exact mPlus_pos.le
    _ = 2 * mPlus * ‖x - y‖ / s := by ring

end Lower

end Sphere

end SandierSerfaty

end
