/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropEBound
public import SandierSerfaty.Tails.OmittedModes

/-!
# `e - ẽ` (paper `tail:e-estimate`)

`e = ẽ + ½ ∑_{(i,k) ∉ [0,38]²} Q_i Q_k/(k_i + k_k)` on `(b/2, 1)`; the spline `Q_i = t D_i' - k_i D_i` is `C¹`
there (`hasDerivAt_Q`), so the off-block series is `C¹` (`hasDerivAt_sR_tsum`) and
`e' - ẽ' = ½ ∑ (Q_i Q_k)'/(k_i + k_k)`. On the closed segment `seg j` the splines are the pieces, so the same
expressions are the explicit piece formulas (`Ee0`, `Ee1`, `Ee2`), where `Ee2` is the second derivative of the
error on the interior `Vg j` of the segment and the one-sided one at the knots. The bound is
`tail:e-estimate`: `|e - ẽ|_{2,t} ≤ 16 (2·10⁶) 𝔞 + 32 𝔞²` on `seg j ∩ [b, l]` (`e_error_bound`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-! ### Spline level: `Q_i` is `C¹` on `(0, ∞)` -/

/-- `Q_i' = t D_i'' + (1 - k_i) D_i'` for the spline. -/
@[expose] noncomputable def Qs1 (i : ℕ) (t : ℝ) : ℝ :=
  t * deriv (deriv (D i)) t + (1 - (k i : ℝ)) * deriv (D i) t

theorem hasDerivAt_Q (i : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (Q i) (Qs1 i t) t := by
  have h0 := (jet_D i).d0 t ht
  have h1 := (jet_D i).d1 t ht
  have h := ((hasDerivAt_id' t).mul h1).sub (h0.const_mul (k i : ℝ))
  exact h.congr_deriv (by unfold Qs1; ring)

/-- `|Q_i|_{1,t} ≤ (k_i + 1) |D_i|_{2,t}` for `0 < t ≤ 1`. -/
theorem jn₁_Q_le (i : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    jn₁ (Q i) (Qs1 i) t ≤ ((k i : ℝ) + 1) * jD i t := by
  have hk : (6 : ℝ) ≤ k i := by exact_mod_cast k_ge_six i
  have n0 := abs_nonneg (D i t)
  have n1 := abs_nonneg (deriv (D i) t)
  have n2 := abs_nonneg (deriv (deriv (D i)) t)
  have a0 : |Q i t| ≤ t * |deriv (D i) t| + (k i : ℝ) * |D i t| := by
    unfold Q
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ k i)]
  have a1 : |Qs1 i t| ≤ t * |deriv (deriv (D i)) t| + ((k i : ℝ) - 1) * |deriv (D i) t| := by
    unfold Qs1
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_nonpos (by linarith : 1 - (k i : ℝ) ≤ 0)]
    linarith
  have b1 : t * |deriv (D i) t| ≤ |deriv (D i) t| := mul_le_of_le_one_left n1 ht1
  have b2 : t * |deriv (deriv (D i)) t| ≤ |deriv (deriv (D i)) t| := mul_le_of_le_one_left n2 ht1
  unfold jn₁ jD
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ)) n0, mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ)) n1,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (k i : ℝ) - 1) n2]

theorem jn₁_Q_le_mq (i : ℕ) {t : ℝ} (ht : t ∈ dom) : jn₁ (Q i) (Qs1 i) t ≤ 2 * mq i := by
  have ht0 : 0 < t := dom_subset_Ioi ht
  refine (jn₁_Q_le i ht0 ht.2.le).trans ?_
  have h := qt_le_mq ht i
  have hj := jD_nonneg i t
  have hk : (6 : ℝ) ≤ k i := by exact_mod_cast k_ge_six i
  nlinarith

/-- The spline term `Q_i Q_k/(k_i + k_k)` and its derivative, off the retained block. -/
@[expose] noncomputable def sR0 (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0 else cc ij * (Q ij.1 t * Q ij.2 t)

@[expose] noncomputable def sR1 (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0 else cc ij * (Qs1 ij.1 t * Q ij.2 t + Q ij.1 t * Qs1 ij.2 t)

theorem hasDerivAt_sR (ij : ℕ × ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (sR0 ij) (sR1 ij t) t := by
  by_cases h : ij.1 < 39 ∧ ij.2 < 39
  · have e0 : sR0 ij = fun _ => 0 := by funext x; simp [sR0, h]
    rw [e0]
    simpa [sR1, h] using hasDerivAt_const t (0 : ℝ)
  · have e0 : sR0 ij = fun x => cc ij * (Q ij.1 x * Q ij.2 x) := by funext x; simp [sR0, h]
    rw [e0]
    simp only [sR1, ite_eq_right h]
    exact ((hasDerivAt_Q ij.1 ht).mul (hasDerivAt_Q ij.2 ht)).const_mul (cc ij)

theorem abs_sR_le (ij : ℕ × ℕ) {t : ℝ} (ht : t ∈ dom) :
    |sR0 ij t| + |sR1 ij t| ≤ rest (fun i => 2 * mq i) ij := by
  by_cases h : ij.1 < 39 ∧ ij.2 < 39
  · simp [sR0, sR1, rest, h]
  · simp only [sR0, sR1, rest, ite_eq_right h]
    have m1 := jn₁_Q_le_mq ij.1 ht
    have m2 := jn₁_Q_le_mq ij.2 ht
    have hmul := jn₁_mul_le (Q ij.1 t) (Qs1 ij.1 t) (Q ij.2 t) (Qs1 ij.2 t)
    unfold jn₁ at m1 m2
    have hcc := abs_cc_le ij
    have hn1 : 0 ≤ |Q ij.1 t| + |Qs1 ij.1 t| := by positivity
    have hn2 : 0 ≤ |Q ij.2 t| + |Qs1 ij.2 t| := by positivity
    have hxy : |Q ij.1 t * Q ij.2 t| + |Qs1 ij.1 t * Q ij.2 t + Q ij.1 t * Qs1 ij.2 t| ≤
        (2 * mq ij.1) * (2 * mq ij.2) := hmul.trans (mul_le_mul m1 m2 hn2 (hn1.trans m1))
    have ea : |cc ij * (Q ij.1 t * Q ij.2 t)| = |cc ij| * |Q ij.1 t * Q ij.2 t| := abs_mul _ _
    have eb : |cc ij * (Qs1 ij.1 t * Q ij.2 t + Q ij.1 t * Qs1 ij.2 t)| =
        |cc ij| * |Qs1 ij.1 t * Q ij.2 t + Q ij.1 t * Qs1 ij.2 t| := abs_mul _ _
    rw [ea, eb, ← mul_add]
    calc |cc ij| * (|Q ij.1 t * Q ij.2 t| + |Qs1 ij.1 t * Q ij.2 t + Q ij.1 t * Qs1 ij.2 t|)
        ≤ 1 * ((2 * mq ij.1) * (2 * mq ij.2)) :=
          mul_le_mul hcc hxy (by positivity) zero_le_one
      _ = _ := one_mul _

theorem summable_2mq : Summable fun ij : ℕ × ℕ => rest (fun i => 2 * mq i) ij :=
  summable_rest (fun i => by have := mq_nonneg i; positivity) (summable_mq.mul_left 2)

theorem summable_sR0 {t : ℝ} (ht : t ∈ dom) : Summable fun ij => sR0 ij t :=
  Summable.of_norm_bounded summable_2mq fun ij => by
    rw [Real.norm_eq_abs]; have := abs_sR_le ij ht; linarith [abs_nonneg (sR1 ij t)]

theorem hasDerivAt_sR_tsum {x : ℝ} (hx : x ∈ dom) :
    HasDerivAt (fun y => ∑' ij, sR0 ij y) (∑' ij, sR1 ij x) x :=
  hasDerivAt_tsum_of_isPreconnected (g := sR0) (g' := sR1) summable_2mq isOpen_dom isPreconnected_dom
    (fun ij y hy => hasDerivAt_sR ij (dom_subset_Ioi hy))
    (fun ij y hy => by
      rw [Real.norm_eq_abs]; have := abs_sR_le ij hy; linarith [abs_nonneg (sR0 ij y)])
    hx (summable_sR0 hx) hx

theorem cc_mul (ij : ℕ × ℕ) (t : ℝ) :
    cc ij * (Q ij.1 t * Q ij.2 t) = Q ij.1 t * Q ij.2 t / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) := by
  unfold cc; ring

theorem Trunc_e_eq : Trunc.e = fun t =>
    1 / 2 * ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39, cc (i, j) * (Q i t * Q j t) := by
  funext t
  unfold Trunc.e
  simp only [Trunc.modes_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [cc_mul]

theorem e_eq {t : ℝ} (ht : t ∈ dom) : e t = Trunc.e t + 1 / 2 * ∑' ij, sR0 ij t := by
  set T : ℕ × ℕ → ℝ := fun ij => cc ij * (Q ij.1 t * Q ij.2 t) with hT
  have hb0 : ∀ ij ∉ (Finset.range 39 ×ˢ Finset.range 39),
      (if ij.1 < 39 ∧ ij.2 < 39 then T ij else 0) = 0 := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, not_and] at hij
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hij h1 h2
  have hb : Summable fun ij : ℕ × ℕ => if ij.1 < 39 ∧ ij.2 < 39 then T ij else 0 :=
    summable_of_ne_finset_zero hb0
  have hsplit : T = fun ij => (if ij.1 < 39 ∧ ij.2 < 39 then T ij else 0) + sR0 ij t := by
    funext ij; simp only [hT, sR0]; split_ifs <;> simp
  have hsum : ∑' ij, T ij = ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39, T (i, j) + ∑' ij, sR0 ij t := by
    rw [hsplit, hb.tsum_add (summable_sR0 ht), tsum_eq_sum hb0, Finset.sum_product]
    congr 1
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp [sR0, Finset.mem_range.1 hi, Finset.mem_range.1 hj]
  have : e t = 1 / 2 * ∑' ij, T ij := by
    unfold e
    congr 1
    exact tsum_congr fun ij => (cc_mul ij t).symm
  rw [this, hsum, Trunc_e_eq]
  ring

/-- `ẽ'` (the spline form). -/
@[expose] noncomputable def sTe1 (t : ℝ) : ℝ :=
  1 / 2 * ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39,
    cc (i, j) * (Qs1 i t * Q j t + Q i t * Qs1 j t)

theorem hasDerivAt_Trunc_e {t : ℝ} (ht : 0 < t) : HasDerivAt Trunc.e (sTe1 t) t := by
  rw [Trunc_e_eq]
  exact (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_Q i ht).mul (hasDerivAt_Q j ht)).const_mul (cc (i, j))).const_mul (1 / 2)

theorem hasDerivAt_e {t : ℝ} (ht : t ∈ dom) :
    HasDerivAt e (sTe1 t + 1 / 2 * ∑' ij, sR1 ij t) t := by
  have hev : (fun y => Trunc.e y + 1 / 2 * ∑' ij, sR0 ij y) =ᶠ[nhds t] e :=
    Filter.eventually_of_mem (isOpen_dom.mem_nhds ht) fun y hy => (e_eq hy).symm
  exact ((hasDerivAt_Trunc_e (dom_subset_Ioi ht)).add ((hasDerivAt_sR_tsum ht).const_mul (1 / 2))).congr_of_eventuallyEq
    hev.symm

theorem deriv_e_sub {t : ℝ} (ht : t ∈ dom) :
    deriv e t - deriv Trunc.e t = 1 / 2 * ∑' ij, sR1 ij t := by
  rw [(hasDerivAt_e ht).deriv, (hasDerivAt_Trunc_e (dom_subset_Ioi ht)).deriv]
  ring

/-! ### Piece level -/

/-- The error `e - ẽ` and its two derivatives, as explicit piece formulas on the segment `j`. -/
@[expose] noncomputable def Ee0 (j : ℕ) (t : ℝ) : ℝ := 1 / 2 * ∑' ij, rP0 j ij t

@[expose] noncomputable def Ee1 (j : ℕ) (t : ℝ) : ℝ := 1 / 2 * ∑' ij, rP1 j ij t

@[expose] noncomputable def Ee2 (j : ℕ) (t : ℝ) : ℝ := 1 / 2 * ∑' ij, rP2 j ij t

theorem Q_eq_qP {i j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j) :
    Q i t = qP0 i j t ∧ Qs1 i t = qP1 i j t := by
  obtain ⟨h0, h1, h2⟩ := deriv_D_seg (i := i) hj ht
  unfold Q Qs1 qP0 qP1
  rw [h0, h1, h2]
  exact ⟨rfl, rfl⟩

theorem sR_eq_rP {j : ℕ} (hj : j ≤ 5) (ij : ℕ × ℕ) {t : ℝ} (ht : t ∈ seg j) :
    sR0 ij t = rP0 j ij t ∧ sR1 ij t = rP1 j ij t := by
  obtain ⟨a1, b1⟩ := Q_eq_qP (i := ij.1) hj ht
  obtain ⟨a2, b2⟩ := Q_eq_qP (i := ij.2) hj ht
  by_cases h : ij.1 < 39 ∧ ij.2 < 39
  · simp [sR0, sR1, rP0, rP1, h]
  · simp [sR0, sR1, rP0, rP1, tP0, tP1, mul₁, h, a1, b1, a2, b2]

/-- `e - ẽ = Ee0 j` on `seg j ∩ (b/2, 1)`. -/
theorem e_sub_eq {j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j) (htd : t ∈ dom) :
    e t - Trunc.e t = Ee0 j t := by
  rw [e_eq htd]
  unfold Ee0
  rw [add_sub_cancel_left]
  congr 1
  exact tsum_congr fun ij => (sR_eq_rP hj ij ht).1

theorem deriv_e_sub_eq {j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j) (htd : t ∈ dom) :
    deriv e t - deriv Trunc.e t = Ee1 j t := by
  rw [deriv_e_sub htd]
  unfold Ee1
  congr 1
  exact tsum_congr fun ij => (sR_eq_rP hj ij ht).2

/-- The finite block of the derivative of `ẽ` on the piece `j`, and its derivative. -/
@[expose] noncomputable def TT1 (j : ℕ) (t : ℝ) : ℝ :=
  1 / 2 * ∑ i ∈ Finset.range 39, ∑ k ∈ Finset.range 39, tP1 j (i, k) t

@[expose] noncomputable def TT2 (j : ℕ) (t : ℝ) : ℝ :=
  1 / 2 * ∑ i ∈ Finset.range 39, ∑ k ∈ Finset.range 39, tP2 j (i, k) t

theorem sTe1_eq {j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ seg j) : sTe1 t = TT1 j t := by
  unfold sTe1 TT1
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨a1, b1⟩ := Q_eq_qP (i := i) hj ht
  obtain ⟨a2, b2⟩ := Q_eq_qP (i := k) hj ht
  simp only [tP1, mul₁, a1, b1, a2, b2]

theorem hasDerivAt_TT1 (j : ℕ) {x : ℝ} (hx : 0 < x) : HasDerivAt (TT1 j) (TT2 j x) x :=
  (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun k _ => (je_tP j (i, k)).jet.d1 x hx).const_mul (1 / 2)

/-! ### The bound `tail:e-estimate` -/

/-- **`tail:e-estimate`**: `|e - ẽ|_{2,t} ≤ 16 (2·10⁶) 𝔞 + 32 𝔞²` on `seg j ∩ [b, l]`. -/
theorem e_error_bound (hc : FiniteCore) {j : ℕ} (hj : j ≤ 5) {t : ℝ} (hts : t ∈ seg j) (h1 : b ≤ t)
    (h2 : t ≤ l) :
    |Ee0 j t| + |Ee1 j t| + |Ee2 j t| / 2 ≤ 16 * (2 * 10 ^ 6) * aa + 32 * aa ^ 2 := by
  have htS : t ∈ Sg j := ⟨hts, by have := b_pos; linarith, by have := l_lt; linarith⟩
  have hbd := (je_rP_tsum j hj).bd t htS
  have hsh := rest_tsum_sharp hc hj hts h1 h2
  have hc2 := jn_const_mul (1 / 2) (fun x => ∑' ij, rP0 j ij x) (fun x => ∑' ij, rP1 j ij x)
    (fun x => ∑' ij, rP2 j ij x) t
  have ha := aa_nonneg
  have : jn (Ee0 j) (Ee1 j) (Ee2 j) t ≤ 1 / 2 * (2 * 4000000 * (16 / 3 * aa) + (16 / 3 * aa) ^ 2) := by
    have e1 : jn (Ee0 j) (Ee1 j) (Ee2 j) t = |(1 / 2 : ℝ)| * jn (fun x => ∑' ij, rP0 j ij x)
        (fun x => ∑' ij, rP1 j ij x) (fun x => ∑' ij, rP2 j ij x) t := hc2
    rw [e1, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hbd.trans hsh) (by norm_num)
  unfold jn at this
  nlinarith [sq_nonneg aa]

end Tails

end SandierSerfaty

end
