/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.JetCalc
public import SandierSerfaty.Calibration.Spline

/-!
# Jet bounds for the cutoffs `S`, `τ` and the continuation polynomials `P`, `Q` (paper §6.2)

* `Squintic3`, and for `0 ≤ y ≤ 1` the bounds `|S| ≤ 1`, `|S'| ≤ 2`, `|S''| ≤ 6`, `|S'''| ≤ 60`
  (paper §6.2; the quintic `S(y) = 10y³ - 15y⁴ + 6y⁵`);
* `BJ_squintic_aff`: the jet bounds `1, 2α, 6α², 60α³` of `r ↦ S(α r + β)` where `α r + β ∈ [0, 1]`;
* `tau_BJ`, `one_sub_tau_BJ`: the cutoff `τ` and `1 - τ` on each segment `seg j`, `j ≤ 5`, have jets bounded by
  `1, 27, 1067, 142223` (paper §6.2);
* `Ppoly3`, `Qpoly3` and the bounds `|P^{(j)}| ≤ 2·10⁵`, `|Q^{(j)}| ≤ 4000` on `[0, h_s]` (paper §6.2);
* `contPolyC_BJ`: the continuation polynomial `v₀ + P(r - R₀) v₁ + Q(r - R₀) v₂` has all jet bounds
  `|v₀| + 2·10⁵ |v₁| + 4000 |v₂|`.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-! ### The quintic -/

/-- `S''' = 60 - 360 y + 360 y²`. -/
@[expose] def Squintic3 (y : ℝ) : ℝ := 60 - 360 * y + 360 * y ^ 2

theorem hasDerivAt_Squintic2 (y : ℝ) : HasDerivAt Squintic2 (Squintic3 y) y := by
  have h := (((hasDerivAt_id y).const_mul 60).sub ((hasDerivAt_pow 2 y).const_mul 180)).add
    ((hasDerivAt_pow 3 y).const_mul 120)
  have e : Squintic2 = fun y => 60 * id y - 180 * y ^ 2 + 120 * y ^ 3 := by
    funext y; simp [Squintic2]
  rw [e]
  refine h.congr_deriv ?_
  unfold Squintic3; simp; ring

theorem jet3_Squintic : Jet3 univ Squintic Squintic1 Squintic2 Squintic3 :=
  ⟨fun x _ => hasDerivAt_Squintic x, fun x _ => hasDerivAt_Squintic1 x,
    fun x _ => hasDerivAt_Squintic2 x⟩

theorem abs_Squintic_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |Squintic y| ≤ 1 := by
  rw [abs_le]
  unfold Squintic
  constructor
  · nlinarith [mul_nonneg (pow_nonneg h0 3) (sq_nonneg (y - 5 / 4)), pow_nonneg h0 3]
  · nlinarith [mul_nonneg (pow_nonneg (sub_nonneg.2 h1) 3) (by positivity : (0 : ℝ) ≤ 1 + 3 * y + 6 * y ^ 2)]

theorem abs_Squintic1_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |Squintic1 y| ≤ 2 := by
  rw [abs_le]
  unfold Squintic1
  have : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have h2 : 0 ≤ y * (1 - y) := mul_nonneg h0 (sub_nonneg.2 h1)
  have h3 : (y * (1 - y)) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ h2 this 2
  constructor <;> nlinarith

theorem abs_Squintic2_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |Squintic2 y| ≤ 6 := by
  rw [abs_le]
  unfold Squintic2
  have a1 : 0 ≤ y + 8 / 100 := by linarith
  have a2 : 0 ≤ (1 - y) + 8 / 100 := by linarith
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (y - 79 / 100)) a1]
  · nlinarith [mul_nonneg (sq_nonneg ((1 - y) - 79 / 100)) a2]

theorem abs_Squintic3_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |Squintic3 y| ≤ 60 := by
  rw [abs_le]
  unfold Squintic3
  constructor <;> nlinarith [sq_nonneg (y - 1 / 2), mul_nonneg h0 (sub_nonneg.2 h1)]

/-- The jets of the quintic `S` are bounded by `1, 2, 6, 60` on `[0, 1]`. -/
theorem BJ_squintic : BJ univ (Icc 0 1) Squintic 1 2 6 60 :=
  ⟨_, _, _, jet3_Squintic, fun _ hy => ⟨abs_Squintic_le hy.1 hy.2, abs_Squintic1_le hy.1 hy.2,
    abs_Squintic2_le hy.1 hy.2, abs_Squintic3_le hy.1 hy.2⟩⟩

/-- The affine map `r ↦ α r + β` has the jet `(α, 0, 0)`. -/
theorem BJ_affine (α β : ℝ) (U s : Set ℝ) {W₀ : ℝ} (hs : ∀ x ∈ s, |α * x + β| ≤ W₀) :
    BJ U s (fun r : ℝ => α * r + β) W₀ |α| 0 0 := by
  refine ⟨fun _ => α, fun _ => 0, fun _ => 0, ⟨fun x _ => ?_, fun x _ => hasDerivAt_const x _,
    fun x _ => hasDerivAt_const x _⟩, fun x hx => ⟨by simpa using hs x hx, by simp, by simp, by simp⟩⟩
  simpa using ((hasDerivAt_id x).const_mul α).add_const β

/-- **Jets of `S(α r + β)`** (paper §6.2): bounds `1, 2α, 6α², 60α³` where
`α r + β ∈ [0, 1]`. -/
theorem BJ_squintic_aff {α β : ℝ} (hα : 0 ≤ α) (U s : Set ℝ) (hs : ∀ r ∈ s, 0 ≤ α * r + β ∧ α * r + β ≤ 1) :
    BJ U s (fun r : ℝ => Squintic (α * r + β)) 1 (2 * α) (6 * α ^ 2) (60 * α ^ 3) := by
  have hw : BJ U s (fun r : ℝ => α * r + β) 1 α 0 0 := by
    have := BJ_affine α β U s (W₀ := 1) (fun x hx => by
      rw [abs_le]; constructor <;> linarith [(hs x hx).1, (hs x hx).2])
    rwa [abs_of_nonneg hα] at this
  have h := BJ.comp BJ_squintic hw (fun x hx => ⟨(hs x hx).1, (hs x hx).2⟩) (by norm_num) (by norm_num)
    (by norm_num) hα le_rfl
  refine h.mono le_rfl (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))

/-- `1 - S(α r + β)` has the same bounds. -/
theorem BJ_one_sub_squintic_aff {α β : ℝ} (hα : 0 ≤ α) (U s : Set ℝ)
    (hs : ∀ r ∈ s, 0 ≤ α * r + β ∧ α * r + β ≤ 1) :
    BJ U s (fun r : ℝ => 1 - Squintic (α * r + β)) 1 (2 * α) (6 * α ^ 2) (60 * α ^ 3) := by
  refine (BJ_squintic_aff hα U s hs).one_sub 1 (fun x hx => ?_)
  have h0 := abs_Squintic_le (hs x hx).1 (hs x hx).2
  have : 0 ≤ Squintic (α * x + β) := by
    unfold Squintic
    have h0' := (hs x hx).1; have h1' := (hs x hx).2
    nlinarith [mul_nonneg (pow_nonneg h0' 3) (sq_nonneg (α * x + β - 5 / 4)), pow_nonneg h0' 3]
  rw [abs_le] at h0 ⊢
  constructor <;> linarith [h0.2]

/-! ### The cutoff `τ` and `1 - τ` on the segments -/

theorem tau_BJ {j : ℕ} (hj : j ≤ 5) : BJ univ (seg j) (Piece.tau j) 1 27 1067 142223 := by
  have hsp := hs_pos
  have hz : BJ univ (seg j) (fun _ : ℝ => (0 : ℝ)) 0 0 0 0 := by
    simpa using BJ.const (0 : ℝ) univ (seg j)
  have hsq : ∀ {j : ℕ}, 4 ≤ j → j ≤ 5 → BJ univ (seg j) (Piece.tau j) 1 27 1067 142223 := by
    intro j h4 h5
    have hseg : ∀ r ∈ seg j, 0 ≤ (1 / hs) * r + (-(R₀ + 1 / 1000) / hs) ∧
        (1 / hs) * r + (-(R₀ + 1 / 1000) / hs) ≤ 1 := by
      intro r hr
      have e : (1 / hs) * r + (-(R₀ + 1 / 1000) / hs) = (r - R₀ - 1 / 1000) / hs := by ring
      rw [e]
      have hl := l_eq
      have hr' : R₀ + 1 / 1000 ≤ r ∧ r ≤ l := by
        interval_cases j
        · exact ⟨hr.1, by have := hr.2; have := R₀_add_hs_lt_l; linarith⟩
        · exact ⟨by have := hr.1; have := R₀_add_thousandth_lt_R₀_add_hs; linarith, hr.2⟩
      constructor
      · exact div_nonneg (by linarith [hr'.1]) hsp.le
      · rw [div_le_one hsp]; linarith [hr'.2]
    have h := BJ_squintic_aff (α := 1 / hs) (β := -(R₀ + 1 / 1000) / hs) (by positivity) univ (seg j) hseg
    have hnum : 2 * (1 / hs) ≤ 27 ∧ 6 * (1 / hs) ^ 2 ≤ 1067 ∧ 60 * (1 / hs) ^ 3 ≤ 142223 := by
      unfold hs; norm_num
    refine (h.mono le_rfl hnum.1 hnum.2.1 hnum.2.2).congr isOpen_univ (subset_univ _) ?_
    intro r _
    interval_cases j <;> simp only [Piece.tau] <;> congr 1 <;> ring
  by_cases h4 : 4 ≤ j
  · exact hsq h4 hj
  · have : Piece.tau j = fun _ : ℝ => (0 : ℝ) := by
      funext r; interval_cases j <;> simp [Piece.tau]
    rw [this]
    exact hz.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem one_sub_tau_BJ {j : ℕ} (hj : j ≤ 5) :
    BJ univ (seg j) (fun r => 1 - Piece.tau j r) 1 27 1067 142223 := by
  have hsp := hs_pos
  by_cases h4 : 4 ≤ j
  · have hseg : ∀ r ∈ seg j, 0 ≤ (1 / hs) * r + (-(R₀ + 1 / 1000) / hs) ∧
        (1 / hs) * r + (-(R₀ + 1 / 1000) / hs) ≤ 1 := by
      intro r hr
      have e : (1 / hs) * r + (-(R₀ + 1 / 1000) / hs) = (r - R₀ - 1 / 1000) / hs := by ring
      rw [e]
      have hl := l_eq
      have hr' : R₀ + 1 / 1000 ≤ r ∧ r ≤ l := by
        interval_cases j
        · exact ⟨hr.1, by have := hr.2; have := R₀_add_hs_lt_l; linarith⟩
        · exact ⟨by have := hr.1; have := R₀_add_thousandth_lt_R₀_add_hs; linarith, hr.2⟩
      constructor
      · exact div_nonneg (by linarith [hr'.1]) hsp.le
      · rw [div_le_one hsp]; linarith [hr'.2]
    have h := BJ_one_sub_squintic_aff (α := 1 / hs) (β := -(R₀ + 1 / 1000) / hs) (by positivity) univ
      (seg j) hseg
    have hnum : 2 * (1 / hs) ≤ 27 ∧ 6 * (1 / hs) ^ 2 ≤ 1067 ∧ 60 * (1 / hs) ^ 3 ≤ 142223 := by
      unfold hs; norm_num
    refine (h.mono le_rfl hnum.1 hnum.2.1 hnum.2.2).congr isOpen_univ (subset_univ _) ?_
    intro r _
    interval_cases j <;> simp only [Piece.tau] <;> congr 2 <;> ring
  · have : (fun r => 1 - Piece.tau j r) = fun _ : ℝ => (1 : ℝ) := by
      funext r; interval_cases j <;> simp [Piece.tau]
    rw [this]
    have := BJ.const (1 : ℝ) univ (seg j)
    exact this.mono (by simp) (by norm_num) (by norm_num) (by norm_num)

/-! ### The continuation polynomials `P`, `Q` -/

/-- `P''' = -36/h_s² + 192 z/h_s³ - 180 z²/h_s⁴`. -/
@[expose] noncomputable def Ppoly3 (z : ℝ) : ℝ := -36 / hs ^ 2 + 192 * z / hs ^ 3 - 180 * z ^ 2 / hs ^ 4

/-- `Q''' = -9/h_s + 36 z/h_s² - 30 z²/h_s³`. -/
@[expose] noncomputable def Qpoly3 (z : ℝ) : ℝ := -9 / hs + 36 * z / hs ^ 2 - 30 * z ^ 2 / hs ^ 3

theorem hasDerivAt_Ppoly2 (z : ℝ) : HasDerivAt Ppoly2 (Ppoly3 z) z := by
  have h := (((hasDerivAt_id z).const_mul 36).div_const (hs ^ 2)).neg.add
    ((((hasDerivAt_pow 2 z).const_mul 96).div_const (hs ^ 3)).sub
      (((hasDerivAt_pow 3 z).const_mul 60).div_const (hs ^ 4)))
  have e : Ppoly2 = fun z => -(36 * id z / hs ^ 2) +
      (96 * z ^ 2 / hs ^ 3 - 60 * z ^ 3 / hs ^ 4) := by
    funext z; simp [Ppoly2]; ring
  rw [e]
  refine h.congr_deriv ?_
  unfold Ppoly3; simp; ring

theorem hasDerivAt_Qpoly2 (z : ℝ) : HasDerivAt Qpoly2 (Qpoly3 z) z := by
  have h := (((hasDerivAt_id z).const_mul 9).div_const hs).neg.add
    ((((hasDerivAt_pow 2 z).const_mul 18).div_const (hs ^ 2)).sub
      (((hasDerivAt_pow 3 z).const_mul 10).div_const (hs ^ 3)))
  have e : Qpoly2 = fun z => 1 + (-(9 * id z / hs) +
      (18 * z ^ 2 / hs ^ 2 - 10 * z ^ 3 / hs ^ 3)) := by
    funext z; simp [Qpoly2]; ring
  rw [e]
  refine (h.const_add 1).congr_deriv ?_
  unfold Qpoly3; simp; ring

theorem jet3_Ppoly : Jet3 univ Ppoly Ppoly1 Ppoly2 Ppoly3 :=
  ⟨fun x _ => hasDerivAt_Ppoly x, fun x _ => hasDerivAt_Ppoly1 x, fun x _ => hasDerivAt_Ppoly2 x⟩

theorem jet3_Qpoly : Jet3 univ Qpoly Qpoly1 Qpoly2 Qpoly3 :=
  ⟨fun x _ => hasDerivAt_Qpoly x, fun x _ => hasDerivAt_Qpoly1 x, fun x _ => hasDerivAt_Qpoly2 x⟩

/-- The powers of `z ∈ [0, h_s]` are between `0` and the powers of `h_s = 3/40`. -/
private theorem pow_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 3 / 40) (n : ℕ) :
    0 ≤ z ^ n ∧ z ^ n ≤ (3 / 40 : ℝ) ^ n :=
  ⟨pow_nonneg h0 n, pow_le_pow_left₀ h0 h1 n⟩

private theorem abs_le_of_pm {x B : ℝ} (h1 : -B ≤ x) (h2 : x ≤ B) : |x| ≤ B := abs_le.2 ⟨h1, h2⟩

theorem abs_P_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Ppoly z| ≤ 200000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  obtain ⟨a3, b3⟩ := pow_bounds h0 h1 3
  obtain ⟨a4, b4⟩ := pow_bounds h0 h1 4
  obtain ⟨a5, b5⟩ := pow_bounds h0 h1 5
  unfold Ppoly hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_P1_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Ppoly1 z| ≤ 200000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  obtain ⟨a3, b3⟩ := pow_bounds h0 h1 3
  obtain ⟨a4, b4⟩ := pow_bounds h0 h1 4
  unfold Ppoly1 hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_P2_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Ppoly2 z| ≤ 200000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  obtain ⟨a3, b3⟩ := pow_bounds h0 h1 3
  unfold Ppoly2 hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_P3_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Ppoly3 z| ≤ 200000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  unfold Ppoly3 hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_Q_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Qpoly z| ≤ 4000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  obtain ⟨a3, b3⟩ := pow_bounds h0 h1 3
  obtain ⟨a4, b4⟩ := pow_bounds h0 h1 4
  obtain ⟨a5, b5⟩ := pow_bounds h0 h1 5
  unfold Qpoly hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_Q1_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Qpoly1 z| ≤ 4000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  obtain ⟨a3, b3⟩ := pow_bounds h0 h1 3
  obtain ⟨a4, b4⟩ := pow_bounds h0 h1 4
  unfold Qpoly1 hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_Q2_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Qpoly2 z| ≤ 4000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  obtain ⟨a3, b3⟩ := pow_bounds h0 h1 3
  unfold Qpoly2 hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem abs_Q3_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ hs) : |Qpoly3 z| ≤ 4000 := by
  unfold hs at h1
  obtain ⟨a2, b2⟩ := pow_bounds h0 h1 2
  unfold Qpoly3 hs
  apply abs_le_of_pm <;> norm_num at * <;> linarith

theorem BJ_Ppoly : BJ univ (Icc 0 hs) Ppoly 200000 200000 200000 200000 :=
  ⟨_, _, _, jet3_Ppoly, fun _ hz => ⟨abs_P_le hz.1 hz.2, abs_P1_le hz.1 hz.2, abs_P2_le hz.1 hz.2,
    abs_P3_le hz.1 hz.2⟩⟩

theorem BJ_Qpoly : BJ univ (Icc 0 hs) Qpoly 4000 4000 4000 4000 :=
  ⟨_, _, _, jet3_Qpoly, fun _ hz => ⟨abs_Q_le hz.1 hz.2, abs_Q1_le hz.1 hz.2, abs_Q2_le hz.1 hz.2,
    abs_Q3_le hz.1 hz.2⟩⟩

/-- The shift `r ↦ r - R₀` on `[R₀, R₀ + h_s]` has the jet `(1, 0, 0)`. -/
theorem BJ_shift (U : Set ℝ) {s : Set ℝ} (hs' : s ⊆ Icc R₀ (R₀ + hs)) :
    BJ U s (fun r : ℝ => r - R₀) 1 1 0 0 := by
  have h := BJ_affine 1 (-R₀) U s (W₀ := 1) (fun x hx => by
    have h1 := hs' hx
    have h2 := hs_pos
    have h3 : hs ≤ 1 := by unfold hs; norm_num
    rw [abs_le]; constructor <;> simp only [one_mul] <;> linarith [h1.1, h1.2])
  have e : (fun r : ℝ => r - R₀) = fun r => 1 * r + (-R₀) := by funext r; ring
  rw [e]
  simpa using h

/-- **The continuation polynomial** `v₀ + P(r - R₀) v₁ + Q(r - R₀) v₂` on `[R₀, R₀ + h_s]` has all jet bounds
`|v₀| + 2·10⁵ |v₁| + 4000 |v₂|` (paper §6.2). -/
theorem BJ_contPolyC (v₀ v₁ v₂ : ℝ) (U : Set ℝ) {s : Set ℝ} (hs' : s ⊆ Icc R₀ (R₀ + hs)) :
    BJ U s (contPolyC v₀ v₁ v₂) (|v₀| + 200000 * |v₁| + 4000 * |v₂|)
      (|v₀| + 200000 * |v₁| + 4000 * |v₂|) (|v₀| + 200000 * |v₁| + 4000 * |v₂|)
      (|v₀| + 200000 * |v₁| + 4000 * |v₂|) := by
  have hmaps : ∀ x ∈ s, x - R₀ ∈ Icc 0 hs := fun x hx => by
    have := hs' hx
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hP := (BJ.comp BJ_Ppoly (BJ_shift U hs') hmaps (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).const_mul v₁
  have hQ := (BJ.comp BJ_Qpoly (BJ_shift U hs') hmaps (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).const_mul v₂
  have h := ((BJ.const v₀ U s).add hP).add hQ
  have e : contPolyC v₀ v₁ v₂ =
      fun x => ((fun _ : ℝ => v₀) x + v₁ * Ppoly (x - R₀)) + v₂ * Qpoly (x - R₀) := by
    funext x; simp only [contPolyC]; ring
  rw [e]
  have a0 := abs_nonneg v₀
  have a1 := abs_nonneg v₁
  have a2 := abs_nonneg v₂
  simp only [Real.norm_eq_abs] at h
  refine h.mono ?_ ?_ ?_ ?_ <;> nlinarith

end Tails

end SandierSerfaty

end
