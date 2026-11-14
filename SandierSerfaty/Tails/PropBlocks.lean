/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropH
public import SandierSerfaty.Tails.JetBound
public import SandierSerfaty.Tails.TailSums

/-!
# The `D`-blocks of `f₀ - f̃₀` (paper `tail:f-estimate`)

With `dom = (b/2, 1) ⊇ [b, l]` and `jD i t = |D_i|_{2,t}`, the pieces of `f₀ - f̃₀` other than `ΔS₁, ΔS₂`:

* `Ablk = ∑_{i ≥ 39} D_i/(k_i+2)` (the `t² ∑ D_i/(k_i+2)` term);
* `Bblk = ∑_{i ≥ 39} (-2D_i + 2 k_i D_i H_{k_i})`;
* `Cblk = ∑_{i ≤ 38} 2 k_i D_i ΔH_{k_i}` (paper §6.5, first sum);
* `Eblk = ∑_{(i,j) ∉ [0,38]²} k_i k_j/(k_i+k_j) D_i D_j` (paper §6.5).

Each is a `JB` (jet with pointwise norm bound); the convergence of the series on `dom` uses the crude estimates
(`8 (k+1)` for `H_k`, compactness for the finitely many retained modes), and the quantitative bounds at
`t ∈ [b, l]` use `tail:H-estimate`, `tail:weighted-sum` and the finite-core premise.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The open interval `(b/2, 1) ⊇ [b, l]` on which the jets are built. -/
@[expose] def dom : Set ℝ := Ioo (b / 2) 1

theorem isOpen_dom : IsOpen dom := isOpen_Ioo

theorem isPreconnected_dom : IsPreconnected dom := isPreconnected_Ioo

theorem dom_subset_Ioi : dom ⊆ Ioi 0 := fun t ht => by
  have := b_pos; exact lt_trans (by positivity) ht.1

theorem Icc_subset_dom : Icc b l ⊆ dom := fun t ht =>
  ⟨lt_of_lt_of_le (by have := b_pos; linarith) ht.1, lt_of_le_of_lt ht.2 (by have := l_lt; linarith)⟩

/-- `|D_i|_{2,t}`. -/
@[expose] noncomputable def jD (i : ℕ) (t : ℝ) : ℝ :=
  |D i t| + |deriv (D i) t| + |deriv (deriv (D i)) t| / 2

theorem jD_nonneg (i : ℕ) (t : ℝ) : 0 ≤ jD i t := by unfold jD; positivity

theorem jb_D (i : ℕ) : JB (Ioi 0) (D i) (jD i) :=
  JB.of_jet (jet_D i) fun _t _ => le_of_eq rfl

theorem jD_tail (j : ℕ) {t : ℝ} (ht : 0 < t) : jD (j + 39) t ≤ 5 / 2 * wk (kk j) := by
  obtain ⟨a, b', c⟩ := D_bound_tail j ht
  unfold jD
  linarith

theorem k_tail' (j : ℕ) : ((k (j + 39) : ℕ) : ℝ) = ((kk j : ℕ) : ℝ) := by rw [k_tail]

/-! ### Block A -/

/-- `∑_{i ≥ 39} D_i(t)/(k_i + 2)`. -/
@[expose] noncomputable def Ablk (t : ℝ) : ℝ := ∑' j, 1 / ((kk j : ℝ) + 2) * D (j + 39) t

theorem jb_Ablk : JB (Ioi 0) Ablk (fun _ => 5 / 2 * ww) := by
  have h : ∀ j, JB (Ioi 0) (fun x => 1 / ((kk j : ℝ) + 2) * D (j + 39) x) (fun _ => 5 / 2 * wk (kk j)) := by
    intro j
    refine ((jb_D (j + 39)).const_mul (1 / ((kk j : ℝ) + 2))).mono_bound fun t ht => ?_
    have hc : |1 / ((kk j : ℝ) + 2)| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one (by positivity)]
      have : (0 : ℝ) ≤ kk j := by positivity
      linarith
    have h1 := jD_tail j ht
    have h2 := jD_nonneg (j + 39) t
    calc |1 / ((kk j : ℝ) + 2)| * jD (j + 39) t ≤ 1 * jD (j + 39) t :=
          mul_le_mul_of_nonneg_right hc h2
      _ ≤ _ := by linarith
  have := JB.tsum isOpen_Ioi isPreconnected_Ioi h (u := fun j => 5 / 2 * wk (kk j))
    (summable_wk.mul_left _) fun j t _ => le_rfl
  refine this.mono_bound fun t _ => ?_
  rw [tsum_mul_left]
  exact le_of_eq rfl

/-! ### Block B -/

/-- The sup bound `6000 + ∑ w` for `|B₁|` and `|B₁'|` (paper `tail:H-estimate`, with `ww ≤ W_*`). -/
@[expose] noncomputable def GB : ℝ := 6000 + ww

theorem GB_nonneg : 0 ≤ GB := by unfold GB; have := ww_nonneg; positivity

theorem jb_Hk_B₁ (hc : FiniteCore) (k : ℕ) :
    JB (Ioi 0) (Hk B₁ k) (fun t => (t / ((k : ℝ) + 1) + 5 / 2 + (k : ℝ) / t) * GB) :=
  JB.of_jet (jet_Hk_B₁ hc k) fun _ ht =>
    jn_Hk_le' (nearZero_B₁ hc) k ht (G := GB) (fun _ hr => (abs_B₁_le' hc hr.1).1) (abs_B₁_le' hc ht).2

theorem jb_Hk_dU1 (k : ℕ) :
    JB (Ioi 0) (Hk dU1 k) (fun t => (t / ((k : ℝ) + 1) + 5 / 2 + (k : ℝ) / t) * ww) :=
  JB.of_jet (jet_Hk_dU1 k) fun _ ht =>
    jn_Hk_le' nearZero_dU1 k ht (G := ww) (fun _ hr => (dU_bound hr.1).2.1) (dU_bound ht).2.2

/-- `∑_{i ≥ 39} (-2 D_i + 2 k_i D_i H_{k_i})`. -/
@[expose] noncomputable def Bblk (t : ℝ) : ℝ :=
  ∑' j, (-2 * D (j + 39) t + 2 * (kk j : ℝ) * D (j + 39) t * Hk B₁ (kk j) t)

/-- The bound for the `j`-th term of `Bblk`. -/
@[expose] noncomputable def bB (j : ℕ) (t : ℝ) : ℝ :=
  |(-2 : ℝ)| * (5 / 2 * wk (kk j)) +
    (|2 * (kk j : ℝ)| * (5 / 2 * wk (kk j))) *
      ((t / ((kk j : ℝ) + 1) + 5 / 2 + (kk j : ℝ) / t) * GB)

theorem jb_Bterm (hc : FiniteCore) (j : ℕ) :
    JB (Ioi 0) (fun x => -2 * D (j + 39) x + 2 * (kk j : ℝ) * D (j + 39) x * Hk B₁ (kk j) x) (bB j) := by
  have hD : JB (Ioi 0) (D (j + 39)) (fun _ => 5 / 2 * wk (kk j)) :=
    (jb_D (j + 39)).mono_bound fun t ht => jD_tail j ht
  exact ((hD.const_mul (-2)).add (((hD.const_mul (2 * (kk j : ℝ))).mul (jb_Hk_B₁ hc (kk j)))))

theorem bB_nonneg (j : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ bB j t := by
  unfold bB; have := wk_nonneg (kk j); have := GB_nonneg; positivity

theorem bB_crude (j : ℕ) {t : ℝ} (h1 : b / 2 ≤ t) (h2 : t ≤ 2) :
    bB j t ≤ (5 + 40 * GB) * wt 2 j := by
  have hc := coef_crude (k := kk j) h1 h2
  have hw := wk_nonneg (kk j)
  have hG := GB_nonneg
  have hk : (0 : ℝ) ≤ kk j := by positivity
  unfold bB wt
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (kk j : ℝ)), abs_neg, abs_two]
  have h3 : (t / ((kk j : ℝ) + 1) + 5 / 2 + (kk j : ℝ) / t) * GB ≤ 8 * ((kk j : ℝ) + 1) * GB :=
    mul_le_mul_of_nonneg_right hc hG
  have h4 : 2 * (kk j : ℝ) * (5 / 2 * wk (kk j)) * ((t / ((kk j : ℝ) + 1) + 5 / 2 + (kk j : ℝ) / t) * GB) ≤
      2 * (kk j : ℝ) * (5 / 2 * wk (kk j)) * (8 * ((kk j : ℝ) + 1) * GB) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : 2 * (5 / 2 * wk (kk j)) + 2 * (kk j : ℝ) * (5 / 2 * wk (kk j)) * (8 * ((kk j : ℝ) + 1) * GB) ≤
      (5 + 40 * GB) * (((kk j : ℝ) + 1) ^ 2 * wk (kk j)) := by
    have e1 : 0 ≤ ((kk j : ℝ) + 1) ^ 2 - 1 := by nlinarith
    have e2 : 0 ≤ ((kk j : ℝ) + 1) ^ 2 - (kk j : ℝ) * ((kk j : ℝ) + 1) := by nlinarith
    nlinarith [mul_nonneg hw e1, mul_nonneg (mul_nonneg hw hG) e2]
  linarith

theorem bB_sharp (j : ℕ) {t : ℝ} (h1 : b ≤ t) (h2 : t ≤ l) :
    bB j t ≤ 5 * wk (kk j) + 30 * GB * wt 2 j := by
  have hc := coef_sharp (k := kk j) h1 h2
  have hw := wk_nonneg (kk j)
  have hG := GB_nonneg
  have hk : (0 : ℝ) ≤ kk j := by positivity
  unfold bB wt
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (kk j : ℝ)), abs_neg, abs_two]
  have h3 : (t / ((kk j : ℝ) + 1) + 5 / 2 + (kk j : ℝ) / t) * GB ≤ 6 * ((kk j : ℝ) + 1) * GB :=
    mul_le_mul_of_nonneg_right hc hG
  have h4 : 2 * (kk j : ℝ) * (5 / 2 * wk (kk j)) * ((t / ((kk j : ℝ) + 1) + 5 / 2 + (kk j : ℝ) / t) * GB) ≤
      2 * (kk j : ℝ) * (5 / 2 * wk (kk j)) * (6 * ((kk j : ℝ) + 1) * GB) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e2 : 0 ≤ ((kk j : ℝ) + 1) ^ 2 - (kk j : ℝ) * ((kk j : ℝ) + 1) := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hw hG) e2]

theorem jb_Bblk (hc : FiniteCore) : JB dom Bblk (fun t => ∑' j, bB j t) := by
  have hs : Summable fun j => (5 + 40 * GB) * wt 2 j := (summable_wt (by norm_num)).mul_left _
  exact JB.tsum isOpen_dom isPreconnected_dom (fun j => (jb_Bterm hc j).mono_set dom_subset_Ioi) hs
    fun j t ht => bB_crude j ht.1.le (by have := ht.2; linarith)

theorem bB_tsum_sharp {t : ℝ} (h1 : b ≤ t) (h2 : t ≤ l) : ∑' j, bB j t ≤ (5 + 30 * GB) * aa := by
  have ht : 0 < t := lt_of_lt_of_le b_pos h1
  have hs1 : Summable fun j => (5 + 40 * GB) * wt 2 j := (summable_wt (by norm_num)).mul_left _
  have hsb : Summable fun j => bB j t :=
    Summable.of_nonneg_of_le (fun j => bB_nonneg j ht) (fun j => bB_crude j (by linarith [b_pos]) (by linarith [l_lt]))
      hs1
  have hs2 : Summable fun j => 5 * wk (kk j) + 30 * GB * wt 2 j :=
    (summable_wk.mul_left 5).add ((summable_wt (by norm_num)).mul_left _)
  have h := Summable.tsum_le_tsum (fun j => bB_sharp j h1 h2) hsb hs2
  refine h.trans ?_
  rw [Summable.tsum_add (summable_wk.mul_left 5) ((summable_wt (by norm_num)).mul_left _), tsum_mul_left,
    tsum_mul_left]
  have a1 : ww ≤ aa := ww_le_aa
  have a2 : ∑' j, wt 2 j ≤ aa := tsum_wt_le (by norm_num)
  have hG := GB_nonneg
  have : ∑' j, wk (kk j) = ww := rfl
  rw [this]
  nlinarith

/-! ### Block C -/

/-- `∑_{i ≤ 38} 2 k_i D_i ΔH_{k_i}`. -/
@[expose] noncomputable def Cblk (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 39, 2 * (k i : ℝ) * D i t * Hk dU1 (k i) t

@[expose] noncomputable def bC (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 39, (|2 * (k i : ℝ)| * jD i t) *
    ((t / ((k i : ℝ) + 1) + 5 / 2 + (k i : ℝ) / t) * ww)

theorem jb_Cblk : JB (Ioi 0) Cblk bC :=
  JB.finset_sum _ fun i _ => ((jb_D i).const_mul (2 * (k i : ℝ))).mul (jb_Hk_dU1 (k i))

theorem bC_sharp (hc : FiniteCore) {t : ℝ} (h1 : b ≤ t) (h2 : t ≤ l) : bC t ≤ 12 * ww * 2000000 := by
  have hcore := core_D hc ⟨h1, h2⟩
  have hw := ww_nonneg
  have h : ∀ i ∈ Finset.range 39, (|2 * (k i : ℝ)| * jD i t) *
      ((t / ((k i : ℝ) + 1) + 5 / 2 + (k i : ℝ) / t) * ww) ≤
      12 * ww * (((k i : ℝ) + 1) ^ 3 * jD i t) := by
    intro i _
    have hk : (0 : ℝ) ≤ k i := by positivity
    have c := coef_sharp (k := k i) h1 h2
    have hj := jD_nonneg i t
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (k i : ℝ))]
    have h3 : (t / ((k i : ℝ) + 1) + 5 / 2 + (k i : ℝ) / t) * ww ≤ 6 * ((k i : ℝ) + 1) * ww :=
      mul_le_mul_of_nonneg_right c hw
    calc 2 * (k i : ℝ) * jD i t * ((t / ((k i : ℝ) + 1) + 5 / 2 + (k i : ℝ) / t) * ww)
        ≤ 2 * (k i : ℝ) * jD i t * (6 * ((k i : ℝ) + 1) * ww) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 12 * ww * ((k i : ℝ) * ((k i : ℝ) + 1) * jD i t) := by ring
      _ ≤ 12 * ww * (((k i : ℝ) + 1) ^ 3 * jD i t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ hj
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (k i : ℝ) + 1)
            (by positivity : (0 : ℝ) ≤ (k i : ℝ) ^ 2 + (k i : ℝ) + 1)]
  unfold bC
  refine (Finset.sum_le_sum h).trans ?_
  rw [← Finset.mul_sum]
  have : ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 * jD i t < 2000000 := hcore
  nlinarith

/-! ### Block E -/

theorem continuousOn_jD (i : ℕ) : ContinuousOn (jD i) (Ioi 0) := by
  have h2 := contDiffOn_D i
  have c0 : ContinuousOn (D i) (Ioi 0) := h2.continuousOn
  have h1 : ContDiffOn ℝ 1 (deriv (D i)) (Ioi 0) := h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have c1 : ContinuousOn (deriv (D i)) (Ioi 0) := h1.continuousOn
  have c2 : ContinuousOn (deriv (deriv (D i))) (Ioi 0) :=
    (h1.deriv_of_isOpen (m := 0) isOpen_Ioi (by norm_num)).continuousOn
  unfold jD
  exact ((continuous_abs.comp_continuousOn c0).add (continuous_abs.comp_continuousOn c1)).add
    ((continuous_abs.comp_continuousOn c2).div_const 2)

theorem exists_CD : ∃ C : ℝ, 0 ≤ C ∧ ∀ i < 39, ∀ t ∈ Icc (b / 2) 1, jD i t ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_finite (isCompact_Icc (a := b / 2) (b := 1)) 39 (F := jD)
    (fun i _ => (continuousOn_jD i).mono fun t ht => lt_of_lt_of_le (by have := b_pos; positivity) ht.1)
  exact ⟨C, hC0, fun i hi t ht => (le_abs_self _).trans (hC i hi t ht)⟩

/-- A uniform bound for `|D_i|_{2,t}`, `i ≤ 38`, `t ∈ [b/2, 1]` (convergence only; no quantitative role). -/
@[expose] noncomputable def CD : ℝ := Classical.choose exists_CD

theorem CD_nonneg : 0 ≤ CD := (Classical.choose_spec exists_CD).1

theorem jD_le_CD {i : ℕ} (hi : i < 39) {t : ℝ} (ht : t ∈ Icc (b / 2) 1) : jD i t ≤ CD :=
  (Classical.choose_spec exists_CD).2 i hi t ht

/-- The majorant of `k_i |D_i|_{2,t}`. -/
@[expose] noncomputable def mq (i : ℕ) : ℝ :=
  if i < 39 then (k i : ℝ) * CD else (k i : ℝ) * (5 / 2 * wk (k i))

theorem mq_nonneg (i : ℕ) : 0 ≤ mq i := by
  unfold mq; have := CD_nonneg; have := wk_nonneg (k i); split_ifs <;> positivity

theorem mq_tail (j : ℕ) : mq (j + 39) = (kk j : ℝ) * (5 / 2 * wk (kk j)) := by
  unfold mq
  rw [ite_eq_right (by omega), k_tail]

theorem summable_mq : Summable mq := by
  rw [← summable_nat_add_iff 39]
  have h : Summable fun j => 5 / 2 * wt 1 j := (summable_wt (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun j => mq_nonneg _) (fun j => ?_) h
  rw [mq_tail]
  unfold wt
  have := wk_nonneg (kk j)
  have hk : (0 : ℝ) ≤ kk j := by positivity
  nlinarith

theorem qt_le_mq {t : ℝ} (ht : t ∈ dom) (i : ℕ) : (k i : ℝ) * jD i t ≤ mq i := by
  have ht' : t ∈ Icc (b / 2) 1 := ⟨ht.1.le, ht.2.le⟩
  have hk : (0 : ℝ) ≤ k i := by positivity
  unfold mq
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (jD_le_CD h ht') hk
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 39 := ⟨i - 39, by omega⟩
    have := jD_tail j (dom_subset_Ioi ht)
    rw [k_tail]
    exact mul_le_mul_of_nonneg_left this (by positivity)

theorem rest_mono {q m : ℕ → ℝ} (hq : ∀ i, 0 ≤ q i) (hqm : ∀ i, q i ≤ m i) (ij : ℕ × ℕ) :
    rest q ij ≤ rest m ij := by
  unfold rest
  split_ifs
  · exact le_rfl
  · exact mul_le_mul (hqm _) (hqm _) (hq _) ((hq _).trans (hqm _))

theorem k_ge_six (i : ℕ) : 6 ≤ k i := by
  unfold k; split_ifs <;> omega

/-- The `(i, j)` term of the double sum off the retained block. -/
@[expose] noncomputable def Rt (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0
  else (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * D ij.1 t * D ij.2 t

/-- `∑_{(i,j) ∉ [0,38]²} k_i k_j/(k_i + k_j) D_i D_j`. -/
@[expose] noncomputable def Eblk (t : ℝ) : ℝ := ∑' ij : ℕ × ℕ, Rt ij t

theorem jb_Rt (ij : ℕ × ℕ) : JB (Ioi 0) (Rt ij) (fun t => rest (fun i => (k i : ℝ) * jD i t) ij) := by
  by_cases h : ij.1 < 39 ∧ ij.2 < 39
  · have e : Rt ij = fun _ => 0 := by funext t; simp [Rt, h]
    rw [e]
    exact (JB.const (U := Ioi 0) 0).mono_bound fun t _ => by simp [rest, h]
  · have e : Rt ij = fun t => (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * D ij.1 t * D ij.2 t := by
      funext t; simp [Rt, h]
    rw [e]
    refine (((jb_D ij.1).const_mul _).mul (jb_D ij.2)).mono_bound fun t ht => ?_
    have h1 := jD_nonneg ij.1 t
    have h2 := jD_nonneg ij.2 t
    have hk1 : (6 : ℝ) ≤ k ij.1 := by exact_mod_cast k_ge_six ij.1
    have hk2 : (6 : ℝ) ≤ k ij.2 := by exact_mod_cast k_ge_six ij.2
    have hc : |(k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ))| ≤ (k ij.1 : ℝ) * (k ij.2 : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_self (by positivity) (by linarith)
    simp only [rest, ite_eq_right h]
    calc |(k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ))| * jD ij.1 t * jD ij.2 t
        ≤ ((k ij.1 : ℝ) * (k ij.2 : ℝ)) * jD ij.1 t * jD ij.2 t := by gcongr
      _ = (k ij.1 : ℝ) * jD ij.1 t * ((k ij.2 : ℝ) * jD ij.2 t) := by ring

theorem jb_Eblk : JB dom Eblk (fun t => ∑' ij, rest (fun i => (k i : ℝ) * jD i t) ij) :=
  JB.tsum isOpen_dom isPreconnected_dom (fun ij => (jb_Rt ij).mono_set dom_subset_Ioi)
    (summable_rest mq_nonneg summable_mq) fun ij t ht =>
      rest_mono (fun i => by have := jD_nonneg i t; positivity) (qt_le_mq ht) ij

theorem Eblk_tsum_sharp (hc : FiniteCore) {t : ℝ} (h1 : b ≤ t) (h2 : t ≤ l) :
    ∑' ij, rest (fun i => (k i : ℝ) * jD i t) ij ≤ 10000000 * aa + 7 * aa ^ 2 := by
  have htd : t ∈ dom := Icc_subset_dom ⟨h1, h2⟩
  set q : ℕ → ℝ := fun i => (k i : ℝ) * jD i t with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    have := jD_nonneg i t; show 0 ≤ (k i : ℝ) * jD i t; positivity
  have hqs : Summable q :=
    Summable.of_nonneg_of_le hq0 (fun i => qt_le_mq htd i) summable_mq
  rw [tsum_rest hq0 hqs]
  -- the finite part
  have hA : ∑ i ∈ Finset.range 39, q i ≤ 2000000 := by
    have hcore := core_D hc ⟨h1, h2⟩
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hcore.le
    have hj : jD i t = |D i t| + |deriv (D i) t| + |deriv (deriv (D i)) t| / 2 := rfl
    have hk : (0 : ℝ) ≤ k i := by positivity
    have hj0 := jD_nonneg i t
    show (k i : ℝ) * jD i t ≤ _
    rw [← hj]
    refine mul_le_mul_of_nonneg_right ?_ hj0
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (k i : ℝ) + 1) (by positivity : (0 : ℝ) ≤ (k i : ℝ) ^ 2 + (k i : ℝ) + 1)]
  have hA0 : 0 ≤ ∑ i ∈ Finset.range 39, q i := Finset.sum_nonneg fun i _ => hq0 i
  have hs1 : Summable fun j => 5 / 2 * wt 1 j := (summable_wt (by norm_num)).mul_left _
  have hqt : Summable fun j => q (j + 39) := (summable_nat_add_iff 39).2 hqs
  have hD : ∑' j, q (j + 39) ≤ 5 / 2 * aa := by
    have h := Summable.tsum_le_tsum (f := fun j => q (j + 39)) (g := fun j => 5 / 2 * wt 1 j)
      (fun j => ?_) hqt hs1
    · rw [tsum_mul_left] at h
      have := tsum_wt_le (s := 1) (by norm_num)
      linarith
    · have h3 := jD_tail j (dom_subset_Ioi htd)
      show (k (j + 39) : ℝ) * jD (j + 39) t ≤ _
      rw [k_tail]
      unfold wt
      have := wk_nonneg (kk j)
      have hk : (0 : ℝ) ≤ kk j := by positivity
      calc (kk j : ℝ) * jD (j + 39) t ≤ (kk j : ℝ) * (5 / 2 * wk (kk j)) :=
            mul_le_mul_of_nonneg_left h3 hk
        _ ≤ 5 / 2 * (((kk j : ℝ) + 1) ^ 1 * wk (kk j)) := by nlinarith
  have hD0 : 0 ≤ ∑' j, q (j + 39) := tsum_nonneg fun j => hq0 _
  nlinarith [mul_nonneg hA0 hD0]

end Tails

end SandierSerfaty

end
