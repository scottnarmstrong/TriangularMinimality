/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropBlocks
public import SandierSerfaty.Tails.PropTrunc

/-!
# `f₀ - f̃₀` (paper `tail:f-estimate`)

`f₀ = f̃₀ + Δf` on `dom` with
`Δf = -2π (ΔS₁ + t² A) - ½ (ΔS₂ + B + C + E)` (`Δf_def`; `A, B, C, E` the blocks of `PropBlocks`), hence a jet
for `f₀` on `dom ⊇ [b, l]` (so `f₀` is `C²` there) and the bound
`|f₀ - f̃₀|_{2,t} ≤ 6·10⁷ 𝔞` (`jn_Δf_le`, `tail:f-estimate`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- `Δf = f₀ - f̃₀` as the sum of the blocks (paper `tail:f-estimate`). -/
@[expose] noncomputable def Δf (t : ℝ) : ℝ :=
  -2 * Real.pi * (dS1 t + t ^ 2 * Ablk t) - 1 / 2 * (dS2 t + Bblk t + Cblk t + Eblk t)

theorem summable_Ablk_term {t : ℝ} (ht : 0 < t) : Summable fun j => 1 / ((kk j : ℝ) + 2) * D (j + 39) t := by
  refine Summable.of_norm_bounded summable_wk fun j => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have hc : |1 / ((kk j : ℝ) + 2)| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one (by positivity)]
    have : (0 : ℝ) ≤ kk j := by positivity
    linarith
  have := (D_bound_tail j ht).1
  calc |1 / ((kk j : ℝ) + 2)| * |D (j + 39) t| ≤ 1 * wk (kk j) :=
        mul_le_mul hc this (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem summable_Bterm (hc : FiniteCore) {t : ℝ} (ht : t ∈ dom) :
    Summable fun j => -2 * D (j + 39) t + 2 * (kk j : ℝ) * D (j + 39) t * Hk B₁ (kk j) t :=
  JB.summable_family (fun j => (jb_Bterm hc j).mono_set dom_subset_Ioi)
    ((summable_wt (by norm_num)).mul_left (5 + 40 * GB)) (fun j t ht => bB_crude j ht.1.le
      (by have := ht.2; linarith)) ht

theorem summable_Rt {t : ℝ} (ht : t ∈ dom) : Summable fun ij : ℕ × ℕ => Rt ij t :=
  JB.summable_family (fun ij => (jb_Rt ij).mono_set dom_subset_Ioi)
    (summable_rest mq_nonneg summable_mq) (fun ij t ht =>
      rest_mono (fun i => by have := jD_nonneg i t; positivity) (qt_le_mq ht) ij) ht

theorem sum_A_eq {t : ℝ} (ht0 : 0 < t) :
    ∑' i, D i t / ((k i : ℝ) + 2) = ∑ i ∈ Finset.range 39, D i t / ((k i : ℝ) + 2) + Ablk t := by
  have sA' : Summable fun j => D (j + 39) t / ((k (j + 39) : ℝ) + 2) := by
    refine (summable_Ablk_term ht0).congr fun j => ?_
    rw [k_tail']; ring
  have sA : Summable fun i => D i t / ((k i : ℝ) + 2) := (summable_nat_add_iff 39).1 sA'
  rw [← sA.sum_add_tsum_nat_add 39]
  congr 1
  unfold Ablk
  refine tsum_congr fun j => ?_
  rw [k_tail']; ring

theorem sum_B_eq (hc : FiniteCore) {t : ℝ} (ht : t ∈ dom) :
    ∑' i, (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t) =
      ∑ i ∈ Finset.range 39, (-2 * D i t + 2 * (k i : ℝ) * D i t * Trunc.H (k i) t) + Cblk t + Bblk t := by
  have ht0 : 0 < t := dom_subset_Ioi ht
  have sB' : Summable fun j => (-2 * D (j + 39) t + 2 * (k (j + 39) : ℝ) * D (j + 39) t * H (k (j + 39)) t) := by
    refine (summable_Bterm hc ht).congr fun j => ?_
    rw [k_tail]; rfl
  have sB : Summable fun i => (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t) :=
    (summable_nat_add_iff 39).1 sB'
  rw [← sB.sum_add_tsum_nat_add 39]
  have e1 : ∑ i ∈ Finset.range 39, (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t) =
      ∑ i ∈ Finset.range 39, (-2 * D i t + 2 * (k i : ℝ) * D i t * Trunc.H (k i) t) + Cblk t := by
    unfold Cblk
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Hk_B₁_eq hc (k i) ht0
    have e : H (k i) t = Trunc.H (k i) t + Hk dU1 (k i) t := this
    rw [e]; ring
  have e2 : ∑' j, (-2 * D (j + 39) t + 2 * (k (j + 39) : ℝ) * D (j + 39) t * H (k (j + 39)) t) = Bblk t := by
    unfold Bblk
    refine tsum_congr fun j => ?_
    rw [k_tail]; rfl
  rw [e1, e2]

/-- The double-sum summand. -/
@[expose] noncomputable def Ft (ij : ℕ × ℕ) (t : ℝ) : ℝ :=
  (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * D ij.1 t * D ij.2 t

theorem Ft_eq (ij : ℕ × ℕ) (t : ℝ) :
    Ft ij t = (if ij.1 < 39 ∧ ij.2 < 39 then Ft ij t else 0) + Rt ij t := by
  unfold Rt Ft; split_ifs <;> simp

theorem sum_E_eq {t : ℝ} (ht : t ∈ dom) :
    ∑' ij : ℕ × ℕ, Ft ij t =
      ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39, Ft (i, j) t + Eblk t := by
  have hb0 : ∀ ij ∉ (Finset.range 39 ×ˢ Finset.range 39),
      (if ij.1 < 39 ∧ ij.2 < 39 then Ft ij t else 0) = 0 := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, not_and] at hij
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hij h1 h2
  have hb : Summable fun ij : ℕ × ℕ => if ij.1 < 39 ∧ ij.2 < 39 then Ft ij t else 0 :=
    summable_of_ne_finset_zero hb0
  have e : (fun ij : ℕ × ℕ => Ft ij t) = fun ij => (if ij.1 < 39 ∧ ij.2 < 39 then Ft ij t else 0) + Rt ij t :=
    funext fun ij => Ft_eq ij t
  rw [e, hb.tsum_add (summable_Rt ht), tsum_eq_sum hb0, Finset.sum_product]
  unfold Eblk
  congr 1

theorem f₀_eq (hc : FiniteCore) {t : ℝ} (ht : t ∈ dom) : f₀ t = Trunc.f₀ t + Δf t := by
  have ht0 : 0 < t := dom_subset_Ioi ht
  have h1 := sum_A_eq ht0
  have h2 := sum_B_eq hc ht
  have h3 := sum_E_eq ht
  have h3' : ∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * D ij.1 t * D ij.2 t =
      ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39,
        (k i : ℝ) * (k j : ℝ) / ((k i : ℝ) + (k j : ℝ)) * D i t * D j t + Eblk t := h3
  have hS1 := S₁_eq ht0
  have hS2 := S₂_eq hc ht0
  unfold f₀ Trunc.f₀ Δf
  simp only [Trunc.modes_succ]
  rw [hS1, hS2, h1, h2, h3']
  ring

/-! ### The bound -/

theorem Wstar_nonneg : 0 ≤ Wstar := by unfold Wstar; linarith [ww_nonneg]

theorem jb_dS1 : JB dom dS1 (fun _ => 3 * Wstar) :=
  JB.of_jet (jet_dS1.mono dom_subset_Ioi dom_subset_Ioi subset_rfl)
    fun _ ht => jn_dS1_le (dom_subset_Ioi ht) ht.2.le

theorem jb_dS2 (hc : FiniteCore) : JB dom dS2 (fun _ => 2 * ((24002 + Wstar) * Wstar)) :=
  JB.of_jet ((jet_dS2 hc).mono dom_subset_Ioi dom_subset_Ioi subset_rfl)
    fun _ ht => jn_dS2_le hc (dom_subset_Ioi ht) ht.2.le

/-- The bound function for `Δf`. -/
@[expose] noncomputable def bΔf (t : ℝ) : ℝ :=
  |(-2 * Real.pi : ℝ)| * (3 * Wstar + (|t| + 1) * (|t| + 1) * (5 / 2 * ww)) +
    |(1 / 2 : ℝ)| * (2 * ((24002 + Wstar) * Wstar) + (∑' j, bB j t) + bC t +
      ∑' ij, rest (fun i => (k i : ℝ) * jD i t) ij)

theorem jb_Δf (hc : FiniteCore) : JB dom Δf bΔf := by
  have hA : JB dom (fun x => x ^ 2 * Ablk x) (fun t => (|t| + 1) * (|t| + 1) * (5 / 2 * ww)) := by
    have := (JB.id (U := dom)).mul (JB.id (U := dom)) |>.mul (jb_Ablk.mono_set dom_subset_Ioi)
    have e : (fun x : ℝ => x ^ 2 * Ablk x) = fun x => x * x * Ablk x := by funext x; ring
    rw [e]; exact this
  have h1 := ((jb_dS1.add hA).const_mul (-2 * Real.pi))
  have h2 := (((jb_dS2 hc).add (jb_Bblk hc)).add (jb_Cblk.mono_set dom_subset_Ioi)).add jb_Eblk
  exact h1.sub (h2.const_mul (1 / 2))

theorem bΔf_le {t : ℝ} (hc : FiniteCore) (h1 : b ≤ t) (h2 : t ≤ l) : bΔf t ≤ 60000000 * aa := by
  have hw := ww_nonneg
  have hW := Wstar_nonneg
  have a1 : ww ≤ aa := ww_le_aa
  have a2 : Wstar ≤ 4 * aa := Wstar_le
  have a0 : aa < 2 / 10 ^ 21 := aa_lt
  have a00 := aa_nonneg
  have hB := bB_tsum_sharp h1 h2
  have hC := bC_sharp hc h1 h2
  have hE := Eblk_tsum_sharp hc h1 h2
  have hGB : GB ≤ 6001 := by unfold GB; linarith
  have ht0 : 0 < t := lt_of_lt_of_le b_pos h1
  have htl : t ≤ 1 := by have := l_lt; linarith
  have ht1 : (|t| + 1) * (|t| + 1) ≤ 4 := by
    rw [abs_of_pos ht0]; nlinarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  unfold bΔf
  rw [abs_of_neg (by nlinarith), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have e1 : (5 + 30 * GB) * aa ≤ 180100 * aa := by
    refine mul_le_mul_of_nonneg_right ?_ a00; linarith
  have e2 : ((24002 + Wstar) * Wstar) ≤ 24003 * (4 * aa) := by
    have : Wstar ≤ 1 := by linarith
    nlinarith
  have e3 : (|t| + 1) * (|t| + 1) * (5 / 2 * ww) ≤ 4 * (5 / 2 * aa) := by
    calc (|t| + 1) * (|t| + 1) * (5 / 2 * ww) ≤ 4 * (5 / 2 * ww) :=
          mul_le_mul_of_nonneg_right ht1 (by positivity)
      _ ≤ 4 * (5 / 2 * aa) := by linarith
  have e4 : 7 * aa ^ 2 ≤ aa := by nlinarith
  nlinarith

theorem exists_jet_Δf (hc : FiniteCore) :
    ∃ F₁ F₂ : ℝ → ℝ, Jet2 dom dom Δf F₁ F₂ ∧ ∀ t ∈ Icc b l, jn Δf F₁ F₂ t ≤ 60000000 * aa := by
  obtain ⟨F₁, F₂, hj, hb⟩ := jb_Δf hc
  exact ⟨F₁, F₂, hj, fun t ht => (hb t (Icc_subset_dom ht)).trans (bΔf_le hc ht.1 ht.2)⟩

/-- **`tail:uniform-error` for `f₀`** (paper `tail:f-estimate`): `f₀` is `C²` on a neighbourhood of `[b, l]` and
`|f₀ - f̃₀|_{2,t} < 6·10⁷ 𝔞` there (in particular, `|f₀ - f̃₀|`, `|f₀' - f̃₀'|`, `½|f₀'' - f̃₀''|` are at most
that). -/
theorem f_error (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc b l) :
    |f₀ t - Trunc.f₀ t| + |deriv f₀ t - deriv Trunc.f₀ t| +
        |deriv (deriv f₀) t - deriv (deriv Trunc.f₀) t| / 2 ≤ 60000000 * aa := by
  obtain ⟨G₁, G₂, hG⟩ := exists_jet_Trunc_f₀ hc
  obtain ⟨F₁, F₂, hF, hb⟩ := exists_jet_Δf hc
  have htd : t ∈ dom := Icc_subset_dom ht
  have hG' : Jet2 dom dom Trunc.f₀ G₁ G₂ := hG.mono dom_subset_Ioi dom_subset_Ioi subset_rfl
  have hS : Jet2 dom dom f₀ (fun x => G₁ x + F₁ x) (fun x => G₂ x + F₂ x) :=
    (hG'.add hF).congr isOpen_dom (fun x hx => (f₀_eq hc hx).symm) (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨d1, d2⟩ := Jet2.deriv_eq isOpen_dom hS htd
  obtain ⟨e1, e2⟩ := Jet2.deriv_eq isOpen_dom hG' htd
  rw [d1, d2, e1, e2, f₀_eq hc htd, add_sub_cancel_left, add_sub_cancel_left, add_sub_cancel_left]
  exact hb t ht

end Tails

end SandierSerfaty

end
