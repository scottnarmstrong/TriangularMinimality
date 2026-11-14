/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenPoints

/-!
# The energy of the flux cells (screening note, Lemma 4.19(b),(c))

The screening note, Lemma 4.19(b),(c) (`lem:flux`) and the count bound
`N₂ = ∫ n²` of Lemma 4.12(b), for `A : Asm` with `A.Good D` under `D.Hyp`:

* `Data.volume_band_le`: a depth band `{a ≤ δ ≤ b}` has area `≤ 4(b - a)t` (four strips);
* `Hyp.lintegral_nD_sq_le_N2b`: `N₂ = ∫ n² ≤ N2b = 62((9π/4)m)² t + (81/32) S_d`;
* `Good.sum_top_le`: **Lemma 4.19(c)**, `Ĝ = ∑_k ∫_{T_k} g̃² ≤ Gb`, with
  `Gb = 864π²m² t + 7776 N2b + 6 S_d + 256π²/ℓc` (from `g̃² ≤ 6(2πm)² + 7776 n² + 6·1_Ā|Φ|²`
  plus the carries, the tops having total area `36L ≤ 36t`);
* `Good.lintegral_Vflux_le`: **Lemma 4.19(b)**, `∫ |∑_k V_k|² ≤ 504 ℓc Gb` (the flux cells overlap
  in null sets).
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

/-- For sets with null pairwise intersections, `∑_i ∫_{S_i} h ≤ ∫ h`. -/
theorem sum_setLIntegral_le_of_null {ι : Type*} (s : Finset ι) (S : ι → Set ℂ)
    (hS : ∀ i ∈ s, MeasurableSet (S i)) (hnull : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → volume (S i ∩ S j) = 0)
    (h : ℂ → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ x in S i, h x ≤ ∫⁻ x, h x := by
  rw [← lintegral_biUnion_finset₀ (fun i hi j hj hij => hnull i hi j hj hij)
    (fun i hi => (hS i hi).nullMeasurableSet)]
  exact setLIntegral_le_lintegral _ _

namespace Scr

open Pinwheel

/-- `N2b = 62((9π/4)m)² t + (81/32) S_d`, the bound for `∫ n²`. -/
@[expose] noncomputable def N2b (m t Sd : ℝ) : ℝ := 2 * (9 * π / 4 * m) ^ 2 * (31 * t) + 81 / 32 * Sd

/-- `Gb = 864π²m² t + 7776 N2b + 6 S_d + 256π²/ℓc`, the bound for `Ĝ`. -/
@[expose] noncomputable def Gb (m t ℓ Sd : ℝ) : ℝ :=
  864 * π ^ 2 * m ^ 2 * t + 7776 * N2b m t Sd + 6 * Sd + 256 * π ^ 2 / ℓ

namespace Data

variable {D : Data}

/-- A depth band `{a ≤ δ ≤ b}` (`0 ≤ a ≤ b`) has area at most `4(b - a)t`. -/
theorem volume_band_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ D.t) :
    volume {x | a ≤ D.dep x ∧ D.dep x ≤ b} ≤ ENNReal.ofReal (4 * (b - a) * D.t) := by
  set c := D.c
  set t := D.t
  set J := Icc (c.im - t / 2) (c.im + t / 2)
  set I := Icc (c.re - t / 2) (c.re + t / 2)
  have hsub : {x | a ≤ D.dep x ∧ D.dep x ≤ b} ⊆
      (Icc (c.re + (t / 2 - b)) (c.re + (t / 2 - a)) ×ℂ J ∪
        Icc (c.re - (t / 2 - a)) (c.re - (t / 2 - b)) ×ℂ J) ∪
      (I ×ℂ Icc (c.im + (t / 2 - b)) (c.im + (t / 2 - a)) ∪
        I ×ℂ Icc (c.im - (t / 2 - a)) (c.im - (t / 2 - b))) := by
    intro x hx
    simp only [mem_ofPred_eq, dep, sqDepth] at hx
    set r := (x - c).re
    set s := (x - c).im
    have hr : (x - c).re = x.re - c.re := Complex.sub_re _ _
    have hs : (x - c).im = x.im - c.im := Complex.sub_im _ _
    have hM1 : max |r| |s| ≤ t / 2 - a := by linarith [hx.1]
    have hM2 : t / 2 - b ≤ max |r| |s| := by linarith [hx.2]
    have hr' := abs_le.1 ((le_max_left _ _).trans hM1)
    have hs' := abs_le.1 ((le_max_right _ _).trans hM1)
    simp only [mem_union, Complex.mem_reProdIm, mem_Icc, I, J]
    rcases max_choice |r| |s| with hm | hm <;> rw [hm] at hM2
    · rcases le_or_gt 0 r with h0 | h0
      · rw [abs_of_nonneg h0] at hM2
        left; left
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · rw [abs_of_neg h0] at hM2
        left; right
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rcases le_or_gt 0 s with h0 | h0
      · rw [abs_of_nonneg h0] at hM2
        right; left
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      · rw [abs_of_neg h0] at hM2
        right; right
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) (measure_union_le _ _)).trans (le_of_eq ?_)
  simp only [Screening.volume_reProdIm, Real.volume_Icc, I, J]
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add (by nlinarith) (by nlinarith), ← ENNReal.ofReal_add (by nlinarith) (by nlinarith),
    ← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
  congr 1; ring

namespace Hyp

variable (h : D.Hyp)
include h

/-- **`N₂ = ∫ n² ≤ N2b`** (replaces Lemma 4.12(b)). -/
theorem lintegral_nD_sq_le_N2b :
    ∫⁻ x, ENNReal.ofReal (D.nD x ^ 2) ≤ ENNReal.ofReal (N2b D.m D.t D.Sd) := by
  set B := {x | D.d - 3 / 2 ≤ D.dep x ∧ D.dep x ≤ D.d + 25 / 4}
  have hsupp : Function.support (fun x => ENNReal.ofReal (D.nD x ^ 2)) ⊆ B := by
    intro x hx
    have hn : D.nD x ≠ 0 := fun h0 => hx (by simp [h0])
    have := h.dep_mem_of_nD_ne_zero hn
    exact ⟨this.1.le, this.2.le⟩
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have ht := h.t_pos
  have hB : volume B ≤ ENNReal.ofReal (31 * D.t) := by
    refine (volume_band_le (by linarith [h.d_pos]) (by linarith) ht.le).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))
  have hS := h.Sd_nonneg
  calc ∫⁻ x in B, ENNReal.ofReal (D.nD x ^ 2)
      ≤ ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) * volume B + ENNReal.ofReal (81 / 32 * D.Sd) :=
        h.lintegral_nD_sq_le B
    _ ≤ ENNReal.ofReal (2 * (9 * π / 4 * D.m) ^ 2) * ENNReal.ofReal (31 * D.t) +
          ENNReal.ofReal (81 / 32 * D.Sd) := by gcongr
    _ = _ := by
        rw [N2b, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]

end Hyp

end Data

namespace Asm

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

/-- The tops of the columns of `R_j` have total area `9L`. -/
theorem sum_volume_top (j : Fin 4) :
    ∑ k ∈ Finset.range (A.cut.K j), volume (A.cut.top D.c D.t D.d j k) =
      ENNReal.ofReal (9 * side D.t D.d) := by
  have hP := hA.part j
  have hw : ∀ k ∈ Finset.range (A.cut.K j), 0 ≤ A.cut.u j (k + 1) - A.cut.u j k := fun k hk =>
    sub_nonneg.2 (hP.mono h.ℓ_pos.le (Nat.le_succ k) (Finset.mem_range.1 hk))
  calc ∑ k ∈ Finset.range (A.cut.K j), volume (A.cut.top D.c D.t D.d j k)
      = ∑ k ∈ Finset.range (A.cut.K j), ENNReal.ofReal (9 * (A.cut.u j (k + 1) - A.cut.u j k)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [ColumnCut.top, Rect.volume_box_Icc, ← ENNReal.ofReal_mul (hw k hk)]
        congr 1; ring
    _ = ENNReal.ofReal (∑ k ∈ Finset.range (A.cut.K j), 9 * (A.cut.u j (k + 1) - A.cut.u j k)) :=
        (ENNReal.ofReal_sum_of_nonneg fun k hk => by linarith [hw k hk]).symm
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub, hP.last, hP.zero, sub_zero]

omit hA in
theorem top_subset_col (jk : Fin 4 × ℕ) :
    A.cut.top D.c D.t D.d jk.1 jk.2 ⊆ A.col D jk :=
  Rect.box_mono subset_rfl (Icc_subset_Icc (by linarith [h.d_pos]) le_rfl)

omit hA in
/-- The pointwise bound `g̃² ≤ 6(2πm)² + 7776 n² + 6 (1_Ā|Φ|)² + 8 ∑ κ_i² (1_{A_i} + 1_{A'_i})`. -/
theorem src_sq_le (x : ℂ) :
    A.cut.src D.c D.t D.d D.g x ^ 2 ≤ 6 * (2 * π * D.m) ^ 2 + 7776 * D.nD x ^ 2 +
      6 * (D.Abar.indicator (fun y => ‖D.Φ y‖) x) ^ 2 +
      8 * ∑ i : Fin 4, (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 *
        ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x +
          (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x) := by
  set I := D.Abar.indicator (fun y => ‖D.Φ y‖) x
  have hI : 0 ≤ I := D.Abar.indicator_nonneg (fun y _ => norm_nonneg (D.Φ y)) x
  have hn := Data.nD_nonneg (D := D) x
  have hm := h.m_pos
  have hg := h.abs_g_le x
  have hg2 : D.g x ^ 2 ≤ 3 * ((2 * π * D.m) ^ 2 + 1296 * D.nD x ^ 2 + I ^ 2) := by
    have h0 : 0 ≤ 2 * π * D.m := by positivity
    have : D.g x ^ 2 ≤ (2 * π * D.m + 36 * D.nD x + I) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hg 2
    linarith [sq_nonneg (2 * π * D.m - 36 * D.nD x), sq_nonneg (2 * π * D.m - I),
      sq_nonneg (36 * D.nD x - I)]
  set y : Fin 4 → ℝ := fun i => 2 * π * A.cut.θ i / A.cut.lastWidth i *
    ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x -
      (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x)
  have hsrc : A.cut.src D.c D.t D.d D.g x = D.g x - ∑ i, y i := rfl
  have hy : ∀ i, y i ^ 2 ≤ (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 *
      ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x +
        (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x) := by
    intro i
    simp only [y, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    by_cases h1 : x ∈ carryA D.c D.t D.d i (A.cut.lastWidth i) <;>
      by_cases h2 : x ∈ carryA' D.c D.t D.d i (A.cut.lastWidth i) <;> simp [h1, h2]
  have hsum : (∑ i, y i) ^ 2 ≤ 4 * ∑ i, y i ^ 2 := by
    simp only [Fin.sum_univ_four]
    linarith [sq_nonneg (y 0 - y 1), sq_nonneg (y 0 - y 2), sq_nonneg (y 0 - y 3),
      sq_nonneg (y 1 - y 2), sq_nonneg (y 1 - y 3), sq_nonneg (y 2 - y 3)]
  have hsy : ∑ i, y i ^ 2 ≤ ∑ i : Fin 4, (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 *
      ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x +
        (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x) :=
    Finset.sum_le_sum fun i _ => hy i
  rw [hsrc]
  linarith [sq_nonneg (D.g x + ∑ i, y i)]

omit h hA in
theorem integrable_carryInd (i : Fin 4) :
    Integrable fun x => (carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ) x +
      (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x := by
  have hA1 : Integrable ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff measurableSet_carryA).2
      (integrableOn_const (by rw [volume_carryA]; exact ENNReal.ofReal_ne_top))
  have hA2 : Integrable ((carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff measurableSet_carryA').2
      (integrableOn_const (by rw [volume_carryA']; exact ENNReal.ofReal_ne_top))
  exact hA1.add hA2

/-- `∫ ∑ κ_i² (1_{A_i} + 1_{A'_i}) ≤ 32π²/ℓc`. -/
theorem integral_carry_sq_le :
    ∫ x, ∑ i : Fin 4, (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 *
        ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ) x +
          (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x) ≤ 32 * π ^ 2 / D.ℓ := by
  rw [integral_finsetSum _ fun i _ => (Good.integrable_carryInd i).const_mul _]
  have hℓ := h.ℓ_pos
  have hπ := Real.pi_pos
  have hterm : ∀ i : Fin 4, ∫ x, (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 *
      ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ) x +
        (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x) ≤ 8 * π ^ 2 / D.ℓ := by
    intro i
    have hw := hA.lastWidth_mem i
    have hw0 : 0 < A.cut.lastWidth i := hℓ.trans_le hw.1
    have hθ := hA.isCut.θ_mem i
    have hA1 : Integrable ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ)) :=
      (integrable_indicator_iff measurableSet_carryA).2
        (integrableOn_const (by rw [volume_carryA]; exact ENNReal.ofReal_ne_top))
    have hA2 : Integrable ((carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ)) :=
      (integrable_indicator_iff measurableSet_carryA').2
        (integrableOn_const (by rw [volume_carryA']; exact ENNReal.ofReal_ne_top))
    rw [integral_const_mul, integral_add hA1 hA2,
      integral_indicator_one measurableSet_carryA, integral_indicator_one measurableSet_carryA',
      measureReal_def, measureReal_def, volume_carryA, volume_carryA',
      ENNReal.toReal_ofReal hw0.le]
    have hθ2 : A.cut.θ i ^ 2 ≤ 1 := by nlinarith [hθ.1, hθ.2]
    calc (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 * (A.cut.lastWidth i + A.cut.lastWidth i)
        = 8 * π ^ 2 * A.cut.θ i ^ 2 / A.cut.lastWidth i := by field_simp; ring
      _ ≤ 8 * π ^ 2 * 1 / A.cut.lastWidth i := by gcongr
      _ ≤ 8 * π ^ 2 / D.ℓ := by rw [mul_one]; gcongr; exact hw.1
  calc ∑ i : Fin 4, _ ≤ ∑ _i : Fin 4, 8 * π ^ 2 / D.ℓ := Finset.sum_le_sum fun i _ => hterm i
    _ = 32 * π ^ 2 / D.ℓ := by simp; ring

/-- **Lemma 4.19(c)**: `Ĝ = ∑_k ∫_{T_k} g̃² ≤ Gb`. -/
theorem sum_top_le :
    ∑ jk ∈ A.cols, ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2,
      ENNReal.ofReal (A.cut.src D.c D.t D.d D.g x ^ 2) ≤ ENNReal.ofReal (Gb D.m D.t D.ℓ D.Sd) := by
  have hm := h.m_pos
  have hℓ := h.ℓ_pos
  have hπ := Real.pi_pos
  have hS := h.Sd_nonneg
  set c₀ := 6 * (2 * π * D.m) ^ 2
  set κ2 : ℂ → ℝ := fun x => ∑ i : Fin 4, (2 * π * A.cut.θ i / A.cut.lastWidth i) ^ 2 *
    ((carryA D.c D.t D.d i (A.cut.lastWidth i)).indicator (1 : ℂ → ℝ) x +
      (carryA' D.c D.t D.d i (A.cut.lastWidth i)).indicator 1 x)
  have hκ0 : ∀ x, 0 ≤ κ2 x := fun x => Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
    (add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun _ _ => zero_le_one) _))
  set I : ℂ → ℝ := fun x => D.Abar.indicator (fun y => ‖D.Φ y‖) x
  set H : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (7776 * D.nD x ^ 2) +
    ENNReal.ofReal (6 * I x ^ 2) + ENNReal.ofReal (8 * κ2 x)
  have hpt : ∀ x, ENNReal.ofReal (A.cut.src D.c D.t D.d D.g x ^ 2) ≤ ENNReal.ofReal c₀ + H x := by
    intro x
    have := Good.src_sq_le (A := A) h x
    have h0 : 0 ≤ c₀ := by positivity
    have h1 : 0 ≤ 7776 * D.nD x ^ 2 := by positivity
    have h2 : 0 ≤ 6 * I x ^ 2 := by positivity
    have h3 : 0 ≤ 8 * κ2 x := by have := hκ0 x; positivity
    have he : ENNReal.ofReal c₀ + H x =
        ENNReal.ofReal (c₀ + (7776 * D.nD x ^ 2 + 6 * I x ^ 2 + 8 * κ2 x)) := by
      rw [ENNReal.ofReal_add h0 (by positivity), ENNReal.ofReal_add (by positivity) h3,
        ENNReal.ofReal_add h1 h2]
    rw [he]
    exact ENNReal.ofReal_le_ofReal (by simp only [c₀, I, κ2] at this ⊢; linarith)
  -- the constant part: the tops have total area `36L`
  have hconst : ∑ jk ∈ A.cols, volume (A.cut.top D.c D.t D.d jk.1 jk.2) ≤ ENNReal.ofReal (36 * D.t) := by
    have : ∑ jk ∈ A.cols, volume (A.cut.top D.c D.t D.d jk.1 jk.2) =
        ∑ j : Fin 4, ∑ k ∈ Finset.range (A.cut.K j), volume (A.cut.top D.c D.t D.d j k) := by
      classical
      rw [cols, Finset.sum_biUnion]
      · exact Finset.sum_congr rfl fun j _ =>
          Finset.sum_image fun k _ k' _ hkk' => by simpa using hkk'
      · intro j _ j' _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro i hi hi'
        simp only [Finset.mem_image] at hi hi'
        obtain ⟨k, _, rfl⟩ := hi
        obtain ⟨k', _, he⟩ := hi'
        exact hne (congrArg Prod.fst he).symm
    rw [this, Finset.sum_congr rfl fun j _ => hA.sum_volume_top h j, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := h.side_ge
    rw [side] at this ⊢
    norm_num
    nlinarith [h.d_pos]
  -- the variable part: the tops overlap in null sets
  have hnull : ∀ jk ∈ A.cols, ∀ jk' ∈ A.cols, jk ≠ jk' →
      volume (A.cut.top D.c D.t D.d jk.1 jk.2 ∩ A.cut.top D.c D.t D.d jk'.1 jk'.2) = 0 :=
    fun jk hjk jk' hjk' hne => measure_mono_null
      (inter_subset_inter (Good.top_subset_col h jk) (Good.top_subset_col h jk'))
      (hA.volume_col_inter h hjk hjk' hne)
  have hvar := sum_setLIntegral_le_of_null A.cols (fun jk => A.cut.top D.c D.t D.d jk.1 jk.2)
    (fun _ _ => Rect.measurableSet_box measurableSet_Icc measurableSet_Icc) hnull H
  have hH : ∫⁻ x, H x ≤ ENNReal.ofReal (7776 * N2b D.m D.t D.Sd) + ENNReal.ofReal (6 * D.Sd) +
      ENNReal.ofReal (8 * (32 * π ^ 2 / D.ℓ)) := by
    have hm1 : AEMeasurable (fun x => ENNReal.ofReal (7776 * D.nD x ^ 2)) :=
      ((Data.measurable_nD.pow_const 2).const_mul _).ennreal_ofReal.aemeasurable
    have hm2 : AEMeasurable (fun x => ENNReal.ofReal (6 * I x ^ 2)) := by
      have : AEMeasurable I := by
        simp only [I]
        refine (aemeasurable_indicator_iff Data.measurableSet_Abar).2 ?_
        exact (h.integrableOn_Φ_R.mono_set Data.Abar_subset_R).aestronglyMeasurable.norm.aemeasurable
      exact ((this.pow_const 2).const_mul _).ennreal_ofReal
    have hint8 : Integrable fun x => 8 * κ2 x :=
      (integrable_finsetSum _ fun i _ => (Good.integrable_carryInd i).const_mul _).const_mul _
    simp only [H]
    rw [lintegral_add_right' _ hint8.aemeasurable.ennreal_ofReal, lintegral_add_left' hm1]
    · gcongr
      · simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7776)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact h.lintegral_nD_sq_le_N2b
      · simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        simpa using h.lintegral_Abar_le univ
      · have hint : Integrable fun x => 8 * κ2 x := by
          refine (integrable_finsetSum _ fun i _ => ?_).const_mul _
          exact (((integrable_indicator_iff measurableSet_carryA).2
            (integrableOn_const (by rw [volume_carryA]; exact ENNReal.ofReal_ne_top))).add
            ((integrable_indicator_iff measurableSet_carryA').2
              (integrableOn_const (by rw [volume_carryA']; exact ENNReal.ofReal_ne_top)))).const_mul _
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => by have := hκ0 x; simp only [Pi.zero_apply]; positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        have := hA.integral_carry_sq_le h
        linarith
  calc ∑ jk ∈ A.cols, ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2,
        ENNReal.ofReal (A.cut.src D.c D.t D.d D.g x ^ 2)
      ≤ ∑ jk ∈ A.cols, ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2, (ENNReal.ofReal c₀ + H x) :=
        Finset.sum_le_sum fun jk _ => lintegral_mono fun x => hpt x
    _ = ∑ jk ∈ A.cols, (ENNReal.ofReal c₀ * volume (A.cut.top D.c D.t D.d jk.1 jk.2) +
          ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2, H x) := by
        refine Finset.sum_congr rfl fun jk _ => ?_
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ = ENNReal.ofReal c₀ * ∑ jk ∈ A.cols, volume (A.cut.top D.c D.t D.d jk.1 jk.2) +
          ∑ jk ∈ A.cols, ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2, H x := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ENNReal.ofReal c₀ * ENNReal.ofReal (36 * D.t) + (ENNReal.ofReal (7776 * N2b D.m D.t D.Sd) +
          ENNReal.ofReal (6 * D.Sd) + ENNReal.ofReal (8 * (32 * π ^ 2 / D.ℓ))) := by
        gcongr
        exact hvar.trans hH
    _ = ENNReal.ofReal (Gb D.m D.t D.ℓ D.Sd) := by
        have hN : 0 ≤ N2b D.m D.t D.Sd := by rw [N2b]; have := h.t_pos; positivity
        have hc0 : 0 ≤ c₀ := by simp only [c₀]; positivity
        have ht := h.t_pos
        have e1 : 0 ≤ c₀ * (36 * D.t) := by positivity
        have e2 : 0 ≤ 7776 * N2b D.m D.t D.Sd := by positivity
        have e3 : 0 ≤ 6 * D.Sd := by positivity
        have e4 : 0 ≤ 8 * (32 * π ^ 2 / D.ℓ) := by positivity
        rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add e2 e3,
          ← ENNReal.ofReal_add (add_nonneg e2 e3) e4,
          ← ENNReal.ofReal_add e1 (add_nonneg (add_nonneg e2 e3) e4), Gb]
        congr 1
        simp only [c₀]
        ring

/-- **Lemma 4.19(b)**: `∫ |∑_k V_k|² ≤ 504 ℓc Gb`. -/
theorem lintegral_Vflux_le :
    ∫⁻ x, ENNReal.ofReal (‖A.Vflux D x‖ ^ 2) ≤ ENNReal.ofReal (504 * D.ℓ * Gb D.m D.t D.ℓ D.Sd) := by
  have hat := ae_atMostOne A.cols (A.col D) fun _ hi _ hj hne => hA.volume_col_inter h hi hj hne
  have hpt : ∀ᵐ x, ENNReal.ofReal (‖A.Vflux D x‖ ^ 2) =
      ∑ jk ∈ A.cols, ENNReal.ofReal (‖A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x‖ ^ 2) := by
    filter_upwards [hat] with x hx
    rw [Vflux, norm_sq_sum_of_atMostOne hx fun jk _ hxjk => Good.fluxV_eq_zero h hxjk,
      ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  have hmeas : ∀ jk ∈ A.cols, AEMeasurable fun x =>
      ENNReal.ofReal (‖A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x‖ ^ 2) := fun jk hjk =>
    ((h.cutHyp.isFieldPiece_fluxV hA.isCut (mem_cols.1 hjk)).1.aestronglyMeasurable.norm.aemeasurable.pow_const
      2).ennreal_ofReal
  rw [lintegral_congr_ae hpt, lintegral_finsetSum' _ hmeas]
  calc ∑ jk ∈ A.cols, ∫⁻ x, ENNReal.ofReal (‖A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x‖ ^ 2)
      ≤ ∑ jk ∈ A.cols, ENNReal.ofReal (504 * D.ℓ) *
          ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2, ENNReal.ofReal (A.cut.src D.c D.t D.d D.g x ^ 2) :=
        Finset.sum_le_sum fun jk hjk =>
          h.cutHyp.lintegral_norm_sq_fluxV_le hA.isCut (mem_cols.1 hjk)
    _ = ENNReal.ofReal (504 * D.ℓ) * ∑ jk ∈ A.cols,
          ∫⁻ x in A.cut.top D.c D.t D.d jk.1 jk.2, ENNReal.ofReal (A.cut.src D.c D.t D.d D.g x ^ 2) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (504 * D.ℓ) * ENNReal.ofReal (Gb D.m D.t D.ℓ D.Sd) := by
        gcongr; exact hA.sum_top_le h
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith [h.ℓ_pos])]

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
