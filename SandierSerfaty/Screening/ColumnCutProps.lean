/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ColumnCut

/-!
# Properties of a column cut (screening note, Lemma 4.18(c),(d))

The screening note, Lemma 4.18(c),(d) (`lem:cuts`). These hold for every
column cut `C` with `C.IsCut` (they do not depend on the choices):

* (c) `ColumnCut.carryA_subset_top`: `A_j ⊆ T_last(R_j)`;
  `ColumnCut.carryA'_subset_bottom`: `A'_j ⊆ Ψ_{j+1}([0, u_1] × [0, d - 1 - ℓc])`, i.e. inside the
  first filler part of `R_{j+1}` and below its compensation strip;
  `ColumnCut.sqDepth_mem_of_mem_carryRect`: the carry cells lie in `O_- ∩ {0 ≤ δ ≤ 3ℓc}`;
  `ColumnCut.kappa_mem`: `κ_j = 2πθ_j/w'_j ∈ [0, 2π/ℓc]`;
  `ColumnCut.src_bottom`: `g̃ = 2πm + κ_{j-1} 1_{A'_{j-1}}` a.e. on the bottom parts
  `Ψ_j([0, L] × [0, d - 1])` (so `g̃ = 2πm` on `P_k \ ⋃ A'` and `g̃ ∈ [2πm, 2πm + 2π/ℓc]` on `A'_j`);
* (d) `ColumnCut.abs_integral_top_le`: `|∫_{T_I} g̃| ≤ (π/2) m w ℓc` and
  `ColumnCut.col_mass_ge`: `(2π)⁻¹ ∫_{Ψ_j(I × [0, w_f])} g̃ ≥ 6 m w ℓc`, for every interval
  `I ⊆ [0, L]` of length `w ∈ [ℓc, 3ℓc]`.
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty.Screening.Pinwheel

namespace ColumnCut

variable {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {ntot : ℤ} {C : ColumnCut}

theorem IsCut.lastWidth_mem (hC : C.IsCut c t d ℓ g ntot) (j : Fin 4) :
    C.lastWidth j ∈ Ico ℓ (3 * ℓ) :=
  (hC.partition j).stepLast

theorem IsCut.lastWidth_mem_Icc (hC : C.IsCut c t d ℓ g ntot) (hℓ : 0 ≤ ℓ) (j : Fin 4) :
    C.lastWidth j ∈ Icc 0 (3 * ℓ) :=
  ⟨hℓ.trans (hC.lastWidth_mem j).1, (hC.lastWidth_mem j).2.le⟩

/-- **Lemma 4.18(c)**: `κ_j = 2πθ_j / w'_j ∈ [0, 2π/ℓc]`. -/
theorem IsCut.kappa_mem (hC : C.IsCut c t d ℓ g ntot) (hℓ : 0 < ℓ) (j : Fin 4) :
    C.kappa j ∈ Icc 0 (2 * π / ℓ) := by
  have hw := hC.lastWidth_mem j
  have hθ := hC.θ_mem j
  have hw0 : 0 < C.lastWidth j := hℓ.trans_le hw.1
  refine ⟨div_nonneg (by have := Real.pi_pos; have := hθ.1; positivity) hw0.le, ?_⟩
  rw [kappa, div_le_div_iff₀ hw0 hℓ]
  have := Real.pi_pos
  have h1 : 2 * π * C.θ j * ℓ ≤ 2 * π * 1 * ℓ := by gcongr; exact hθ.2.le
  nlinarith [hw.1]

/-- **Lemma 4.18(c)**: `A'_j` lies in the first filler part of `R_{j+1}`, below its compensation
strip `Ψ_{j+1}(I_1 × [d - 1 - ℓc, d - 1])`. -/
theorem IsCut.carryA'_subset_bottom (hC : C.IsCut c t d ℓ g ntot) (hℓ : 1 ≤ ℓ) (hd : 4 * ℓ + 1 ≤ d)
    (j : Fin 4) :
    carryA' c t d j (C.lastWidth j) ⊆
      (rect c t d (j + 1)).box (Icc 0 (C.u (j + 1) 1)) (Icc 0 (d - 1 - ℓ)) := by
  have hP := hC.partition (j + 1)
  have h1 := (hP.step_mem (by linarith) (k := 0) (by have := hP.one_le; omega)).1
  rw [hP.zero, zero_add, sub_zero] at h1
  rw [carryA']
  exact Rect.box_mono (Icc_subset_Icc le_rfl (by linarith))
    (Icc_subset_Icc le_rfl (by linarith [(hC.lastWidth_mem j).2]))

end ColumnCut

namespace CutHyp

variable {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {ntot : ℤ} (h : CutHyp c t d m ℓ g ntot)
  {C : ColumnCut}
include h

/-- **Lemma 4.20 (location)**: the carry cells `H^c_j = A_j ∪ A'_j` lie in `{0 ≤ δ ≤ 3ℓc}`, hence in
`O_- = Q ∩ {δ ≤ d - 1}`. -/
theorem sqDepth_mem_of_mem_carryRect (hC : C.IsCut c t d ℓ g ntot) (j : Fin 4) {x : ℂ}
    (hx : x ∈ (carryRect c t d j (C.lastWidth j)).carrier) :
    sqDepth c t x ∈ Icc 0 (3 * ℓ) ∧ sqDepth c t x ≤ d - 1 := by
  have hw := hC.lastWidth_mem_Icc h.ℓ_pos.le j
  have := Pinwheel.sqDepth_mem_of_mem_carryRect h.offset_pos.le (hw.2.trans h.side_ge)
    (hw.2.trans (by linarith [h.d_ge, h.K4])) (by linarith [h.side_ge, h.K4])
    (by linarith [h.d_pos]) hx
  exact ⟨⟨this.1, this.2.trans hw.2⟩, this.2.trans (hw.2.trans (by linarith [h.d_ge, h.K4]))⟩

/-- The points of `R_j` off the junction lines lie in no other `R_i`. -/
theorem eq_of_mem_rect_of_notMem {x : ℂ} (hx : x ∉ junctionLines c (offset t d)) {i j : Fin 4}
    (hi : x ∈ (rect c t d i).carrier) (hj : x ∈ (rect c t d j).carrier) : i = j := by
  by_contra hij
  exact hx (rect_inter_subset h.offset_pos hij ⟨hi, hj⟩)

/-- **The carry sum on a subset of `R_j`**: for `S ⊆ R_j`,
`∑_i κ_i (|S ∩ A_i| - |S ∩ A'_i|) = κ_j |S ∩ A_j| - κ_{j-1} |S ∩ A'_{j-1}|`. -/
theorem sum_carry_eq (hC : C.IsCut c t d ℓ g ntot) (j : Fin 4) {S : Set ℂ}
    (hS : S ⊆ (rect c t d j).carrier) :
    ∑ i, 2 * π * C.θ i / C.lastWidth i *
        (volume.real (S ∩ carryA c t d i (C.lastWidth i)) -
          volume.real (S ∩ carryA' c t d i (C.lastWidth i))) =
      C.kappa j * volume.real (S ∩ carryA c t d j (C.lastWidth j)) -
        C.kappa (j - 1) * volume.real (S ∩ carryA' c t d (j - 1) (C.lastWidth (j - 1))) := by
  have hw := hC.lastWidth_mem_Icc h.ℓ_pos.le
  have hA : ∀ i, volume.real (S ∩ carryA c t d i (C.lastWidth i)) =
      if i = j then volume.real (S ∩ carryA c t d j (C.lastWidth j)) else 0 := by
    intro i
    split_ifs with hij
    · rw [hij]
    · have : volume (S ∩ carryA c t d i (C.lastWidth i)) = 0 :=
        measure_mono_null (inter_subset_inter hS (h.carryA_subset hw i))
          (aedisjoint_rect h.offset_pos (Ne.symm hij))
      simp [Measure.real, this]
  have hA' : ∀ i, volume.real (S ∩ carryA' c t d i (C.lastWidth i)) =
      if i = j - 1 then volume.real (S ∩ carryA' c t d (j - 1) (C.lastWidth (j - 1))) else 0 := by
    intro i
    split_ifs with hij
    · rw [hij]
    · have hne : j ≠ i + 1 := fun e => hij (by rw [e, add_sub_cancel_right])
      have : volume (S ∩ carryA' c t d i (C.lastWidth i)) = 0 :=
        measure_mono_null (inter_subset_inter hS (h.carryA'_subset hw i))
          (aedisjoint_rect h.offset_pos hne)
      simp [Measure.real, this]
  rw [Finset.sum_congr rfl fun i _ => by rw [hA i, hA' i]]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, ColumnCut.kappa]

/-- **Lemma 4.18(d)**, top strips: `|∫_{T_I} g̃| ≤ (π/2) m w ℓc` for `I = [x, x + w] ⊆ [0, L]`,
`w ∈ [ℓc, 3ℓc]`. -/
theorem abs_integral_top_le (hC : C.IsCut c t d ℓ g ntot) (j : Fin 4) {x w : ℝ} (hx : 0 ≤ x)
    (hxw : x + w ≤ side t d) (hw : w ∈ Icc ℓ (3 * ℓ)) :
    |∫ z in (rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8)), C.src c t d g z| ≤
      π / 2 * m * w * ℓ := by
  set T := (rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8))
  have hd1 : 0 ≤ d - 1 := by linarith [h.d_ge, h.K4]
  have hTR : T ⊆ (rect c t d j).carrier := box_subset_rect j hx hxw hd1 le_rfl
  have hTf : volume T ≠ ⊤ := by
    rw [Rect.volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hgT := h.integrableOn_box j hx hxw hd1 le_rfl
  rw [ColumnCut.src, integral_tildeG C.θ C.lastWidth hTf hgT, h.sum_carry_eq hC j hTR]
  -- `T` misses `A'_{j-1}`
  have hA' : volume.real (T ∩ carryA' c t d (j - 1) (C.lastWidth (j - 1))) = 0 := by
    have hw1 := hC.lastWidth_mem_Icc h.ℓ_pos.le (j - 1)
    have : T ∩ carryA' c t d (j - 1) (C.lastWidth (j - 1)) = ∅ := by
      rw [carryA', sub_add_cancel, Rect.box_inter]
      refine eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨-, ⟨h1, -⟩, ⟨-, h2⟩⟩ := Rect.mem_box.1 hz
      linarith [hw1.2, h.d_ge, h.K4]
    rw [this, measureReal_empty]
  have hAj : volume.real (T ∩ carryA c t d j (C.lastWidth j)) ≤ C.lastWidth j := by
    have hw0 := (hC.lastWidth_mem_Icc h.ℓ_pos.le j).1
    calc volume.real (T ∩ carryA c t d j (C.lastWidth j))
        ≤ volume.real (carryA c t d j (C.lastWidth j)) :=
          measureReal_mono inter_subset_right (by
            rw [volume_carryA]; exact ENNReal.ofReal_ne_top)
      _ = C.lastWidth j := by rw [Measure.real, volume_carryA, ENNReal.toReal_ofReal hw0]
  have hκ := hC.kappa_mem h.ℓ_pos j
  have hκw : C.kappa j * C.lastWidth j = 2 * π * C.θ j := by
    have := (h.ℓ_pos.trans_le (hC.lastWidth_mem j).1).ne'
    rw [ColumnCut.kappa]; field_simp
  have hθ := (hC.θ_mem j).2
  have habs := abs_integral_le_integral_abs (μ := volume.restrict T) (f := g)
  have hstrip := h.strip j x w hx hxw hw
  have hA0 : 0 ≤ volume.real (T ∩ carryA c t d j (C.lastWidth j)) := measureReal_nonneg
  rw [hA', mul_zero, sub_zero, abs_le]
  have hle : C.kappa j * volume.real (T ∩ carryA c t d j (C.lastWidth j)) ≤ 2 * π := by
    calc C.kappa j * volume.real (T ∩ carryA c t d j (C.lastWidth j))
        ≤ C.kappa j * C.lastWidth j := mul_le_mul_of_nonneg_left hAj hκ.1
      _ = 2 * π * C.θ j := hκw
      _ ≤ 2 * π := by have := Real.pi_pos; nlinarith
  have hnn : 0 ≤ C.kappa j * volume.real (T ∩ carryA c t d j (C.lastWidth j)) :=
    mul_nonneg hκ.1 hA0
  constructor <;> linarith [abs_le.1 (habs.trans hstrip)]

/-- **Lemma 4.18(c)**: `g̃ = 2πm + κ_{j-1} 1_{A'_{j-1}}` a.e. on the bottom part
`Ψ_j([0, L] × [0, d - 1])` of `R_j` (so `g̃ = 2πm` on the filler parts off `A'`, and
`2πm ≤ g̃ ≤ 2πm + 2π/ℓc` there). -/
theorem src_bottom (hC : C.IsCut c t d ℓ g ntot) (j : Fin 4) :
    ∀ᵐ x, x ∈ (rect c t d j).box (Icc 0 (side t d)) (Icc 0 (d - 1)) →
      C.src c t d g x = 2 * π * m +
        C.kappa (j - 1) * (carryA' c t d (j - 1) (C.lastWidth (j - 1))).indicator 1 x := by
  have hw := hC.lastWidth_mem_Icc h.ℓ_pos.le
  have hjl : ∀ᵐ x, x ∉ junctionLines c (offset t d) :=
    measure_eq_zero_iff_ae_notMem.1 (volume_junctionLines c _)
  filter_upwards [h.low j, hjl] with x hlow hx hxb
  have hxR : x ∈ (rect c t d j).carrier :=
    Rect.box_mono subset_rfl (Icc_subset_Icc le_rfl (by simp only [rect_height]; linarith)) hxb
  have hA : ∀ i, (carryA c t d i (C.lastWidth i)).indicator (1 : ℂ → ℝ) x = 0 := by
    intro i
    refine indicator_of_notMem (fun hxA => ?_) _
    have hij := h.eq_of_mem_rect_of_notMem hx (h.carryA_subset hw i hxA) hxR
    subst hij
    obtain ⟨-, h1, -⟩ := Rect.mem_box.1 hxA
    obtain ⟨-, -, h2⟩ := Rect.mem_box.1 hxb
    linarith
  have hA' : ∀ i, i ≠ j - 1 → (carryA' c t d i (C.lastWidth i)).indicator (1 : ℂ → ℝ) x = 0 := by
    intro i hi
    refine indicator_of_notMem (fun hxA => hi ?_) _
    have := h.eq_of_mem_rect_of_notMem hx (h.carryA'_subset hw i hxA) hxR
    rw [← this, add_sub_cancel_right]
  unfold ColumnCut.src tildeG
  rw [hlow hxb]
  simp only [hA, zero_sub, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [Finset.sum_eq_single (j - 1) (fun i _ hi => by rw [hA' i hi, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), ColumnCut.kappa]

end CutHyp

end SandierSerfaty.Screening.Pinwheel

end
