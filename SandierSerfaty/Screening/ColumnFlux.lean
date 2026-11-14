/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ColumnCutProps
public import SandierSerfaty.Screening.FluxCell

/-!
# Flux cells of the columns (screening note, Lemma 4.19)

The screening note, Lemma 4.19 (`lem:flux`), for the columns of a column cut
`C` (`ColumnCut.IsCut`, under `Pinwheel.CutHyp`). For the column `k` of `R_j`, `I_k = [u_k, u_{k+1}]`
of width `w_k` (`ColumnCut.width`):

* `T_k = Ψ_j(I_k × [d - 1, w_f])` (`ColumnCut.top`), `H'_k = Ψ_j(I_k × [d - 1 - ℓc, d - 1])`
  (`ColumnCut.comp`), the flux cell `H_k = H'_k ∪ T_k = Ψ_j(I_k × [d - 1 - ℓc, w_f])`
  (`ColumnCut.fluxRect`, the sub-rectangle with `s`-axis along `u`, height `ℓc + 9`);
* `μ_k = m + (2π w_k ℓc)⁻¹ ∫_{T_k} g̃` (`ColumnCut.muK`); the flux-cell source is `g̃` on `T_k` and
  `2π(m - μ_k)` on `H'_k` (`ColumnCut.fluxConst_fluxRect`), and `V_k = T2_{H_k}[f_k]`
  (`ColumnCut.fluxV`).

Results (`CutHyp.…`):

* (a) `abs_muK_sub_le`: `|μ_k - m| ≤ m/4`;
  `integral_inner_fluxV`: `∫ ⟪V_k, ∇φ⟫ = -∫_{H_k} f_k φ` for Lipschitz `φ`; `isFieldPiece_fluxV`;
* (b) `lintegral_norm_sq_fluxV_le`: `∫ |V_k|² ≤ 504 ℓc ∫_{T_k} g̃²`.

Part (c) of Lemma 4.19 (the bound on `Ĝ = ∫_T g̃²`) depends on the soft-cut decomposition of `g`
(Definition 4.10) and is left to the assembly.
-/

open MeasureTheory Set Real
open scoped ENNReal NNReal

public section

namespace SandierSerfaty.Screening.Pinwheel

namespace ColumnCut

variable (C : ColumnCut)

/-- The width `w_k = u_{k+1} - u_k` of the column `k` of `R_j`. -/
@[expose] def width (j : Fin 4) (k : ℕ) : ℝ := C.u j (k + 1) - C.u j k

/-- The top part `T_k = Ψ_j(I_k × [d - 1, w_f])`. -/
@[expose] def top (c : ℂ) (t d : ℝ) (j : Fin 4) (k : ℕ) : Set ℂ :=
  (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc (d - 1) (d + 8))

/-- The compensation strip `H'_k = Ψ_j(I_k × [d - 1 - ℓc, d - 1])`. -/
@[expose] def comp (c : ℂ) (t d ℓ : ℝ) (j : Fin 4) (k : ℕ) : Set ℂ :=
  (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc (d - 1 - ℓ) (d - 1))

/-- The flux cell `H_k = Ψ_j(I_k × [d - 1 - ℓc, w_f])`, a sub-rectangle of `R_j`. -/
@[expose] noncomputable def fluxRect (c : ℂ) (t d ℓ : ℝ) (j : Fin 4) (k : ℕ) : Rect :=
  (rect c t d j).sub (C.u j k) (d - 1 - ℓ) (C.width j k) (ℓ + 9)

/-- `μ_k = m + (2π w_k ℓc)⁻¹ ∫_{T_k} g̃`. -/
@[expose] noncomputable def muK (c : ℂ) (t d m ℓ : ℝ) (g : ℂ → ℝ) (j : Fin 4) (k : ℕ) : ℝ :=
  m + (2 * π * C.width j k * ℓ)⁻¹ * ∫ x in C.top c t d j k, C.src c t d g x

/-- The flux-cell field `V_k = T2_{H_k}[f_k]`. -/
@[expose] noncomputable def fluxV (c : ℂ) (t d ℓ : ℝ) (g : ℂ → ℝ) (j : Fin 4) (k : ℕ) : ℂ → ℂ :=
  (C.fluxRect c t d ℓ j k).fluxField ℓ (C.src c t d g)

variable {C} {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {j : Fin 4} {k : ℕ}

@[simp] theorem fluxRect_width : (C.fluxRect c t d ℓ j k).width = C.width j k := rfl

@[simp] theorem fluxRect_height : (C.fluxRect c t d ℓ j k).height = ℓ + 9 := rfl

theorem carrier_fluxRect :
    (C.fluxRect c t d ℓ j k).carrier =
      (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc (d - 1 - ℓ) (d + 8)) := by
  rw [fluxRect, Rect.carrier_sub, width, add_sub_cancel]
  congr 2; ring

theorem fluxTop_fluxRect : (C.fluxRect c t d ℓ j k).fluxTop ℓ = C.top c t d j k := by
  ext x
  simp only [Rect.fluxTop, fluxRect, top, Rect.mem_box, Rect.coords_sub, Complex.sub_re,
    Complex.sub_im, mem_Icc, Rect.sub_width, Rect.sub_height, width]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem fluxConst_fluxRect (hw : C.width j k ≠ 0) (hℓ : ℓ ≠ 0) :
    (C.fluxRect c t d ℓ j k).fluxConst ℓ (C.src c t d g) = 2 * π * (m - C.muK c t d m ℓ g j k) := by
  rw [Rect.fluxConst, fluxTop_fluxRect, fluxRect_width, muK]
  have := Real.pi_pos.ne'
  field_simp
  ring

end ColumnCut

namespace CutHyp

variable {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {ntot : ℤ} (h : CutHyp c t d m ℓ g ntot)
  {C : ColumnCut} (hC : C.IsCut c t d ℓ g ntot) {j : Fin 4} {k : ℕ} (hk : k < C.K j)
include h hC hk

theorem width_mem : C.width j k ∈ Icc ℓ (3 * ℓ) :=
  (hC.partition j).step_mem h.ℓ_pos.le (Nat.succ_le_of_lt hk)

theorem width_pos : 0 < C.width j k := h.ℓ_pos.trans_le (h.width_mem hC hk).1

theorem u_mem : C.u j k ∈ Icc 0 (side t d) := (hC.partition j).mem_Icc h.ℓ_pos.le hk.le

theorem u_succ_mem : C.u j (k + 1) ∈ Icc 0 (side t d) :=
  (hC.partition j).mem_Icc h.ℓ_pos.le (Nat.succ_le_of_lt hk)

omit h hC hk in
/-- `g̃` is integrable on every set of finite measure on which `g` is. -/
theorem integrableOn_tildeG {θ w : Fin 4 → ℝ} {S : Set ℂ} (hSf : volume S ≠ ⊤)
    (hg : IntegrableOn g S) : IntegrableOn (tildeG c t d g θ w) S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have hind : ∀ A : Set ℂ, MeasurableSet A → IntegrableOn (A.indicator (1 : ℂ → ℝ)) S :=
    fun A hA => (integrable_const (1 : ℝ)).indicator hA
  unfold tildeG
  exact hg.sub (integrable_finsetSum _ fun i _ =>
    ((hind _ measurableSet_carryA).sub (hind _ measurableSet_carryA')).const_mul _)

omit hC hk in
/-- `g̃` is integrable on the boxes `Ψ_j([x, y] × [v₁, v₂]) ⊆ R_j`. -/
theorem integrableOn_src_box (C : ColumnCut) (j : Fin 4) {x y v₁ v₂ : ℝ} (hx : 0 ≤ x)
    (hy : y ≤ side t d) (hv₁ : 0 ≤ v₁) (hv₂ : v₂ ≤ d + 8) :
    IntegrableOn (C.src c t d g) ((rect c t d j).box (Icc x y) (Icc v₁ v₂)) := by
  refine integrableOn_tildeG ?_ (h.integrableOn_box j hx hy hv₁ hv₂)
  rw [Rect.volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem integrableOn_src_top : IntegrableOn (C.src c t d g) (C.top c t d j k) :=
  h.integrableOn_src_box C j (h.u_mem hC hk).1 (h.u_succ_mem hC hk).2
    (by linarith [h.d_ge, h.K4]) le_rfl

/-- **Lemma 4.19(a)**: `|μ_k - m| ≤ m/4`. -/
theorem abs_muK_sub_le : |C.muK c t d m ℓ g j k - m| ≤ m / 4 := by
  have hw := h.width_mem hC hk
  have hw0 := h.width_pos hC hk
  have hℓ := h.ℓ_pos
  have htop := h.abs_integral_top_le hC j (x := C.u j k) (w := C.width j k) (h.u_mem hC hk).1
    (by rw [ColumnCut.width, add_sub_cancel]; exact (h.u_succ_mem hC hk).2) hw
  rw [show C.u j k + C.width j k = C.u j (k + 1) by rw [ColumnCut.width]; ring] at htop
  rw [ColumnCut.muK, add_sub_cancel_left, abs_mul, abs_inv,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π * C.width j k * ℓ), ColumnCut.top]
  rw [inv_mul_le_iff₀ (by positivity)]
  calc _ ≤ π / 2 * m * C.width j k * ℓ := htop
    _ = 2 * π * C.width j k * ℓ * (m / 4) := by ring

/-- `μ_k ∈ [3m/4, 5m/4]`. -/
theorem muK_mem : C.muK c t d m ℓ g j k ∈ Icc (3 * m / 4) (5 * m / 4) := by
  have := abs_le.1 (h.abs_muK_sub_le hC hk)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

omit h hC hk in
theorem ell_le_height : ℓ ≤ (C.fluxRect c t d ℓ j k).height := by
  rw [ColumnCut.fluxRect_height]; linarith

/-- **Lemma 4.19(a)**: `∫ ⟪V_k, ∇φ⟫ = -∫_{H_k} f_k φ` for every Lipschitz `φ`. -/
theorem integral_inner_fluxV {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∫ x, inner ℝ (C.fluxV c t d ℓ g j k x) (gradient φ x) =
      -∫ x in (C.fluxRect c t d ℓ j k).carrier,
        (C.fluxRect c t d ℓ j k).fluxSrc ℓ (C.src c t d g) x * φ x :=
  Rect.integral_inner_fluxField h.ℓ_pos ell_le_height
    (by rw [ColumnCut.fluxTop_fluxRect]; exact h.integrableOn_src_top hC hk) (h.width_pos hC hk) hφ

/-- `V_k` is a field piece without charges and with source `1_{H_k} f_k`. -/
theorem isFieldPiece_fluxV :
    IsFieldPiece (C.fluxV c t d ℓ g j k) ∅
      ((C.fluxRect c t d ℓ j k).carrier.indicator
        ((C.fluxRect c t d ℓ j k).fluxSrc ℓ (C.src c t d g))) :=
  Rect.isFieldPiece_fluxField h.ℓ_pos ell_le_height
    (by rw [ColumnCut.fluxTop_fluxRect]; exact h.integrableOn_src_top hC hk) (h.width_pos hC hk)

omit h hC hk in
/-- The flux-cell source is `g̃` on `T_k`. -/
theorem fluxSrc_col_of_mem_top {x : ℂ} (hx : x ∈ C.top c t d j k) :
    (C.fluxRect c t d ℓ j k).fluxSrc ℓ (C.src c t d g) x = C.src c t d g x := by
  rw [← ColumnCut.fluxTop_fluxRect (ℓ := ℓ)] at hx
  exact Rect.fluxSrc_of_mem_fluxTop hx

/-- The flux-cell source is `2π(m - μ_k)` a.e. on `H'_k`. -/
theorem ae_fluxSrc_col_comp :
    ∀ᵐ x, x ∈ C.comp c t d ℓ j k →
      (C.fluxRect c t d ℓ j k).fluxSrc ℓ (C.src c t d g) x = 2 * π * (m - C.muK c t d m ℓ g j k) := by
  filter_upwards [(C.fluxRect c t d ℓ j k).ae_fluxSrc_bottom (ℓ := ℓ) (F := C.src c t d g)]
    with x hx hxc
  rw [hx, ColumnCut.fluxConst_fluxRect (h.width_pos hC hk).ne' h.ℓ_pos.ne']
  simp only [ColumnCut.comp, ColumnCut.fluxRect, Rect.mem_box, Rect.coords_sub, Complex.sub_re,
    Complex.sub_im, mem_Icc, Rect.sub_width, ColumnCut.width] at hxc ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hxc
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **Lemma 4.19(b)**: `∫ |V_k|² ≤ 504 ℓc ∫_{T_k} g̃²`. -/
theorem lintegral_norm_sq_fluxV_le :
    ∫⁻ x, ENNReal.ofReal (‖C.fluxV c t d ℓ g j k x‖ ^ 2) ≤
      ENNReal.ofReal (504 * ℓ) * ∫⁻ x in C.top c t d j k, ENNReal.ofReal (C.src c t d g x ^ 2) := by
  have hw := h.width_mem hC hk
  have hw0 := h.width_pos hC hk
  have hℓ := h.ℓ_pos
  have hK4 := h.K4
  have hb := Rect.lintegral_norm_sq_fluxField_le h.ℓ_pos ell_le_height
    (by rw [ColumnCut.fluxTop_fluxRect]; exact h.integrableOn_src_top hC hk) (h.width_pos hC hk)
  rw [ColumnCut.fluxTop_fluxRect, ColumnCut.fluxRect_width, ColumnCut.fluxRect_height] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity))
  have h1 : C.width j k ^ 2 / (ℓ + 9) ≤ 9 * ℓ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hw.1, hw.2]
  rw [show ℓ + 9 - ℓ = (9 : ℝ) by ring]
  linarith

end CutHyp

end SandierSerfaty.Screening.Pinwheel

end
