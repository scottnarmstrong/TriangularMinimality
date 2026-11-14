/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ColumnFlux

/-!
# The filler of a column (screening note, Definition 4.23, first sentence, with Lemma 4.21)

The screening note, Definition 4.23 (`def:assembly`): "for every column, apply
Lemma 4.21 to the filler part `P_k` (sides `w_k`, `h = d - 1`) with `μ = g̃/2π` on `P_k \ H'_k` and
`μ = μ_k` on `H'_k`". This file checks the hypotheses of Lemma 4.21 for every column of a column cut
(`ColumnCut.IsCut`, under `Pinwheel.CutHyp`) and produces the partition:

* `ColumnCut.fillRect`: the filler part `P_k = Ψ_j(I_k × [0, d - 1])` as a sub-rectangle of `R_j`;
* `ColumnCut.fillDensity`: `g̃/2π` on `{v < d - 1 - ℓc}`, `μ_k` above (on `P_k` the latter is `H'_k`);
* `CutHyp.ae_fillDensity_mem`: `m/2 ≤ μ ≤ 3m/2` a.e. on `P_k` (Lemma 4.18(c): `g̃/2π ∈ [m, m + 1/ℓc]`
  on the filler, (K2) `1/ℓc ≤ m/8`; Lemma 4.19(a): `μ_k ∈ [3m/4, 5m/4]`);
* `CutHyp.setIntegral_fillDensity`: `∫_{P_k} μ = n_k` whenever `∫_{Col_k} g̃ = 2π n_k` (the
  compensation strip carries `g̃ = 2πm` since it misses `A'`, and `μ_k w_k ℓc = m w_k ℓc + ∫_{T_k} g̃/2π`);
* `CutHyp.sqrt_mul_width_ge`, `CutHyp.sqrt_mul_fill_height_ge`: `w_k √m ≥ 2`, `(d - 1)√m ≥ 2`
  (from (K2), (K4); this is (K3));
* `CutHyp.exists_fillerPartition_col`: the filler partition of every column (Lemma 4.21).
-/

open MeasureTheory Set Real
open scoped ENNReal

public section

namespace SandierSerfaty.Screening.Pinwheel

namespace ColumnCut

variable (C : ColumnCut)

/-- The filler part `P_k = Ψ_j(I_k × [0, d - 1])`. -/
@[expose] noncomputable def fillRect (c : ℂ) (t d : ℝ) (j : Fin 4) (k : ℕ) : Rect :=
  (rect c t d j).sub (C.u j k) 0 (C.width j k) (d - 1)

/-- The part `{v < d - 1 - ℓc}` of `R_j` (in the coordinates of `R_j`). -/
@[expose] def lowSet (c : ℂ) (t d ℓ : ℝ) (j : Fin 4) : Set ℂ :=
  (rect c t d j).box univ (Iio (d - 1 - ℓ))

open scoped Classical in
/-- The filler density of the column `k` of `R_j`: `g̃/2π` below the compensation strip `H'_k`,
`μ_k` on it. -/
@[expose] noncomputable def fillDensity (c : ℂ) (t d m ℓ : ℝ) (g : ℂ → ℝ) (j : Fin 4) (k : ℕ) :
    ℂ → ℝ :=
  (lowSet c t d ℓ j).piecewise (fun x => C.src c t d g x / (2 * π))
    (fun _ => C.muK c t d m ℓ g j k)

variable {C} {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {j : Fin 4} {k : ℕ}

@[simp] theorem fillRect_width : (C.fillRect c t d j k).width = C.width j k := rfl

@[simp] theorem fillRect_height : (C.fillRect c t d j k).height = d - 1 := rfl

theorem carrier_fillRect :
    (C.fillRect c t d j k).carrier =
      (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d - 1)) := by
  rw [fillRect, Rect.carrier_sub, width, add_sub_cancel, zero_add]

theorem measurableSet_lowSet : MeasurableSet (lowSet c t d ℓ j) :=
  Rect.measurableSet_box MeasurableSet.univ measurableSet_Iio

theorem fillDensity_of_mem {x : ℂ} (hx : x ∈ lowSet c t d ℓ j) :
    C.fillDensity c t d m ℓ g j k x = C.src c t d g x / (2 * π) := by
  classical
  rw [fillDensity]; convert Set.piecewise_eq_of_mem _ _ _ hx

theorem fillDensity_of_notMem {x : ℂ} (hx : x ∉ lowSet c t d ℓ j) :
    C.fillDensity c t d m ℓ g j k x = C.muK c t d m ℓ g j k := by
  classical
  rw [fillDensity]; convert Set.piecewise_eq_of_notMem _ _ _ hx

end ColumnCut

namespace CutHyp

variable {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {ntot : ℤ} (h : CutHyp c t d m ℓ g ntot)
  {C : ColumnCut} (hC : C.IsCut c t d ℓ g ntot) {j : Fin 4} {k : ℕ} (hk : k < C.K j)
include h hC hk

theorem fillRect_subset_bottom :
    (C.fillRect c t d j k).carrier ⊆ (rect c t d j).box (Icc 0 (side t d)) (Icc 0 (d - 1)) := by
  rw [ColumnCut.carrier_fillRect]
  exact Rect.box_mono (Icc_subset_Icc (h.u_mem hC hk).1 (h.u_succ_mem hC hk).2) subset_rfl

theorem integrableOn_src_fill : IntegrableOn (C.src c t d g) (C.fillRect c t d j k).carrier := by
  rw [ColumnCut.carrier_fillRect]
  exact h.integrableOn_src_box C j (h.u_mem hC hk).1 (h.u_succ_mem hC hk).2 le_rfl (by linarith)

/-- The filler density is a.e.-strongly measurable on `P_k`. -/
theorem aestronglyMeasurable_fillDensity :
    AEStronglyMeasurable (C.fillDensity c t d m ℓ g j k)
      (volume.restrict (C.fillRect c t d j k).carrier) := by
  classical
  rw [ColumnCut.fillDensity]
  refine AEStronglyMeasurable.piecewise ColumnCut.measurableSet_lowSet.nullMeasurableSet ?_
    aestronglyMeasurable_const
  exact ((h.integrableOn_src_fill hC hk).div_const _).aestronglyMeasurable.restrict

/-- `g̃ = 2πm + κ_{j-1} 1_{A'_{j-1}}` a.e. on `P_k`, with `κ_{j-1} ∈ [0, 2π/ℓc]`. -/
theorem ae_src_fill :
    ∀ᵐ x, x ∈ (C.fillRect c t d j k).carrier →
      C.src c t d g x / (2 * π) ∈ Icc m (m + 1 / ℓ) := by
  have hκ := hC.kappa_mem h.ℓ_pos (j - 1)
  have hπ := Real.pi_pos
  filter_upwards [h.src_bottom hC j] with x hx hxP
  rw [hx (h.fillRect_subset_bottom hC hk hxP)]
  set ι := (carryA' c t d (j - 1) (C.lastWidth (j - 1))).indicator (1 : ℂ → ℝ) x
  have hι : ι ∈ Icc (0 : ℝ) 1 := by
    simp only [ι]
    by_cases hA : x ∈ carryA' c t d (j - 1) (C.lastWidth (j - 1)) <;> simp [hA]
  have e : (2 * π * m + C.kappa (j - 1) * ι) / (2 * π) = m + C.kappa (j - 1) / (2 * π) * ι := by
    field_simp
  rw [e]
  have h1 : 0 ≤ C.kappa (j - 1) / (2 * π) * ι := mul_nonneg (div_nonneg hκ.1 (by positivity)) hι.1
  have h2 : C.kappa (j - 1) / (2 * π) * ι ≤ 1 / ℓ := by
    have : C.kappa (j - 1) / (2 * π) ≤ 1 / ℓ := by
      rw [div_le_iff₀ (by positivity)]
      calc C.kappa (j - 1) ≤ 2 * π / ℓ := hκ.2
        _ = 1 / ℓ * (2 * π) := by ring
    calc C.kappa (j - 1) / (2 * π) * ι ≤ C.kappa (j - 1) / (2 * π) * 1 :=
          mul_le_mul_of_nonneg_left hι.2 (div_nonneg hκ.1 (by positivity))
      _ ≤ 1 / ℓ := by rw [mul_one]; exact this
  exact ⟨by linarith, by linarith⟩

/-- **The density bounds of Lemma 4.21** on `P_k`: `m/2 ≤ μ ≤ 3m/2` a.e. -/
theorem ae_fillDensity_mem :
    ∀ᵐ x, x ∈ (C.fillRect c t d j k).carrier →
      C.fillDensity c t d m ℓ g j k x ∈ Icc (m / 2) (3 * m / 2) := by
  have hm := h.m_pos
  have hK2 : 1 / ℓ ≤ m / 8 := h.K2
  have hμ := h.muK_mem hC hk
  filter_upwards [h.ae_src_fill hC hk] with x hx hxP
  by_cases hlow : x ∈ ColumnCut.lowSet c t d ℓ j
  · rw [ColumnCut.fillDensity_of_mem hlow]
    have := hx hxP
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [ColumnCut.fillDensity_of_notMem hlow]
    exact ⟨by linarith [hμ.1], by linarith [hμ.2]⟩

/-- `g̃ = 2πm` a.e. on the compensation strip `H'_k` (it misses `A'_{j-1}` up to a segment). -/
theorem ae_src_comp :
    ∀ᵐ x, x ∈ C.comp c t d ℓ j k → C.src c t d g x = 2 * π * m := by
  have hline : ∀ᵐ x, x ∉ (rect c t d j).box univ {d - 1 - ℓ} :=
    measure_eq_zero_iff_ae_notMem.1 ((rect c t d j).volume_box_singleton_right univ _)
  have hA' := hC.carryA'_subset_bottom (by linarith [h.K4]) (by linarith [h.d_ge, h.K4]) (j - 1)
  rw [sub_add_cancel] at hA'
  filter_upwards [h.src_bottom hC j, hline] with x hx hxl hxc
  have hxb : x ∈ (rect c t d j).box (Icc 0 (side t d)) (Icc 0 (d - 1)) := by
    refine Rect.box_mono (Icc_subset_Icc (h.u_mem hC hk).1 (h.u_succ_mem hC hk).2)
      (Icc_subset_Icc (by linarith [h.d_ge, h.K4]) le_rfl) hxc
  rw [hx hxb]
  have hnot : x ∉ carryA' c t d (j - 1) (C.lastWidth (j - 1)) := by
    intro hxA
    have h1 := (hA' hxA).2.2
    have h2 := hxc.2.1
    exact hxl ⟨mem_univ _, le_antisymm h1 h2⟩
  rw [indicator_of_notMem hnot, mul_zero, add_zero]

/-- **The mass of the filler density**: `∫_{P_k} μ = n` whenever `∫_{Col_k} g̃ = 2πn`. -/
theorem setIntegral_fillDensity {n : ℝ}
    (hn : ∫ z in C.col c t d j k, C.src c t d g z = 2 * π * n) :
    ∫ x in (C.fillRect c t d j k).carrier, C.fillDensity c t d m ℓ g j k x = n := by
  have hu := (h.u_mem hC hk)
  have hu1 := (h.u_succ_mem hC hk)
  have hw := h.width_pos hC hk
  have hℓ := h.ℓ_pos
  have hd := h.d_ge
  have hK4 := h.K4
  have hπ := Real.pi_pos
  have hle : C.u j k ≤ C.u j (k + 1) := by
    have : C.width j k = C.u j (k + 1) - C.u j k := rfl
    linarith
  have hsrc : ∀ v₁ v₂, 0 ≤ v₁ → v₂ ≤ d + 8 → IntegrableOn (C.src c t d g) ((rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc v₁ v₂)) :=
    fun v₁ v₂ h1 h2 => h.integrableOn_src_box C j hu.1 hu1.2 h1 h2
  -- the density on `P_k`
  have hdens : IntegrableOn (C.fillDensity c t d m ℓ g j k) ((rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d - 1))) := by
    have hfin : volume ((rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d - 1))) ≠ ⊤ := by
      rw [Rect.volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (volume.restrict ((rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d - 1)))) :=
      isFiniteMeasure_restrict.2 hfin
    refine Integrable.mono' (integrable_const (3 * m / 2)) ?_ ?_
    · have := h.aestronglyMeasurable_fillDensity hC hk
      rwa [ColumnCut.carrier_fillRect] at this
    · have := h.ae_fillDensity_mem hC hk
      rw [ColumnCut.carrier_fillRect] at this
      refine (ae_restrict_iff' (Rect.measurableSet_box measurableSet_Icc measurableSet_Icc)).2
        (this.mono fun x hx hxP => ?_)
      have := hx hxP
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [this.1, this.2, h.m_pos]
  rw [ColumnCut.carrier_fillRect]
  rw [(rect c t d j).setIntegral_box_add_right measurableSet_Icc (by linarith : (0 : ℝ) ≤ d - 1 - ℓ)
    (by linarith) hdens]
  -- the low part: `μ = g̃/2π` a.e.
  have hline : ∀ᵐ x, x ∉ (rect c t d j).box univ {d - 1 - ℓ} :=
    measure_eq_zero_iff_ae_notMem.1 ((rect c t d j).volume_box_singleton_right univ _)
  have hlow : ∀ᵐ x, x ∈ (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d - 1 - ℓ)) →
      C.fillDensity c t d m ℓ g j k x = C.src c t d g x / (2 * π) := by
    filter_upwards [hline] with x hxl hx
    refine ColumnCut.fillDensity_of_mem ⟨mem_univ _, ?_⟩
    exact lt_of_le_of_ne hx.2.2 fun he => hxl ⟨mem_univ _, he⟩
  rw [setIntegral_congr_ae (Rect.measurableSet_box measurableSet_Icc measurableSet_Icc) hlow,
    integral_div]
  -- the compensation strip: `μ = μ_k`
  have hcomp : ∀ x ∈ (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc (d - 1 - ℓ) (d - 1)),
      C.fillDensity c t d m ℓ g j k x = C.muK c t d m ℓ g j k := fun x hx =>
    ColumnCut.fillDensity_of_notMem fun hl => absurd hl.2 (not_lt.2 hx.2.1)
  rw [setIntegral_congr_fun (Rect.measurableSet_box measurableSet_Icc measurableSet_Icc) hcomp,
    setIntegral_const, (rect c t d j).volume_real_box_Icc hle (by linarith), smul_eq_mul]
  -- decompose the column
  have hcol : ∫ z in C.col c t d j k, C.src c t d g z =
      (∫ z in (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc 0 (d - 1 - ℓ)), C.src c t d g z) +
        (∫ z in (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc (d - 1 - ℓ) (d - 1)), C.src c t d g z) +
          ∫ z in C.top c t d j k, C.src c t d g z := by
    rw [ColumnCut.col, (rect c t d j).setIntegral_box_add_right measurableSet_Icc (by linarith : (0 : ℝ) ≤ d - 1)
      (by linarith) (hsrc 0 (d + 8) le_rfl le_rfl),
      (rect c t d j).setIntegral_box_add_right measurableSet_Icc (by linarith : (0 : ℝ) ≤ d - 1 - ℓ)
      (by linarith) (hsrc 0 (d - 1) le_rfl (by linarith))]
    rfl
  have hHc : ∫ z in (rect c t d j).box (Icc (C.u j k) (C.u j (k + 1))) (Icc (d - 1 - ℓ) (d - 1)), C.src c t d g z =
      2 * π * m * ((C.u j (k + 1) - C.u j k) * (d - 1 - (d - 1 - ℓ))) := by
    rw [setIntegral_congr_ae (Rect.measurableSet_box measurableSet_Icc measurableSet_Icc)
      (h.ae_src_comp hC hk), setIntegral_const, (rect c t d j).volume_real_box_Icc hle (by linarith),
      smul_eq_mul]
    ring
  rw [hcol, hHc, show d - 1 - (d - 1 - ℓ) = ℓ by ring] at hn
  rw [ColumnCut.muK, ColumnCut.width, show d - 1 - (d - 1 - ℓ) = ℓ by ring]
  have hw' : C.u j (k + 1) - C.u j k ≠ 0 := hw.ne'
  have e : (C.u j (k + 1) - C.u j k) * ℓ * (m + (2 * π * (C.u j (k + 1) - C.u j k) * ℓ)⁻¹ *
      ∫ x in C.top c t d j k, C.src c t d g x) =
      m * ((C.u j (k + 1) - C.u j k) * ℓ) + (∫ x in C.top c t d j k, C.src c t d g x) / (2 * π) := by
    field_simp
  rw [e]
  field_simp
  linear_combination hn

omit hC hk in
/-- (K3) from (K2), (K4): `ℓc √m ≥ 2`. -/
theorem two_le_mul_sqrt : 2 ≤ ℓ * √m := by
  have hm := h.m_pos
  have h8 := h.eight_le_mul
  have hK4 := h.K4
  have hs : 0 ≤ √m := Real.sqrt_nonneg m
  have hss : √m ^ 2 = m := Real.sq_sqrt hm.le
  nlinarith [sq_nonneg (ℓ * √m - 2)]

theorem sqrt_mul_width_ge : 2 ≤ (C.fillRect c t d j k).width * √m := by
  rw [ColumnCut.fillRect_width]
  exact h.two_le_mul_sqrt.trans
    (mul_le_mul_of_nonneg_right (h.width_mem hC hk).1 (Real.sqrt_nonneg m))

omit hC hk in
theorem sqrt_mul_fill_height_ge (C : ColumnCut) (j : Fin 4) (k : ℕ) :
    2 ≤ (C.fillRect c t d j k).height * √m := by
  rw [ColumnCut.fillRect_height]
  exact h.two_le_mul_sqrt.trans
    (mul_le_mul_of_nonneg_right (by linarith [h.d_ge, h.K4]) (Real.sqrt_nonneg m))

/-- **The filler partition of a column** (screening note, Lemma 4.21 applied as in Definition 4.23). -/
theorem exists_fillerPartition_col {n : ℕ}
    (hn : ∫ z in C.col c t d j k, C.src c t d g z = 2 * π * n) :
    ∃ I piece, IsFillerPartition (C.fillRect c t d j k) (C.fillDensity c t d m ℓ g j k) m n I piece :=
  exists_fillerPartition _ h.m_pos (h.aestronglyMeasurable_fillDensity hC hk)
    (h.ae_fillDensity_mem hC hk) (h.setIntegral_fillDensity hC hk hn)
    (h.sqrt_mul_width_ge hC hk) (h.sqrt_mul_fill_height_ge C j k)

end CutHyp

end SandierSerfaty.Screening.Pinwheel

end
