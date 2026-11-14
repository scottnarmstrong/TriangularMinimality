/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenEnergy

/-!
# Constants of the screening theorem (screening note, Definition 4.28, Lemma 4.29)

The screening note, Definition 4.28 (`def:constants`) and Lemma 4.29
(`lem:Kholds`), adapted to the strip estimate used here (`Scr.Data.stripBound`, from the pointwise
bound `|g| ≤ 2πm + 36n + 1_Ā|Φ|`, which replaces Lemma 4.12). For `0 < m₋ ≤ m₊`:

* `Scr.lam0 m₋ = max 10⁴ (8/m₋)` (internal `λ₀`), `Scr.C1 m₋ = 4·10⁶/m₋²`,
  `Scr.r0 m₊ = min (1/4) (1/(16√m₊))`;
* `Scr.strip_num_of`: **(K1)** `stripBound m ℓ S_d w ≤ (π/2) m w ℓ - 2π` for `w ≥ ℓ ≥ 10⁴`, `mℓ ≥ 8`,
  `S_d ≤ m²ℓ³/125000` (which follows from `S_d ≤ 32ℓ³/C1`);
* `Scr.Asm.Good.card_pcs_le`: `#Z ≤ 6m(d + 8)t` (each piece has mass `1` and density `≤ 3m/2`; the
  pieces lie in the frame `{δ ≤ d + 8}` of area `≤ 4(d + 8)t`);
* `Scr.CS m₋ m₊` and `Scr.Asm.Good.excess_le`: `c_m n_∂ + excess ≤ C_S (ℓ S/ℓt + t ℓt + n_∂)` with
  `S_d = 32 S/ℓt`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

namespace Scr

/-- The internal `λ₀ = max 10⁴ (8/m₋)`. -/
@[expose] noncomputable def lam0 (mLo : ℝ) : ℝ := max 10000 (8 / mLo)

/-- `C₁ = 4·10⁶/m₋²`. -/
@[expose] noncomputable def C1 (mLo : ℝ) : ℝ := 4000000 / mLo ^ 2

/-- The radius of the new charges `r₀ = min (1/4) (1/(16√m₊))`. -/
@[expose] noncomputable def r0 (mHi : ℝ) : ℝ := min (1 / 4) (1 / (16 * √mHi))

/-- A bound for the piece energy `e_P` uniform in `m ∈ [m₋, m₊]`. -/
@[expose] noncomputable def eP (mLo mHi : ℝ) : ℝ := 2 * (2 + (16896 + 1024 / (r0 mHi * √mLo)))

/-- Coefficient of `ℓ S/ℓt`. -/
@[expose] def aS : ℝ := 64 + 1008 * 746688 + 3072

/-- Coefficient of `t ℓt`. -/
@[expose] noncomputable def aT (mLo mHi : ℝ) : ℝ :=
  1008 * (39064896 * mHi ^ 2 + 4096) + 160704 * mHi ^ 2 + 1024 + 24 * mHi * eP mLo mHi

/-- Coefficient of `n_∂`. -/
@[expose] def aN (mHi : ℝ) : ℝ := 12 + mHi

/-- **The constant `C_S`**. -/
@[expose] noncomputable def CS (mLo mHi : ℝ) : ℝ := aS + aT mLo mHi + aN mHi

theorem r0_pos {mHi : ℝ} (hmHi : 0 < mHi) : 0 < r0 mHi := by
  have : 0 < √mHi := Real.sqrt_pos.2 hmHi
  unfold r0
  exact lt_min (by norm_num) (by positivity)

theorem r0_le (mHi : ℝ) : r0 mHi ≤ 1 / 4 := min_le_left _ _

theorem r0_le' {m mHi : ℝ} (hm : 0 < m) (hmHi : m ≤ mHi) : r0 mHi ≤ 1 / (16 * √m) := by
  refine (min_le_right _ _).trans ?_
  have h1 : 0 < √m := Real.sqrt_pos.2 hm
  exact one_div_le_one_div_of_le (by positivity) (by gcongr)

theorem eP_pos {mLo mHi : ℝ} (hmLo : 0 < mLo) (hm : mLo ≤ mHi) : 0 < eP mLo mHi := by
  have := r0_pos (hmLo.trans_le hm)
  have : 0 < √mLo := Real.sqrt_pos.2 hmLo
  unfold eP; positivity

theorem CS_pos {mLo mHi : ℝ} (hmLo : 0 < mLo) (hm : mLo ≤ mHi) : 0 < CS mLo mHi := by
  have := eP_pos hmLo hm
  have : 0 < mHi := hmLo.trans_le hm
  unfold CS aS aT aN; positivity

theorem C1_pos {mLo : ℝ} (hmLo : 0 < mLo) : 0 < C1 mLo := by unfold C1; positivity

theorem lam0_pos (mLo : ℝ) : 0 < lam0 mLo := lt_max_of_lt_left (by norm_num)

/-! ### (K1) -/

/-- **(K1)** in the form `strip_num` of `Scr.Data.Hyp`. -/
theorem strip_num_of {m ℓ Sd w : ℝ} (hm : 0 < m) (hℓ : 10000 ≤ ℓ) (hmℓ : 8 ≤ m * ℓ) (hw : ℓ ≤ w)
    (hSd : Sd ≤ m ^ 2 * ℓ ^ 3 / 125000) :
    Data.stripBound m ℓ Sd w ≤ π / 2 * m * w * ℓ - 2 * π := by
  have hℓ0 : 0 < ℓ := by linarith
  have hw0 : 0 < w := by linarith
  have hmℓ0 : 0 < m * ℓ := by positivity
  have hπ := Real.two_le_pi
  have hπ4 := Real.pi_le_four
  have e : Data.stripBound m ℓ Sd w = 18 * π * m * w + 333 / 1000 * (m * w * ℓ) +
      820125 * π ^ 2 * (m * w / ℓ) + 92125 / 4 * (Sd / (m * ℓ)) := by
    unfold Data.stripBound; field_simp; ring
  rw [e]
  set P := m * w * ℓ
  have hP : 0 < P := by positivity
  have hmw : 0 < m * w := by positivity
  -- the four terms
  have b1 : 18 * π * m * w ≤ 72 / 10000 * P := by
    have : m * w * 10000 ≤ P := by
      have := mul_le_mul_of_nonneg_left hℓ hmw.le
      simp only [P]; linarith
    nlinarith
  have b2 : 820125 * π ^ 2 * (m * w / ℓ) ≤ 820125 * 16 / 100000000 * P := by
    have hπ2 : π ^ 2 ≤ 16 := by nlinarith
    have h1 : m * w / ℓ ≤ P / 100000000 := by
      rw [div_le_div_iff₀ hℓ0 (by norm_num)]
      have : (10000 : ℝ) * 10000 ≤ ℓ * ℓ := by nlinarith
      have := mul_le_mul_of_nonneg_left this hmw.le
      simp only [P]; linarith
    have h2 : 0 ≤ m * w / ℓ := by positivity
    calc 820125 * π ^ 2 * (m * w / ℓ) ≤ 820125 * 16 * (m * w / ℓ) := by gcongr
      _ ≤ 820125 * 16 * (P / 100000000) := by gcongr
      _ = _ := by ring
  have b3 : 92125 / 4 * (Sd / (m * ℓ)) ≤ 92125 / 4 / 125000 * P := by
    have h1 : Sd / (m * ℓ) ≤ P / 125000 := by
      rw [div_le_iff₀ hmℓ0]
      have : m * ℓ * ℓ ≤ P := by
        have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ m * ℓ)
        simp only [P]; linarith
      calc Sd ≤ m ^ 2 * ℓ ^ 3 / 125000 := hSd
        _ = (m * ℓ * ℓ) * (m * ℓ) / 125000 := by ring
        _ ≤ P * (m * ℓ) / 125000 := by gcongr
        _ = _ := by ring
    calc 92125 / 4 * (Sd / (m * ℓ)) ≤ 92125 / 4 * (P / 125000) := by gcongr
      _ = _ := by ring
  have b4 : 2 * π ≤ 1 / 10000 * P := by
    have : 80000 ≤ P := by
      have := mul_le_mul hmℓ hw hℓ0.le hmℓ0.le
      have h2 : (8 : ℝ) * 10000 ≤ 8 * w := by linarith
      simp only [P]; linarith
    linarith
  have hP2 : π / 2 * m * w * ℓ = π / 2 * P := by simp only [P]; ring
  rw [hP2]
  nlinarith

namespace Asm

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

/-- `#Z ≤ 6m(d + 8)t`. -/
theorem card_pcs_le : (A.pcs.card : ℝ) ≤ 6 * D.m * (D.d + 8) * D.t := by
  have hm := h.m_pos
  -- each piece has area `≥ 2/(3m)`
  have hpiece : ∀ i ∈ A.pcs, 1 ≤ 3 * D.m / 2 * volume.real (A.pc i).carrier := by
    intro i hi
    have hP := hA.isFillerPiece h hi
    have hfin : volume (A.pc i).carrier ≠ ⊤ := (A.pc i).isCompact_carrier.measure_lt_top.ne
    rw [← hP.mass]
    calc ∫ x in (A.pc i).carrier, A.μ D i x ≤ ∫ x in (A.pc i).carrier, 3 * D.m / 2 := by
          refine setIntegral_mono_ae_restrict hP.integrableOn (integrableOn_const hfin) ?_
          exact (ae_restrict_iff' (A.pc i).measurableSet_carrier).2
            (hP.bound.mono fun x hx hxs => (hx hxs).2)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  -- the pieces fill at most the frame
  have hsum : ∑ i ∈ A.pcs, volume (A.pc i).carrier ≤ ENNReal.ofReal (4 * (D.d + 8 - 0) * D.t) := by
    rw [← measure_biUnion_finset₀ (fun i hi i' hi' hne => hA.volume_pc_inter h hi hi' hne)
      (fun i _ => (A.pc i).measurableSet_carrier.nullMeasurableSet)]
    refine (measure_mono fun x hx => ?_).trans
      (Data.volume_band_le (D := D) le_rfl (by linarith [h.d_pos]) h.t_pos.le)
    rw [mem_iUnion₂] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hA.col_subset_frame h (Good.col_mem_cols hi) (hA.pc_subset_col hi hxi)
  have hfin : ∀ i ∈ A.pcs, volume (A.pc i).carrier ≠ ⊤ := fun i _ =>
    (A.pc i).isCompact_carrier.measure_lt_top.ne
  have hreal : ∑ i ∈ A.pcs, volume.real (A.pc i).carrier ≤ 4 * (D.d + 8) * D.t := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
    rw [ENNReal.toReal_sum hfin, ENNReal.toReal_ofReal (by nlinarith [h.d_pos, h.t_pos])] at this
    simpa only [sub_zero, measureReal_def] using this
  calc (A.pcs.card : ℝ) = ∑ i ∈ A.pcs, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ A.pcs, 3 * D.m / 2 * volume.real (A.pc i).carrier := Finset.sum_le_sum hpiece
    _ = 3 * D.m / 2 * ∑ i ∈ A.pcs, volume.real (A.pc i).carrier := by rw [Finset.mul_sum]
    _ ≤ 3 * D.m / 2 * (4 * (D.d + 8) * D.t) := by gcongr
    _ = _ := by ring

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
