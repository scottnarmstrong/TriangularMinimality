/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenConstants

/-!
# The screening theorem I4 (screening note, Theorems 4.1 and 4.2)

The screening note, §4.6: the proofs of Theorem 4.2 (internal form) and
Theorem 4.1 (the screening theorem I4, `exists_screened_neumannChargeField`).

* `Scr.Asm.Good.total_le`: the excess of Proposition 4.27 plus `c_m n_∂` is at most
  `C_S (ℓc S/ℓt + t ℓt + n_∂)` when `S_d = 32 S/ℓt`;
* `Scr.ScreenConcl`: the conclusion of the screening theorems, for an error bound `B`;
* `Scr.exists_screened_internal`: **Theorem 4.2** (internal `ℓc ≥ λ₀`, `8ℓc ≤ ℓt`, `S ≤ ℓc³ℓt/C₁`):
  choose the good cut `d` (Lemma 4.7), build the screening data (`Scr.Data`, `Scr.Data.Hyp`), the
  column cut and the filler (`Scr.Asm.exists_good`), and collect Lemmas 4.24, 4.25 and
  Proposition 4.27;
* `exists_screened_neumannChargeField`: **Theorem 4.1 (I4)**, with `ℓ₀ = 8λ₀`, `C_scr = 512 C₁`,
  applying Theorem 4.2 to `ℓc/8`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

namespace Scr

/-- The conclusion of the screening theorems with error bound `B`. -/
@[expose] def ScreenConcl (c : ℂ) (t m : ℝ) (N : ℕ) (C : Set ℂ) (α : ℂ → ℝ) (E : ℂ → ℂ) (B : ℝ) :
    Prop :=
  ∃ (Y : Finset ℂ) (ρ : ℂ → ℝ) (E' : ℂ → ℂ),
    Y.card = N ∧ (∀ y ∈ Y, y ∈ interior (sq c t)) ∧
    (∀ y ∈ Y, 0 < ρ y ∧ ρ y ≤ 1 / 4 ∧ closedBall y (ρ y) ⊆ interior (sq c t)) ∧
    (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ρ y + ρ y' ≤ ‖y - y'‖) ∧
    IsNeumannChargeField (sq c t) m Y E' ∧
    locEnergy m (Y : Set ℂ) ρ E' (sq c t) ≤ locEnergy m C α E (sq c t) + ((B : ℝ) : EReal)

theorem ScreenConcl.mono {c : ℂ} {t m : ℝ} {N : ℕ} {C : Set ℂ} {α : ℂ → ℝ} {E : ℂ → ℂ} {B B' : ℝ}
    (h : ScreenConcl c t m N C α E B) (hB : B ≤ B') : ScreenConcl c t m N C α E B' := by
  obtain ⟨Y, ρ, E', h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨Y, ρ, E', h1, h2, h3, h4, h5, h6.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 hB))⟩

/-! ### The final constant chase -/

theorem cQuarter_le {m mHi : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ mHi) : cQuarter m ≤ aN mHi := by
  have hπ := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have hlog : Real.log (1 / 4) = -Real.log 4 := by rw [one_div, Real.log_inv]
  have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : π * Real.log 4 ≤ 12 := by nlinarith
  have h2 : π ^ 2 * m / 16 ≤ mHi := by
    have : π ^ 2 ≤ 16 := by nlinarith
    have := mul_le_mul this hm hm0 (by norm_num)
    linarith
  unfold cQuarter tauM aN
  rw [hlog]
  linarith

theorem N2b_le {m mHi t Sd : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ mHi) (ht : 0 ≤ t) (hSd : 0 ≤ Sd) :
    N2b m t Sd ≤ 5022 * mHi ^ 2 * t + 3 * Sd := by
  have hπ := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have hq : π ^ 2 * m ^ 2 ≤ 16 * mHi ^ 2 :=
    mul_le_mul (by nlinarith) (pow_le_pow_left₀ hm0 hm 2) (by positivity) (by norm_num)
  have hq' : π ^ 2 * m ^ 2 * t ≤ 16 * mHi ^ 2 * t := mul_le_mul_of_nonneg_right hq ht
  have e : N2b m t Sd = 2511 / 8 * (π ^ 2 * m ^ 2 * t) + 81 / 32 * Sd := by unfold N2b; ring
  rw [e]
  linarith

theorem ell_mul_Gb_le {m mHi t ℓ ℓt Sd X1 : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ mHi) (hℓ : 0 < ℓ)
    (ht : 0 ≤ t) (hlt : ℓ * t ≤ t * ℓt) (hX1 : ℓ * Sd = 32 * X1) (hX10 : 0 ≤ X1)
    (h1 : 1 ≤ t * ℓt) :
    ℓ * Gb m t ℓ Sd ≤ 39064896 * mHi ^ 2 * (t * ℓt) + 746688 * X1 + 4096 * (t * ℓt) := by
  have hπ := Real.pi_le_four
  have hπ0 := Real.pi_pos
  have hπ2 : π ^ 2 ≤ 16 := by nlinarith only [hπ, hπ0]
  have hq : π ^ 2 * m ^ 2 ≤ 16 * mHi ^ 2 :=
    mul_le_mul hπ2 (pow_le_pow_left₀ hm0 hm 2) (by positivity) (by norm_num)
  have hq' : π ^ 2 * m ^ 2 * (ℓ * t) ≤ 16 * mHi ^ 2 * (t * ℓt) :=
    mul_le_mul hq hlt (by positivity) (by positivity)
  have e : ℓ * Gb m t ℓ Sd = 2441556 * (π ^ 2 * m ^ 2 * (ℓ * t)) + (7776 * 81 / 32 + 6) * (ℓ * Sd) +
      256 * π ^ 2 := by
    unfold Gb N2b; field_simp; ring
  rw [e, hX1]
  linarith only [hq', hπ2, h1, hX10]

theorem excess_le_real {mLo mHi m t ℓ ℓt S nZ eP' : ℝ} (hmLo : 0 < mLo) (hm1 : mLo ≤ m)
    (hm2 : m ≤ mHi) (hℓ : 36 ≤ ℓ) (hℓℓt : ℓ ≤ ℓt) (ht : 8 * ℓt ≤ t) (hS0 : 0 ≤ S)
    (hnZ : nZ ≤ 12 * mHi * (t * ℓt)) (heP0 : 0 ≤ eP') (heP : eP' ≤ eP mLo mHi) :
    2 * (32 * S / ℓt) + 1008 * ℓ * Gb m t ℓ (32 * S / ℓt) + 32 * N2b m t (32 * S / ℓt) +
        64 * π ^ 2 / ℓ + 2 * nZ * eP' ≤
      aS * (ℓ * S / ℓt) + aT mLo mHi * (t * ℓt) := by
  have hm0 : 0 < m := hmLo.trans_le hm1
  have hmHi : 0 < mHi := hm0.trans_le hm2
  have hℓ0 : 0 < ℓ := by linarith
  have hℓt0 : 0 < ℓt := by linarith
  have ht0 : 0 < t := by linarith
  have hπ := Real.pi_le_four
  have hπ0 := Real.pi_pos
  set σ := S / ℓt with hσ
  set X1 := ℓ * S / ℓt with hX1
  set X2 := t * ℓt with hX2
  have hσ0 : 0 ≤ σ := div_nonneg hS0 hℓt0.le
  have hX1σ : X1 = ℓ * σ := by rw [hX1, hσ, mul_div_assoc]
  have hSd : 32 * S / ℓt = 32 * σ := by rw [hσ, mul_div_assoc]
  have hσX1 : 36 * σ ≤ X1 := by rw [hX1σ]; exact mul_le_mul_of_nonneg_right hℓ hσ0
  have hX10 : 0 ≤ X1 := by linarith
  have h1 : 1 ≤ X2 := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hX2t : t ≤ X2 := le_mul_of_one_le_right ht0.le (by linarith)
  have hlt : ℓ * t ≤ X2 := by rw [mul_comm ℓ t]; exact mul_le_mul_of_nonneg_left hℓℓt ht0.le
  rw [hSd]
  have hG := ell_mul_Gb_le (Sd := 32 * σ) hm0.le hm2 hℓ0 ht0.le hlt (by rw [hX1σ]; ring) hX10 h1
  rw [← hX2] at hG
  have hN := N2b_le hm0.le hm2 ht0.le (by positivity : (0 : ℝ) ≤ 32 * σ)
  have hmt : mHi ^ 2 * t ≤ mHi ^ 2 * X2 := mul_le_mul_of_nonneg_left hX2t (by positivity)
  have hπℓ : 64 * π ^ 2 / ℓ ≤ 1024 * X2 := by
    rw [div_le_iff₀ hℓ0]
    have : π ^ 2 ≤ 16 := by nlinarith only [hπ, hπ0]
    nlinarith only [this, h1, hℓ]
  have hZ : 2 * nZ * eP' ≤ 24 * mHi * eP mLo mHi * X2 := by
    have := mul_le_mul hnZ heP heP0 (by positivity)
    linarith only [this]
  have e1 : 1008 * ℓ * Gb m t ℓ (32 * σ) = 1008 * (ℓ * Gb m t ℓ (32 * σ)) := by ring
  rw [e1]
  unfold aS aT
  linarith only [hG, hN, hmt, hπℓ, hZ, hσX1, hσ0]

namespace Asm

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

/-- **The constant chase** (proof of Theorem 4.2): `c_m n_∂ + excess ≤ C_S (ℓc S/ℓt + t ℓt + n_∂)`. -/
theorem total_le {mLo mHi S : ℝ} (hmLo : 0 < mLo) (hm : D.m ∈ Icc mLo mHi) (hr : D.r₀ = r0 mHi)
    (hS0 : 0 ≤ S) (hSd : D.Sd = 32 * S / D.ℓt) :
    cQuarter D.m * D.nBd + excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card ≤
      CS mLo mHi * (D.ℓ * S / D.ℓt + D.t * D.ℓt + D.nBd) := by
  have hm0 := h.m_pos
  have hmHi : 0 < mHi := hmLo.trans_le (hm.1.trans hm.2)
  have hℓt := h.ℓt_ge
  have hℓ := h.K4
  have hX3 : (0 : ℝ) ≤ D.nBd := Nat.cast_nonneg _
  have hX1 : 0 ≤ D.ℓ * S / D.ℓt := by have := h.ℓ_pos; positivity
  have hX2 : 0 ≤ D.t * D.ℓt := by have := h.t_pos; positivity
  have hc : cQuarter D.m * D.nBd ≤ aN mHi * D.nBd :=
    mul_le_mul_of_nonneg_right (cQuarter_le hm0.le hm.2) hX3
  -- the piece energy
  have hePc : ePiece D.m D.r₀ ≤ eP mLo mHi := by
    rw [hr]
    have hr0 := r0_pos hmHi
    have hsq : √mLo ≤ √D.m := Real.sqrt_le_sqrt hm.1
    have hsq0 : 0 < √mLo := Real.sqrt_pos.2 hmLo
    have hπ := Real.pi_le_four
    have hπ0 := Real.pi_pos
    have h1 : 256 * π / (r0 mHi * √D.m) ≤ 1024 / (r0 mHi * √mLo) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hsq hr0.le
      have h2 : 256 * π * (r0 mHi * √mLo) ≤ 1024 * (r0 mHi * √mLo) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h3 : 1024 * (r0 mHi * √mLo) ≤ 1024 * (r0 mHi * √D.m) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
      linarith
    have h2 : π ^ 2 ≤ 16 := by nlinarith only [hπ, hπ0]
    unfold ePiece eP
    linarith only [h1, h2, hπ]
  have hePc0 : 0 ≤ ePiece D.m D.r₀ := by
    have := h.r₀_pos; unfold ePiece; positivity
  -- the number of new charges
  have hZ' : (A.pcs.card : ℝ) ≤ 12 * mHi * (D.t * D.ℓt) := by
    have hZ := hA.card_pcs_le h
    have h1 : D.d + 8 ≤ 2 * D.ℓt := by linarith [h.d_le]
    have h2 : D.m * (D.d + 8) ≤ mHi * (2 * D.ℓt) :=
      mul_le_mul hm.2 h1 (by linarith [h.d_pos]) hmHi.le
    have h3 : D.m * (D.d + 8) * D.t ≤ mHi * (2 * D.ℓt) * D.t :=
      mul_le_mul_of_nonneg_right h2 h.t_pos.le
    have e1 : 6 * D.m * (D.d + 8) * D.t = 6 * (D.m * (D.d + 8) * D.t) := by ring
    have e2 : 12 * mHi * (D.t * D.ℓt) = 6 * (mHi * (2 * D.ℓt) * D.t) := by ring
    rw [e2]; rw [e1] at hZ; linarith
  have hex := excess_le_real hmLo hm.1 hm.2 h.K4 (by linarith [h.ℓ_le]) h.t_ge hS0 hZ' hePc0 hePc
  have e : excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card = 2 * (32 * S / D.ℓt) +
      1008 * D.ℓ * Gb D.m D.t D.ℓ (32 * S / D.ℓt) + 32 * N2b D.m D.t (32 * S / D.ℓt) +
        64 * π ^ 2 / D.ℓ + 2 * (A.pcs.card : ℝ) * ePiece D.m D.r₀ := by
    rw [excess, hSd]
  have haS : 0 ≤ aS := by unfold aS; norm_num
  have haT : 0 ≤ aT mLo mHi := by
    have := eP_pos hmLo (hm.1.trans hm.2); unfold aT; positivity
  have haN : 0 ≤ aN mHi := by unfold aN; linarith
  have hcoef : aS * (D.ℓ * S / D.ℓt) + aT mLo mHi * (D.t * D.ℓt) + aN mHi * D.nBd ≤
      CS mLo mHi * (D.ℓ * S / D.ℓt + D.t * D.ℓt + D.nBd) := by
    have h1 : aS * (D.ℓ * S / D.ℓt) ≤ CS mLo mHi * (D.ℓ * S / D.ℓt) :=
      mul_le_mul_of_nonneg_right (by unfold CS; linarith) hX1
    have h2 : aT mLo mHi * (D.t * D.ℓt) ≤ CS mLo mHi * (D.t * D.ℓt) :=
      mul_le_mul_of_nonneg_right (by unfold CS; linarith) hX2
    have h3 : aN mHi * D.nBd ≤ CS mLo mHi * D.nBd :=
      mul_le_mul_of_nonneg_right (by unfold CS; linarith) hX3
    rw [mul_add, mul_add]
    linarith
  rw [e]
  linarith

end Good

end Asm

/-! ### Theorem 4.2 -/

/-- **Theorem 4.2** (internal form of the screening theorem). -/
theorem exists_screened_internal {mLo mHi : ℝ} (hmLo : 0 < mLo) {c : ℂ} {t m ℓ ℓt S : ℝ} {N : ℕ}
    {C : Set ℂ} {α : ℂ → ℝ} {E : ℂ → ℂ} (hm : m ∈ Icc mLo mHi) (hN : m * t ^ 2 = N)
    (hℓ : lam0 mLo ≤ ℓ) (hℓt : 8 * ℓ ≤ ℓt) (ht : 8 * ℓt ≤ t)
    (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) (hE : IsChargeField (interior (sq c (t - 1))) m C E)
    (hα : ∀ p ∈ C, 0 < α p ∧ α p ≤ 1 / 4) (hα4 : ∀ p ∈ C, p ∉ sq c (t - 2) → α p = 1 / 4)
    (hdisj : ∀ p ∈ C ∩ sq c (t - 2 * ℓt), ∀ q ∈ C ∩ sq c (t - 2 * ℓt), p ≠ q →
      α p + α q ≤ ‖p - q‖)
    (hL2 : ∫⁻ x in sq c t, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≠ ⊤)
    (hSfin : ∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField C (fun _ => 1 / 4) E x‖ ^ 2) ≠ ⊤)
    (hSdef : S = (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField C (fun _ => 1 / 4) E x‖ ^ 2)).toReal)
    (hSb : S ≤ ℓ ^ 3 * ℓt / C1 mLo) :
    ScreenConcl c t m N C α E
      (CS mLo mHi * (ℓ * S / ℓt + t * ℓt + (C ∩ (sq c t \ sq c (t - 4 * ℓt))).ncard)) := by
  have hm0 : 0 < m := hmLo.trans_le hm.1
  have hmHi : 0 < mHi := hm0.trans_le hm.2
  have hℓ4 : 10000 ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓm : 8 / mLo ≤ ℓ := (le_max_right _ _).trans hℓ
  have hmℓ : 8 ≤ m * ℓ := by
    have h1 : 8 ≤ mLo * ℓ := by rwa [div_le_iff₀' hmLo] at hℓm
    nlinarith [hm.1]
  have hℓt0 : 22 < ℓt := by linarith
  have hS0 : 0 ≤ S := by rw [hSdef]; exact ENNReal.toReal_nonneg
  -- the layer and `Φ`
  set Φ : ℂ → ℂ := truncField C (fun _ => 1 / 4) E with hΦ
  set L : Set ℂ := {x | ℓt / 2 ≤ sqDepth c t x ∧ sqDepth c t x < 2 * ℓt} with hL
  have hLeq : sq c (t - ℓt) \ sq c (t - 4 * ℓt) = L := by
    rw [show t - ℓt = t - 2 * (ℓt / 2) by ring, show t - 4 * ℓt = t - 2 * (2 * ℓt) by ring,
      sq_diff_sq_eq]
  have hLmeas : MeasurableSet L := measurableSet_sqDepth_Ico c t _ _
  set K' : Set ℂ := {x | ℓt / 2 ≤ sqDepth c t x} with hK'
  have hK'sq : K' = sq c (t - 2 * (ℓt / 2)) := by
    ext x; rw [mem_sq_iff_le_sqDepth]; rfl
  have hK'c : IsCompact K' := hK'sq ▸ isCompact_sq _ _
  have hK'U : K' ⊆ interior (sq c (t - 1)) := by
    intro x hx
    rw [show t - 1 = t - 2 * (1 / 2) by ring, mem_interior_sq_iff_lt_sqDepth]
    have : ℓt / 2 ≤ sqDepth c t x := hx
    linarith
  have hΦK : IntegrableOn Φ K' :=
    integrableOn_truncField hC hE.1 (fun _ _ => by norm_num) ⟨1 / 4, fun _ _ => le_rfl⟩ hK'c hK'U
  have hLK : L ⊆ K' := fun x hx => hx.1
  have hΦ'm : AEStronglyMeasurable (L.indicator Φ) volume :=
    (aestronglyMeasurable_indicator_iff hLmeas).2 (hΦK.mono_set hLK).aestronglyMeasurable
  have hLint : ∫⁻ x in L, ENNReal.ofReal (‖L.indicator Φ x‖ ^ 2) =
      ∫⁻ x in L, ENNReal.ofReal (‖Φ x‖ ^ 2) :=
    setLIntegral_congr_fun hLmeas fun x hx => by rw [indicator_of_mem hx]
  -- the good cut
  obtain ⟨d, hd, hRsub, hRd⟩ := exists_goodCut_field (c := c) (t := t) hℓt0 hΦ'm le_rfl
  have hSofReal : ∫⁻ x in L, ENNReal.ofReal (‖Φ x‖ ^ 2) = ENNReal.ofReal S := by
    rw [hSdef, hLeq, ENNReal.ofReal_toReal (hLeq ▸ hSfin)]
  have hSd : ∫⁻ x in goodRing c t d, ENNReal.ofReal (‖Φ x‖ ^ 2) ≤ ENNReal.ofReal (32 * S / ℓt) := by
    have hR : ∫⁻ x in goodRing c t d, ENNReal.ofReal (‖Φ x‖ ^ 2) =
        ∫⁻ x in goodRing c t d, ENNReal.ofReal (‖L.indicator Φ x‖ ^ 2) :=
      setLIntegral_congr_fun (measurableSet_goodRing c t d) fun x hx => by
        rw [indicator_of_mem (hRsub hx)]
    rw [hR]
    refine hRd.trans (le_of_eq ?_)
    rw [hLint, hSofReal, ENNReal.ofReal_div_of_pos (by linarith), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  -- the screening data
  let D : Data := ⟨c, t, m, ℓ, ℓt, d, 32 * S / ℓt, r0 mHi, N, C, α, E⟩
  have hSdle : 32 * S / ℓt ≤ m ^ 2 * ℓ ^ 3 / 125000 := by
    have hC1 : 0 < C1 mLo := C1_pos hmLo
    rw [div_le_iff₀ (by linarith)]
    have h1 : S * C1 mLo ≤ ℓ ^ 3 * ℓt := by rwa [le_div_iff₀ hC1] at hSb
    have h2 : 32 * S = 32 * (S * C1 mLo) * mLo ^ 2 / 4000000 := by
      unfold C1; field_simp
    have h3 : mLo ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hmLo.le hm.1 2
    rw [h2, div_le_iff₀ (by norm_num)]
    have h4 : 32 * (S * C1 mLo) * mLo ^ 2 ≤ 32 * (ℓ ^ 3 * ℓt) * mLo ^ 2 := by gcongr
    have h5 : 32 * (ℓ ^ 3 * ℓt) * mLo ^ 2 ≤ 32 * (ℓ ^ 3 * ℓt) * m ^ 2 := by
      have : 0 ≤ ℓ ^ 3 * ℓt := by positivity
      gcongr
    linarith
  have hD : D.Hyp :=
    { m_pos := hm0
      N_eq := hN
      K2 := by
        change 1 / ℓ ≤ m / 8
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      K4 := by change (36 : ℝ) ≤ ℓ; linarith
      ℓ_le := hℓt
      t_ge := ht
      d_mem := hd
      hC := hC
      hE := hE
      hα := hα
      hα4 := hα4
      hdisj := hdisj
      hL2 := hL2
      Sd_nonneg := by change 0 ≤ 32 * S / ℓt; positivity
      hSd := hSd
      r₀_pos := r0_pos hmHi
      r₀_le := r0_le mHi
      r₀_le' := r0_le' hm0 hm.2
      strip_num := fun w hw => strip_num_of hm0 hℓ4 hmℓ hw.1 hSdle }
  -- the column cut and the filler
  obtain ⟨A, hA⟩ := Asm.exists_good hD
  refine ⟨A.Y D, Asm.rho D, A.E' D, hA.card_Y hD, fun y hy => hA.mem_interior_Q hD hy,
    fun y hy => ⟨(hA.rho_mem hD hy).1, (hA.rho_mem hD hy).2, hA.closedBall_subset_interior hD hy⟩,
    fun y hy y' hy' hne => hA.rho_add_rho_le hD hy hy' hne, hA.isNeumannChargeField hD, ?_⟩
  refine (hA.locEnergy_le hD).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_))
  exact hA.total_le hD hmLo hm rfl hS0 rfl

end Scr

/-! ### Theorem 4.1 (I4) -/

/-- **I4: screening of fields on a square** (screening note, Theorem 4.1; replaces Prop. 7.18 / App. A).
For `0 < m₋ ≤ m₊` there are `ℓ₀, C_scr, C_S > 0` such that every charge field `E` of density
`m ∈ [m₋, m₊]` on `int sq c (t - 1)` with `mt² = N`, `ℓ₀ ≤ ℓc ≤ ℓt`, `8ℓt ≤ t`, truncation radii
`α ≤ 1/4` (equal to `1/4` near the boundary, disjoint in the kept zone `sq c (t - 2ℓt)`), `E_α ∈ L²`
and small strip energy `S ≤ ℓc³ℓt/C_scr` can be replaced by a Neumann charge field `E'` on `sq c t`
with `N` charges and disjoint discs, whose local energy exceeds that of `E` by at most
`C_S (ℓc S/ℓt + t ℓt + n_∂)`. -/
theorem exists_screened_neumannChargeField {mLo mHi : ℝ} (hmLo : 0 < mLo) (hm : mLo ≤ mHi) :
    ∃ ℓ₀ C_scr C_S : ℝ, 0 < ℓ₀ ∧ 0 < C_scr ∧ 0 < C_S ∧
    ∀ (c : ℂ) (t m ℓc ℓt : ℝ) (N : ℕ) (C : Set ℂ) (α : ℂ → ℝ) (E : ℂ → ℂ),
      mLo ≤ m → m ≤ mHi → m * t ^ 2 = N → ℓ₀ ≤ ℓc → ℓc ≤ ℓt → 8 * ℓt ≤ t →
      (∀ R : ℝ, (C ∩ closedBall 0 R).Finite) →
      IsChargeField (interior (sq c (t - 1))) m C E →
      (∀ p ∈ C, 0 < α p ∧ α p ≤ 1 / 4) →
      (∀ p ∈ C, p ∉ sq c (t - 2) → α p = 1 / 4) →
      (∀ p ∈ C ∩ sq c (t - 2 * ℓt), ∀ q ∈ C ∩ sq c (t - 2 * ℓt), p ≠ q → α p + α q ≤ ‖p - q‖) →
      ∫⁻ x in sq c t, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≠ ⊤ →
      let S : ℝ := (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
        ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal
      (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
        ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)) ≠ ⊤ →
      S ≤ ℓc ^ 3 * ℓt / C_scr →
      ∃ (Y : Finset ℂ) (ρ : ℂ → ℝ) (E' : ℂ → ℂ),
        Y.card = N ∧ (∀ y ∈ Y, y ∈ interior (sq c t)) ∧
        (∀ y ∈ Y, 0 < ρ y ∧ ρ y ≤ 1 / 4 ∧ closedBall y (ρ y) ⊆ interior (sq c t)) ∧
        (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ρ y + ρ y' ≤ ‖y - y'‖) ∧
        IsNeumannChargeField (sq c t) m Y E' ∧
        locEnergy m (Y : Set ℂ) ρ E' (sq c t) ≤
          locEnergy m C α E (sq c t) +
            ((C_S * (ℓc * S / ℓt + t * ℓt + (C ∩ (sq c t \ sq c (t - 4 * ℓt))).ncard) : ℝ) :
              EReal) := by
  refine ⟨8 * Scr.lam0 mLo, 512 * Scr.C1 mLo, Scr.CS mLo mHi, by
    have := Scr.lam0_pos mLo; positivity, by have := Scr.C1_pos hmLo; positivity,
    Scr.CS_pos hmLo hm, ?_⟩
  intro c t m ℓc ℓt N C α E hm1 hm2 hN hℓ₀ hℓc ht hC hE hα hα4 hdisj hL2 S hSfin hSb
  have hℓc0 : 0 < ℓc := (mul_pos (by norm_num) (Scr.lam0_pos mLo)).trans_le hℓ₀
  have hℓt0 : 0 < ℓt := hℓc0.trans_le hℓc
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hint := Scr.exists_screened_internal (mHi := mHi) hmLo (ℓ := ℓc / 8) (S := S) ⟨hm1, hm2⟩ hN
    (by linarith) (by linarith) ht hC hE hα hα4 hdisj hL2 hSfin rfl (by
      have hC1 := Scr.C1_pos hmLo
      calc S ≤ ℓc ^ 3 * ℓt / (512 * Scr.C1 mLo) := hSb
        _ = (ℓc / 8) ^ 3 * ℓt / Scr.C1 mLo := by field_simp; ring)
  refine hint.mono ?_
  have hCS := Scr.CS_pos hmLo hm
  gcongr
  linarith

end SandierSerfaty.Screening

end
