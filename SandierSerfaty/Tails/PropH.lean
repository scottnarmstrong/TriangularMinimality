/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropS

/-!
# Propagation to the sector functions `H_k` (paper `tail:H-estimate`)

`H_k = Hk B₁ k` (`Calibration.H k`), `H̃_k = Hk B̃₁ k` (`Trunc.H k`), and `ΔH_k = Hk ΔB₁ k = H_k - H̃_k`
(`Hk_B₁_eq`). The estimate `tail:H-estimate`: for `b ≤ t ≤ l`,
`|H_k|_{2,t} ≤ 6 (k+1) (6000 + W_*)` (`jn_Hk_B₁_le`); the bound `|ΔH_k|_{2,t} ≤ 6 (k+1) W_*` of the
difference is not needed here.
-/

open Set Filter MeasureTheory

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- `B₁' = B̃₁' + ΔB''`. -/
@[expose] noncomputable def B1d (r : ℝ) : ℝ := Bt1d r + dU2 r

theorem hasDerivAt_B₁ {x : ℝ} (hx : 0 < x) : HasDerivAt B₁ (B1d x) x := by
  have h := (jet_Bt1.d0 x hx).add (jet_dU.d1 x hx)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact B₁_eq_trunc_add hy

theorem abs_B₁_le' (hc : FiniteCore) {r : ℝ} (hr : 0 < r) : |B₁ r| ≤ 6000 + ww ∧ |B1d r| ≤ 6000 + ww := by
  have h := B₁_bound_all hc hr
  have d := dU_bound hr
  have h1 := abs_nonneg (Trunc.B₁ r)
  have h2 := abs_nonneg (Bt1d r)
  refine ⟨?_, ?_⟩
  · rw [B₁_eq_trunc_add hr]
    exact (abs_add_le _ _).trans (by linarith [d.2.1])
  · unfold B1d
    exact (abs_add_le _ _).trans (by linarith [d.2.2])

theorem Hk_B₁_eq (hc : FiniteCore) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Hk B₁ k t = Hk Trunc.B₁ k t + Hk dU1 k t := by
  unfold Hk
  rw [← mul_add, ← intervalIntegral.integral_add
    (intervalIntegrable_of_nearZero ((nearZero_Trunc_B₁ hc).mul_pow_self k) ht)
    (intervalIntegrable_of_nearZero (nearZero_dU1.mul_pow_self k) ht)]
  congr 1
  refine integral_congr_pos ht fun r hr => ?_
  rw [B₁_eq_trunc_add hr]; ring

theorem jet_Hk_trunc (hc : FiniteCore) (k : ℕ) :
    Jet2 (Ioi 0) (Ioi 0) (Hk Trunc.B₁ k) (Hd1 Trunc.B₁ k) (Hd2 Trunc.B₁ Bt1d k) :=
  jet_Hk (nearZero_Trunc_B₁ hc) jet_Bt1.d0 k

theorem jet_Hk_dU1 (k : ℕ) : Jet2 (Ioi 0) (Ioi 0) (Hk dU1 k) (Hd1 dU1 k) (Hd2 dU1 dU2 k) :=
  jet_Hk nearZero_dU1 jet_dU.d1 k

theorem jet_Hk_B₁ (hc : FiniteCore) (k : ℕ) :
    Jet2 (Ioi 0) (Ioi 0) (Hk B₁ k) (Hd1 B₁ k) (Hd2 B₁ B1d k) :=
  jet_Hk (nearZero_B₁ hc) (fun _ hx => hasDerivAt_B₁ hx) k

/-! ### The estimates -/

theorem coef_sharp {k : ℕ} {t : ℝ} (h1 : b ≤ t) (h2 : t ≤ l) :
    t / ((k : ℝ) + 1) + 5 / 2 + (k : ℝ) / t ≤ 6 * ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have ht : 0 < t := lt_of_lt_of_le b_pos h1
  have hl := l_lt
  have hb : b = 28209 / 100000 := rfl
  have e1 : t / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have e2 : (k : ℝ) / t ≤ (k : ℝ) / b := div_le_div_of_nonneg_left hk b_pos h1
  have e3 : (k : ℝ) / b ≤ 4 * k := by
    rw [div_le_iff₀ b_pos, hb]; nlinarith
  nlinarith

theorem coef_crude {k : ℕ} {t : ℝ} (h1 : b / 2 ≤ t) (h2 : t ≤ 2) :
    t / ((k : ℝ) + 1) + 5 / 2 + (k : ℝ) / t ≤ 8 * ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ k := by positivity
  have hb2 : 0 < b / 2 := by have := b_pos; positivity
  have ht : 0 < t := lt_of_lt_of_le hb2 h1
  have e1 : t / ((k : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e2 : (k : ℝ) / t ≤ (k : ℝ) / (b / 2) := div_le_div_of_nonneg_left hk hb2 h1
  have e3 : (k : ℝ) / (b / 2) ≤ 8 * k := by
    rw [div_le_iff₀ hb2]; unfold b; nlinarith
  nlinarith

/-- A general `H_k` bound: if `|g| ≤ G` on `(0, ∞)`, `|g'| ≤ G` and `t ∈ [δ, T]`. -/
theorem jn_Hk_le' {g g₁ : ℝ → ℝ} (h : NearZero g) (k : ℕ) {t G : ℝ} (ht : 0 < t)
    (hG : ∀ r ∈ Ioc 0 t, |g r| ≤ G) (hg₁ : |g₁ t| ≤ G) :
    jn (Hk g k) (Hd1 g k) (Hd2 g g₁ k) t ≤ (t / ((k : ℝ) + 1) + 5 / 2 + (k : ℝ) / t) * G := by
  have h0 := jn_Hk_le (g₁ := g₁) h k ht hG
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG t ⟨ht, le_rfl⟩)
  have : (t / ((k : ℝ) + 1) + 5 / 2 + (k : ℝ) / t) * G =
      t * G / ((k : ℝ) + 1) + 5 / 2 * G + (k : ℝ) * G / t := by field_simp
  rw [this]
  linarith

/-- **`tail:H-estimate`**: `|H_k|_{2,t} ≤ 6 (k+1) (6000 + W_*)` on `[b, l]`. -/
theorem jn_Hk_B₁_le (hc : FiniteCore) (k : ℕ) {t : ℝ} (h1 : b ≤ t) (h2 : t ≤ l) :
    jn (Hk B₁ k) (Hd1 B₁ k) (Hd2 B₁ B1d k) t ≤ 6 * ((k : ℝ) + 1) * (6000 + Wstar) := by
  have ht : 0 < t := lt_of_lt_of_le b_pos h1
  have hb : ∀ r, 0 < r → |B₁ r| ≤ 6000 + ww := fun r hr => (abs_B₁_le' hc hr).1
  have := jn_Hk_le' (g₁ := B1d) (nearZero_B₁ hc) k ht (G := 6000 + ww) (fun r hr => hb r hr.1)
    (abs_B₁_le' hc ht).2
  refine this.trans ?_
  have hw := ww_nonneg
  have hW := ww_le_Wstar
  have c := coef_sharp (k := k) h1 h2
  calc _ ≤ (6 * ((k : ℝ) + 1)) * (6000 + ww) := mul_le_mul_of_nonneg_right c (by positivity)
    _ ≤ 6 * ((k : ℝ) + 1) * (6000 + Wstar) := by gcongr

end Tails

end SandierSerfaty

end
