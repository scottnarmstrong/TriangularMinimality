/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The error budget of Theorem 6.14 (pure real arithmetic)

With `R = L²`, `ℓ = ℓ̃ = L`, `ε = L⁴/u` (`u = √n`) and the aggregated bounds of the proof of Theorem 6.14 (number of cells
`N ≲ u²/L⁴`, strip energies, discrepancy sum, number of points outside the good squares, ...), the total error is at most
`K₁ u²/L + K₂ L⁸ u` with `K₁, K₂` depending only on the constants (`Lower.chart_error_le`).  Each step is a separate small
lemma.
-/

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem err_NV0 {cN cV N V0 L u : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u) (hcN : 0 ≤ cN) (hcV : 0 ≤ cV) (_hN0 : 0 ≤ N)
    (hV00 : 0 ≤ V0) (hN : N * L ^ 4 ≤ cN * u ^ 2) (hV0 : V0 * u ^ 2 ≤ cV * L ^ 12) :
    N * V0 ≤ cN * cV * (L ^ 8 * u) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : N * V0 * (L ^ 4 * u ^ 2) ≤ cN * cV * L ^ 8 * (L ^ 4 * u ^ 2) := by
    calc N * V0 * (L ^ 4 * u ^ 2) = (N * L ^ 4) * (V0 * u ^ 2) := by ring
      _ ≤ (cN * u ^ 2) * (cV * L ^ 12) := mul_le_mul hN hV0 (by positivity) (by positivity)
      _ = cN * cV * L ^ 8 * (L ^ 4 * u ^ 2) := by ring
  have h2 : N * V0 ≤ cN * cV * L ^ 8 := le_of_mul_le_mul_right h1 (by positivity)
  have h3 : L ^ 8 ≤ L ^ 8 * u := le_mul_of_one_le_right (by positivity) hu
  exact h2.trans (by
    have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hcN hcV)
    linarith)

theorem err_NL3 {cN N L u : ℝ} (hL : 1 ≤ L) (hN : N * L ^ 4 ≤ cN * u ^ 2) :
    N * L ^ 3 ≤ cN * (u ^ 2 / L) := by
  have hL0 : 0 < L := by linarith
  rw [← mul_div_assoc, le_div_iff₀ hL0]
  calc N * L ^ 3 * L = N * L ^ 4 := by ring
    _ ≤ cN * u ^ 2 := hN

theorem err_NL2 {cN N L u : ℝ} (hL : 1 ≤ L) (hN0 : 0 ≤ N) (hN : N * L ^ 4 ≤ cN * u ^ 2) :
    N * L ^ 2 ≤ cN * (u ^ 2 / L) := by
  have h1 := err_NL3 (u := u) hL hN
  have h2 : N * L ^ 2 ≤ N * L ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num)) hN0
  linarith

theorem err_S {CA G0 L u NV0 cN cV : ℝ} (hL : 1 ≤ L) (_hu : 1 ≤ u) (_hCA : 0 ≤ CA) (hG0 : G0 ≤ CA * u ^ 2)
    (hNV0 : NV0 ≤ cN * cV * (L ^ 8 * u)) {S : ℝ} (hS : S ≤ 48 * G0 / L + 2 * NV0) :
    S ≤ 48 * CA * (u ^ 2 / L) + 2 * (cN * cV) * (L ^ 8 * u) := by
  have hL0 : 0 < L := by linarith
  have h1 : 48 * G0 / L ≤ 48 * CA * (u ^ 2 / L) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hL0.le
  linarith

theorem err_D {CD mP cN F1 N L G0 CA u : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u) (hCD : 0 ≤ CD) (hcN : 0 ≤ cN)
    (hCA : 0 ≤ CA) (hN0 : 0 ≤ N) (hG00 : 0 ≤ G0) (hN : N * L ^ 4 ≤ cN * u ^ 2) (hG0 : G0 ≤ CA * u ^ 2)
    (hF1 : F1 = u ^ 2 / L) (hmP : 0 < mP) {D : ℝ}
    (hD : D ≤ CD * ((1 + mP) * (N * L ^ 2) + Real.sqrt (N * L ^ 2) * Real.sqrt (18 * G0 / L ^ 2))) :
    D ≤ CD * ((1 + mP) * (cN * F1) + Real.sqrt (18 * cN * CA) * F1) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have h3 : N * L ^ 2 ≤ cN * F1 := by rw [hF1]; exact err_NL2 hL hN0 hN
  have a7 : Real.sqrt (N * L ^ 2) * Real.sqrt (18 * G0 / L ^ 2) ≤ Real.sqrt (18 * cN * CA) * F1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have h1 : N * L ^ 2 * (18 * G0 / L ^ 2) = 18 * N * G0 := by field_simp
    rw [h1]
    have h2 : 18 * N * G0 * L ^ 4 ≤ 18 * cN * CA * u ^ 4 := by
      calc 18 * N * G0 * L ^ 4 = 18 * (N * L ^ 4) * G0 := by ring
        _ ≤ 18 * (cN * u ^ 2) * (CA * u ^ 2) := by gcongr
        _ = 18 * cN * CA * u ^ 4 := by ring
    have h3 : 18 * N * G0 ≤ 18 * cN * CA * (u ^ 2 / L ^ 2) ^ 2 := by
      have : 18 * cN * CA * (u ^ 2 / L ^ 2) ^ 2 = 18 * cN * CA * u ^ 4 / L ^ 4 := by field_simp
      rw [this, le_div_iff₀ (by positivity)]
      exact h2
    calc Real.sqrt (18 * N * G0) ≤ Real.sqrt (18 * cN * CA * (u ^ 2 / L ^ 2) ^ 2) := Real.sqrt_le_sqrt h3
      _ = Real.sqrt (18 * cN * CA) * (u ^ 2 / L ^ 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt (18 * cN * CA) * F1 := by
          rw [hF1]
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          exact div_le_div_of_nonneg_left (by positivity) hL0 (by nlinarith)
  refine hD.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hCD
  have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 + mP)
  linarith

theorem err_delta {mP kap δ SP u L : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u) (hmP : 0 < mP) (hkap : 0 < kap)
    (hSP : SP ≤ u ^ 2) (hδ0 : 0 ≤ δ) (hδ : δ * (kap * u) = 4 * mP * L ^ 2) :
    δ * SP ≤ 4 * mP / kap * (L ^ 8 * u) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : δ * SP ≤ δ * u ^ 2 := mul_le_mul_of_nonneg_left hSP hδ0
  have h2 : δ * u ^ 2 = 4 * mP * L ^ 2 * u / kap := by
    field_simp
    linarith [hδ]
  have h3 : 4 * mP * L ^ 2 * u / kap ≤ 4 * mP / kap * (L ^ 8 * u) := by
    rw [div_mul_eq_mul_div, mul_assoc (4 * mP) _ _]
    refine div_le_div_of_nonneg_right ?_ hkap.le
    have : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL (by norm_num)
    have := mul_le_mul_of_nonneg_right this hu0.le
    nlinarith
  linarith

theorem err_eps1 {CA SA L u : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u) (hCA : 0 ≤ CA) (hSA : SA ≤ CA * u ^ 2) :
    L ^ 4 / u / 2 * SA ≤ CA / 2 * (L ^ 8 * u) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : L ^ 4 / u / 2 * SA ≤ L ^ 4 / u / 2 * (CA * u ^ 2) :=
    mul_le_mul_of_nonneg_left hSA (by positivity)
  have h2 : L ^ 4 / u / 2 * (CA * u ^ 2) = CA / 2 * (L ^ 4 * u) := by field_simp
  have hL8 : L ^ 4 ≤ L ^ 8 := pow_le_pow_right₀ hL (by norm_num)
  have h3 : L ^ 4 * u ≤ L ^ 8 * u := mul_le_mul_of_nonneg_right hL8 hu0.le
  have := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ CA / 2)
  linarith

theorem err_eps2 {C cN cV SV N V0 L u : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u) (hC : 0 ≤ C) (hcN : 0 ≤ cN)
    (hcV : 0 ≤ cV) (hSV : SV ≤ N * V0) (hNV0 : N * V0 ≤ cN * cV * L ^ 8) (_hSV0 : 0 ≤ SV) :
    C / (L ^ 4 / u) * SV ≤ C * cN * cV * (L ^ 8 * u) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : C / (L ^ 4 / u) * SV ≤ C / (L ^ 4 / u) * (cN * cV * L ^ 8) :=
    mul_le_mul_of_nonneg_left (hSV.trans hNV0) (by positivity)
  have h3 : C / (L ^ 4 / u) * (cN * cV * L ^ 8) = C * cN * cV * (L ^ 4 * u) := by field_simp
  have hL8 : L ^ 4 ≤ L ^ 8 := pow_le_pow_right₀ hL (by norm_num)
  have h4 : L ^ 4 * u ≤ L ^ 8 * u := mul_le_mul_of_nonneg_right hL8 hu0.le
  have := mul_le_mul_of_nonneg_left h4 (mul_nonneg (mul_nonneg hC hcN) hcV)
  linarith

theorem err_rest {Cscr kap cN cV S rest N ρ L u F1 F2 CA : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u)
    (hCscr : 1 ≤ Cscr) (hkap : 0 < kap) (hN0 : 0 ≤ N) (hN : N * L ^ 4 ≤ cN * u ^ 2) (_hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 2 * kap * u) (hF1 : F1 = u ^ 2 / L) (hF2 : F2 = L ^ 8 * u)
    (hS : S ≤ 48 * CA * F1 + 2 * (cN * cV) * F2)
    (hrest : rest ≤ 2 * Cscr * S + 7 * (L ^ 2 * N) + 16 * ρ * (L ^ 2 + 1)) :
    rest ≤ 2 * Cscr * (48 * CA * F1 + 2 * (cN * cV) * F2) + 7 * (cN * F1) + 64 * kap * F2 := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have h1 : 16 * ρ * (L ^ 2 + 1) ≤ 64 * kap * F2 := by
    have h8 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL (by norm_num)
    have : L ^ 2 + 1 ≤ 2 * L ^ 8 := by
      have : (1 : ℝ) ≤ L ^ 8 := one_le_pow₀ hL
      linarith
    have h2 : 16 * ρ * (L ^ 2 + 1) ≤ 16 * (2 * kap * u) * (2 * L ^ 8) := by gcongr
    have h3 : 16 * (2 * kap * u) * (2 * L ^ 8) = 64 * kap * F2 := by rw [hF2]; ring
    linarith
  have h4 : L ^ 2 * N ≤ cN * F1 := by
    have := err_NL2 (u := u) hL hN0 hN
    rw [← hF1] at this
    linarith [mul_comm (L ^ 2) N]
  have h5 : 2 * Cscr * S ≤ 2 * Cscr * (48 * CA * F1 + 2 * (cN * cV) * F2) :=
    mul_le_mul_of_nonneg_left hS (by linarith)
  linarith

theorem chart_error_le (c1 C Cscr CD mP kap CA cN cV : ℝ) (u L N S Tt D SP SA SV G0 rest V0 ρ δ : ℝ)
    (hc1 : 0 ≤ c1) (hC : 1 ≤ C) (hCscr : 1 ≤ Cscr) (hCD : 0 ≤ CD) (hmP : 0 < mP) (hkap : 0 < kap)
    (hCA : 0 ≤ CA) (hcN : 0 ≤ cN) (hcV : 0 ≤ cV) (hu : 1 ≤ u) (hL : 1 ≤ L)
    (hN0 : 0 ≤ N) (hN : N * L ^ 4 ≤ cN * u ^ 2) (hV00 : 0 ≤ V0) (hV0 : V0 * u ^ 2 ≤ cV * L ^ 12)
    (hS : S ≤ 48 * G0 / L + 2 * (N * V0)) (hG00 : 0 ≤ G0) (hG0 : G0 ≤ CA * u ^ 2)
    (hT : Tt ≤ N * L ^ 2)
    (hD : D ≤ CD * ((1 + mP) * (N * L ^ 2) + Real.sqrt (N * L ^ 2) * Real.sqrt (18 * G0 / L ^ 2)))
    (hSP : SP ≤ u ^ 2) (hSA : SA ≤ CA * u ^ 2) (hSV0 : 0 ≤ SV)
    (hSV : SV ≤ N * V0)
    (hrest : rest ≤ 2 * Cscr * S + 7 * (L ^ 2 * N) + 16 * ρ * (L ^ 2 + 1)) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 2 * kap * u) (hδ0 : 0 ≤ δ) (hδ : δ * (kap * u) = 4 * mP * L ^ 2) :
    c1 * rest + C * (S + L * Tt + D + δ * SP + Tt) + L ^ 4 / u / 2 * SA + C / (L ^ 4 / u) * SV ≤
      (c1 * (2 * Cscr * (48 * CA) + 7 * cN) +
          C * (48 * CA + cN + CD * ((1 + mP) * cN + Real.sqrt (18 * cN * CA)) + cN)) * (u ^ 2 / L) +
        (c1 * (2 * Cscr * (2 * cN * cV) + 64 * kap) + C * (2 * cN * cV + 4 * mP / kap) + CA / 2 +
          C * cN * cV) * (L ^ 8 * u) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hNV0 := err_NV0 hL hu hcN hcV hN0 hV00 hN hV0
  have hNL2 := err_NL2 (u := u) hL hN0 hN
  have hNL3 := err_NL3 (u := u) hL hN
  have hS' := err_S hL hu hCA hG0 hNV0 hS
  have hD' := err_D (F1 := u ^ 2 / L) hL hu hCD hcN hCA hN0 hG00 hN hG0 rfl hmP hD
  have hδ' := err_delta hL hu hmP hkap hSP hδ0 hδ
  have he1 := err_eps1 hL hu hCA hSA
  have hNV0' : N * V0 ≤ cN * cV * L ^ 8 := by
    have h2 : N * V0 * (L ^ 4 * u ^ 2) ≤ cN * cV * L ^ 8 * (L ^ 4 * u ^ 2) := by
      calc N * V0 * (L ^ 4 * u ^ 2) = (N * L ^ 4) * (V0 * u ^ 2) := by ring
        _ ≤ (cN * u ^ 2) * (cV * L ^ 12) := mul_le_mul hN hV0 (by positivity) (by positivity)
        _ = cN * cV * L ^ 8 * (L ^ 4 * u ^ 2) := by ring
    exact le_of_mul_le_mul_right h2 (by positivity)
  have he2 := err_eps2 hL hu hC0 hcN hcV hSV hNV0' hSV0
  have hrest' := err_rest (F1 := u ^ 2 / L) (F2 := L ^ 8 * u) hL hu hCscr hkap hN0 hN hρ0 hρ rfl rfl hS' hrest
  have hF1 : 0 ≤ u ^ 2 / L := by positivity
  have hF2 : 0 ≤ L ^ 8 * u := by positivity
  have hLT : L * Tt ≤ cN * (u ^ 2 / L) :=
    calc L * Tt ≤ L * (N * L ^ 2) := mul_le_mul_of_nonneg_left hT hL0.le
      _ = N * L ^ 3 := by ring
      _ ≤ cN * (u ^ 2 / L) := hNL3
  have hTt : Tt ≤ cN * (u ^ 2 / L) := hT.trans hNL2
  have b1 : c1 * rest ≤ c1 * (2 * Cscr * (48 * CA * (u ^ 2 / L) + 2 * (cN * cV) * (L ^ 8 * u)) +
      7 * (cN * (u ^ 2 / L)) + 64 * kap * (L ^ 8 * u)) := mul_le_mul_of_nonneg_left hrest' hc1
  have b2 : C * (S + L * Tt + D + δ * SP + Tt) ≤
      C * ((48 * CA * (u ^ 2 / L) + 2 * (cN * cV) * (L ^ 8 * u)) + cN * (u ^ 2 / L) +
        CD * ((1 + mP) * (cN * (u ^ 2 / L)) + Real.sqrt (18 * cN * CA) * (u ^ 2 / L)) +
        4 * mP / kap * (L ^ 8 * u) + cN * (u ^ 2 / L)) := by
    refine mul_le_mul_of_nonneg_left ?_ hC0
    linarith
  have e : c1 * (2 * Cscr * (48 * CA * (u ^ 2 / L) + 2 * (cN * cV) * (L ^ 8 * u)) +
      7 * (cN * (u ^ 2 / L)) + 64 * kap * (L ^ 8 * u)) +
      C * ((48 * CA * (u ^ 2 / L) + 2 * (cN * cV) * (L ^ 8 * u)) + cN * (u ^ 2 / L) +
        CD * ((1 + mP) * (cN * (u ^ 2 / L)) + Real.sqrt (18 * cN * CA) * (u ^ 2 / L)) +
        4 * mP / kap * (L ^ 8 * u) + cN * (u ^ 2 / L)) +
      CA / 2 * (L ^ 8 * u) + C * cN * cV * (L ^ 8 * u) =
      (c1 * (2 * Cscr * (48 * CA) + 7 * cN) +
          C * (48 * CA + cN + CD * ((1 + mP) * cN + Real.sqrt (18 * cN * CA)) + cN)) * (u ^ 2 / L) +
        (c1 * (2 * Cscr * (2 * cN * cV) + 64 * kap) + C * (2 * cN * cV + 4 * mP / kap) + CA / 2 +
          C * cN * cV) * (L ^ 8 * u) := by ring
  linarith [b1, b2, he1, he2, e]

end Lower

end Sphere

end SandierSerfaty

end
