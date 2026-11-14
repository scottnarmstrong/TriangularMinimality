/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The bookkeeping of Proposition 6.13

`Lower.good_square_algebra`: the real-number inequality that combines the Input 6.3 bound, the square-torus bound, the Young expansion,
the density comparison and the chart factor into the conclusion of Proposition 6.13.
-/

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem good_square_algebra (W L4 logmb mPl mMin p nbR δ t E1 E2 E3 A V G Dn Dq NE F chart CS C C₂ ε mb : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hV0 : 0 ≤ V) (hp0 : 0 ≤ p) (hδ0 : 0 ≤ δ) (ht : 0 ≤ t)
    (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3) (hmP : 0 < mPl) (hmM : 0 < mMin)
    (hCS : 0 ≤ CS) (hC₂ : 0 ≤ C₂)
    (hC : C = 1 + CS + C₂ + Real.pi ^ 2 / 16 * (1 + 7 * mPl) + Real.pi / (2 * mMin))
    (f1 : nbR * (W - Real.pi / 2 * logmb) ≤ NE)
    (f2 : NE ≤ 1 / 2 * G + Real.pi * p * Real.log (1 / 4) - 2 * Real.pi * mb * Dq + CS * (E1 + E2 + E3))
    (f3 : G ≤ (1 + ε) * A + (1 + 1 / ε) * V)
    (f4 : Dn - mb * Dq ≤ p * (Real.pi / 32 * δ) + Real.pi / 32 * mPl * (7 * t))
    (f5 : F = 1 / 2 * A + (Real.pi * Real.log (1 / 4) * p - 2 * Real.pi * Dn))
    (f6 : p * (Real.pi / 2 * (logmb + L4) - Real.pi / 2 * (δ / mMin)) ≤ chart)
    (f7 : (nbR - p) * (W - Real.pi / 2 * logmb) ≥ -(E3 * C₂)) :
    p * (W + Real.pi / 2 * L4) ≤ F + chart + C * (E1 + E2 + E3 + p * δ + t) + ε / 2 * A + C / ε * V := by
  have hpi := Real.pi_pos
  have hpi2 : 0 ≤ Real.pi ^ 2 / 16 := by positivity
  have hq : 0 ≤ Real.pi / (2 * mMin) := by positivity
  have hq2 : 0 ≤ Real.pi ^ 2 / 16 * (1 + 7 * mPl) := by positivity
  have hCge : 1 ≤ C := by rw [hC]; linarith
  -- density comparison
  have g1 : 2 * Real.pi * (Dn - mb * Dq) ≤
      2 * Real.pi * (p * (Real.pi / 32 * δ) + Real.pi / 32 * mPl * (7 * t)) :=
    mul_le_mul_of_nonneg_left f4 (by positivity)
  -- the `V` coefficient
  have hinv : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have g2 : 1 / 2 * (1 + 1 / ε) * V ≤ C / ε * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have : 1 / 2 * (1 + 1 / ε) ≤ 1 / ε := by linarith
    exact this.trans (div_le_div_of_nonneg_right hCge hε.le)
  -- the error coefficients
  have g3 : CS * E1 ≤ C * E1 := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hE1
  have g4 : CS * E2 ≤ C * E2 := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hE2
  have g5 : (CS + C₂) * E3 ≤ C * E3 := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hE3
  have hpδ : 0 ≤ p * δ := mul_nonneg hp0 hδ0
  have g6 : (Real.pi ^ 2 / 16 + Real.pi / (2 * mMin)) * (p * δ) ≤ C * (p * δ) :=
    mul_le_mul_of_nonneg_right (by rw [hC]; linarith [mul_nonneg hpi2 hmP.le]) hpδ
  have g7 : Real.pi ^ 2 / 16 * 7 * mPl * t ≤ C * t :=
    mul_le_mul_of_nonneg_right (by rw [hC]; linarith [mul_nonneg hpi2 hmP.le]) ht
  have g8 : Real.pi / 2 * (δ / mMin) * p = Real.pi / (2 * mMin) * (p * δ) := by
    field_simp
  have g9 : (nbR - p) * (W - Real.pi / 2 * logmb) = nbR * (W - Real.pi / 2 * logmb) -
      p * (W - Real.pi / 2 * logmb) := by ring
  have g10 : Real.pi / 2 * (δ / mMin) * p = p * (Real.pi / 2 * (δ / mMin)) := by ring
  have g11 : 2 * Real.pi * (p * (Real.pi / 32 * δ) + Real.pi / 32 * mPl * (7 * t)) =
      Real.pi ^ 2 / 16 * (p * δ) + Real.pi ^ 2 / 16 * 7 * mPl * t := by ring
  have g12 : 1 / 2 * G ≤ 1 / 2 * ((1 + ε) * A + (1 + 1 / ε) * V) := by linarith
  have g13 : p * (Real.pi / 2 * (logmb + L4) - Real.pi / 2 * (δ / mMin)) =
      p * (Real.pi / 2 * (logmb + L4)) - p * (Real.pi / 2 * (δ / mMin)) := by ring
  have g14 : 2 * Real.pi * (Dn - mb * Dq) = 2 * Real.pi * Dn - 2 * Real.pi * mb * Dq := by ring
  have g15 : C * (E1 + E2 + E3 + p * δ + t) = C * E1 + C * E2 + C * E3 + C * (p * δ) + C * t := by ring
  have g16 : CS * (E1 + E2 + E3) = CS * E1 + CS * E2 + CS * E3 := by ring
  have g17 : (CS + C₂) * E3 = CS * E3 + C₂ * E3 := by ring
  have g18 : (Real.pi ^ 2 / 16 + Real.pi / (2 * mMin)) * (p * δ) =
      Real.pi ^ 2 / 16 * (p * δ) + Real.pi / (2 * mMin) * (p * δ) := by ring
  have g19 : 1 / 2 * ((1 + ε) * A + (1 + 1 / ε) * V) = 1 / 2 * A + ε / 2 * A + 1 / 2 * (1 + 1 / ε) * V := by
    ring
  have g20 : E3 * C₂ = C₂ * E3 := by ring
  rw [f5]
  linarith [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20]

end Lower

end Sphere

end SandierSerfaty

end
