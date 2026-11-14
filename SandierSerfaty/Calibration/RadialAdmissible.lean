/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SeriesB
public import SandierSerfaty.Dual.RadialData
public import SandierSerfaty.Dual.Separated

/-!
# The calibration's radial data as a `Dual.RadialData` term, and its admissibility

Paper `cal:radial-data` (`cal:radial-endpoints` and the paragraph after it), and the hypotheses
`(dual:radial-origin)`–`(dual:radial-sum)` of paper §3.

* `radialData : Dual.RadialData ℕ` is `(B, k, D)` from `Cal.*`;
* `radialData_isAdmissible hd : radialData.IsAdmissible d₀` for **every** `d₀ > 0`: `six_le`, `C¹` of `B`
  and `D_i` (they are `C²`), the origin expansion (`radial_origin`) and the summable majorant of
  `(1 + k_i)|D_i| + t|D_i'|` on `[d₀, T₀]` (from `exists_D_majorant`);
* the instances `d₀ = b`, `d₀ = p`, and the separation scale `d₀ = dStar = 1/(2√π)` used later.

**Which `d₀`?** The paper states `(dual:radial-sum)` "for every `d₀ > 0`" (paper `cal:radial-data` and the paragraph after it: the omitted modes
are bounded by `(1 + k_i + T₀) w_{k_i}`, the retained ones are finitely many), so the radial hypotheses hold
at `d₀ = dStar` itself; no restriction to `b` or `p` is needed. The scale `b` enters later (the certificate
works on `d ≥ b`) and `b < dStar` (`b_lt_dStar`), so any `d₀ ≤ b` is also `≤ dStar`
(`SectorToEnergy` needs `d₀ ≤ dStar`).
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

/-- The radial data `(B, k, D)` of the calibration. -/
@[expose] noncomputable def radialData : Dual.RadialData ℕ where
  B := B
  k := k
  D := D

/-- **`dual:radial-sum`** for the calibration data, at every `d₀ > 0`. -/
theorem radialData_summable {d₀ : ℝ} (hd : 0 < d₀) :
    ∀ T₀ > d₀, ∃ M : ℕ → ℝ, Summable M ∧ ∀ i, ∀ t ∈ Icc d₀ T₀,
      (1 + (k i : ℝ)) * |D i t| + t * |deriv (D i) t| ≤ M i := by
  intro T₀ hT
  obtain ⟨M, hM0, hMs, hMb⟩ := exists_D_majorant hd
  refine ⟨fun i => (1 + (k i : ℝ) + T₀) * M i, ?_, fun i t ht => ?_⟩
  · have h0 := hMs 0
    have h1 := hMs 1
    simp only [pow_zero, one_mul, pow_one] at h0 h1
    refine ((h0.mul_left (1 + T₀)).add h1).congr fun i => ?_
    ring
  · obtain ⟨b0, b1, -⟩ := hMb i t ht.1
    have h1 : 0 ≤ (k i : ℝ) := Nat.cast_nonneg _
    have ht0 : 0 ≤ t := hd.le.trans ht.1
    calc (1 + (k i : ℝ)) * |D i t| + t * |deriv (D i) t|
        ≤ (1 + (k i : ℝ)) * M i + T₀ * M i := add_le_add
          (mul_le_mul_of_nonneg_left b0 (by linarith)) (mul_le_mul ht.2 b1 (abs_nonneg _) (by linarith))
      _ = (1 + (k i : ℝ) + T₀) * M i := by ring

/-- **Admissibility of the calibration radial data** (`dual:radial-origin`, `dual:radial-sum`, `C¹`
regularity, `k_i ≥ 6`), at every lower distance `d₀ > 0`. -/
theorem radialData_isAdmissible {d₀ : ℝ} (hd : 0 < d₀) : radialData.IsAdmissible d₀ where
  six_le := six_le_k
  contDiffOn_B := contDiffOn_B.of_le (by norm_num)
  contDiffOn_D i := (contDiffOn_D i).of_le (by norm_num)
  origin := by
    obtain ⟨C, hC⟩ := radial_origin
    exact ⟨C, 1 / 2, by norm_num, fun r hr => hC r hr⟩
  summable := radialData_summable hd

theorem b_lt_dStar : b < Dual.dStar := by
  unfold Dual.dStar b
  have hs := Real.sqrt_pos.2 Real.pi_pos
  have hsq : √Real.pi < 100000 / 56418 := by
    rw [Real.sqrt_lt' (by norm_num)]
    have := Real.pi_lt_d4
    norm_num at this ⊢
    linarith
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- Admissibility at `d₀ = p` (the regular hexagon). -/
theorem radialData_isAdmissible_p : radialData.IsAdmissible p := radialData_isAdmissible p_pos

end Calibration

end SandierSerfaty

end
