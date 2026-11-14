/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Spacing
public import SandierSerfaty.Sphere.Ring.PerRow

/-!
# Per-row bounds in a band (sphere note, Proposition 5.12 (ii))

For a band `[lo, hi]` of `Y_n` (`n ≥ 102`) and a row `k ∈ [lo, hi]`, let
`d = min(k - lo + 1, hi - k + 1)`, so that the rows `k ± m`, `1 ≤ m < d`, are in the band. Then
`B_k ≤ N_k e(x_k) + C + C N_k e^{-d/C}` with an absolute `C` (`Sphere.ringRows_rowB_le_band`).

* `Sphere.ringBand_X_le`: the in-band interaction compared with the lattice term:
  `X_{ij} ≤ -N log |1 - (-1)^{j-i} e^{-(j-i) x_r}| + K₁ (j - i)² e^{-(3/56)(j - i)}`;
* `Sphere.ringCell_le_bulk`: `Cell_k ≤ N_k x_k/12 + 891 e^{198}` on interior rows;
* `Sphere.ringBand_far_le`: the rows outside the band contribute `≤ C_X N e^{-(3/112)(d - 1)}`.
-/

open MeasureTheory Set Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- The constant `K₁ = C_s/(1 - e^{-3/56})` of the in-band comparison. -/
@[expose] noncomputable def ringK1 : ℝ := (2 * (1458 * Real.exp 54) + 5832) / (1 - Real.exp (-(3 / 56)))

theorem one_sub_exp_neg_pos {s : ℝ} (hs : 0 < s) : 0 < 1 - Real.exp (-s) := by
  have : Real.exp (-s) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

theorem ringK1_pos : 0 < ringK1 := by
  unfold ringK1
  have := one_sub_exp_neg_pos (show (0 : ℝ) < 3 / 56 by norm_num)
  positivity

/-- **The in-band comparison.** For band rows `i < j` and `r ∈ [i, j]`,
`X_{ij} ≤ -N log |1 - (-1)^{j-i} e^{-(j-i) x_r}| + K₁ (j - i)² e^{-(3/56)(j - i)}`. -/
theorem ringBand_X_le {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n) (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {i r j : ℕ} (hi' : lo ≤ i) (hir : i ≤ r) (hrj : r ≤ j)
    (hij : i < j) (hj : j ≤ hi) :
    (ringRows n).X i j ≤ -(ringN n lo : ℝ) * ringLogTerm ((ringRows n).aspect r) (j - i) +
      ringK1 * ((j - i : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((j - i : ℕ) : ℝ))) := by
  rw [ringBand_X hn hhi hband hi' hij hj, ringLogTerm_eq]
  set N := (ringN n lo : ℝ)
  set M := j - i
  set x := (ringRows n).aspect r
  set D := N * (ringHeight n j - ringHeight n i)
  have hN0 : (0 : ℝ) < N := by
    have := three_le_ringN (n := n) (by omega) lo (by omega)
    simp only [N]; exact_mod_cast (show 0 < ringN n lo by omega)
  have hbr := ringBand_bulk hlo hband r (by omega) (by omega)
  obtain ⟨hr1, hrK⟩ := ringBulk_interior (by omega) hbr
  have hx : 1 / 3 ≤ x := (ringAspect_mem hn hr1 hrK).1
  have hsp := ringBand_spacing hn hhi hlo hband hi' hir hrj hj
  have hge := ringBand_spacing_ge hn hhi hband hi' hij.le hj
  set s₀ : ℝ := 3 / 56
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hD : s₀ * M ≤ D := hge
  have hMx : s₀ * M ≤ M * x := by
    have : s₀ ≤ x := by simp only [s₀]; linarith
    nlinarith
  have hs0M : 0 < s₀ * M := by simp only [s₀]; positivity
  have hu1 : Real.exp (-(s₀ * M)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hwD : |(-1) ^ M * Real.exp (-D)| ≤ Real.exp (-(s₀ * M)) := by
    rw [abs_neg_one_pow_mul, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (by linarith)
  have hwx : |(-1) ^ M * Real.exp (-(M * x))| ≤ Real.exp (-(s₀ * M)) := by
    rw [abs_neg_one_pow_mul, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (by linarith)
  have hlog := abs_log_one_sub_sub_le hwD hwx hu1
  rw [← mul_sub, abs_neg_one_pow_mul] at hlog
  have hexp := abs_exp_neg_sub_le (p := D) (q := M * x) (a := s₀ * M) hD hMx
  have h1s : 1 - Real.exp (-s₀) ≤ 1 - Real.exp (-(s₀ * M)) := by
    have : Real.exp (-(s₀ * M)) ≤ Real.exp (-s₀) := Real.exp_le_exp.2 (by
      have : s₀ ≤ s₀ * M := by nlinarith
      linarith)
    linarith
  have hs1 : 0 < 1 - Real.exp (-s₀) := one_sub_exp_neg_pos (by norm_num)
  -- `|log(1 - w) - log(1 - w')| ≤ e^{-s₀ M} |D - M x| / (1 - e^{-s₀})`
  have hdiff : |ringLogFn M D - ringLogFn M (M * x)| ≤
      Real.exp (-(s₀ * M)) * |D - M * x| / (1 - Real.exp (-s₀)) := by
    unfold ringLogFn
    calc _ ≤ |Real.exp (-D) - Real.exp (-(M * x))| / (1 - Real.exp (-(s₀ * M))) := hlog
      _ ≤ Real.exp (-(s₀ * M)) * |D - M * x| / (1 - Real.exp (-(s₀ * M))) :=
          div_le_div_of_nonneg_right hexp (by linarith)
      _ ≤ Real.exp (-(s₀ * M)) * |D - M * x| / (1 - Real.exp (-s₀)) :=
          div_le_div_of_nonneg_left (by positivity) hs1 h1s
  have hsp' : |D - M * x| ≤ (2 * (1458 * Real.exp 54) + 5832) * (M : ℝ) ^ 2 / N := hsp
  calc -N * ringLogFn M D = -N * ringLogFn M (M * x) + N * (ringLogFn M (M * x) - ringLogFn M D) := by
        ring
    _ ≤ -N * ringLogFn M (M * x) + N * |ringLogFn M D - ringLogFn M (M * x)| := by
        rw [abs_sub_comm]; gcongr; exact le_abs_self _
    _ ≤ -N * ringLogFn M (M * x) + N * (Real.exp (-(s₀ * M)) *
          ((2 * (1458 * Real.exp 54) + 5832) * (M : ℝ) ^ 2 / N) / (1 - Real.exp (-s₀))) := by
        gcongr
        exact hdiff.trans (by gcongr)
    _ = -N * ringLogFn M (M * x) + ringK1 * (M : ℝ) ^ 2 * Real.exp (-(3 / 56 * (M : ℝ))) := by
        simp only [ringK1, s₀]; field_simp

/-- `Cell_k ≤ N_k x_k/12 + 891 e^{198}` on interior rows. -/
theorem ringCell_le_bulk {n k : ℕ} (hn : 102 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    (ringRows n).cell k ≤ (ringN n k : ℝ) * (ringRows n).aspect k / 12 + 891 * Real.exp 198 := by
  have h := ringCell_le_aspect (by omega) hk1 hk
  obtain ⟨hN3, -, -, -, -, -⟩ := ringInterior_facts (by omega) hk1 hk
  obtain ⟨-, hL⟩ := ringSlab_length_mem (by omega) hk1 hk
  obtain ⟨hs1, hs2⟩ := ringHeight_mem_Icc (by omega) hk1 hk
  obtain ⟨hx1, hx2⟩ := ringAspect_mem hn hk1 hk
  set L := ringQuantile n (ringState n (k + 1)).1 - ringQuantile n (ringState n k).1
  set N := (ringN n k : ℝ)
  set x := (ringRows n).aspect k
  have hN0 : 0 < N := by linarith
  have hL0 : 0 ≤ L := by simp only [L]; linarith
  have h22 : 22 * L ≤ 198 := by
    have : 27 / N ≤ 9 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  have hE : Real.exp (22 * L) - 1 ≤ 22 * L * Real.exp 198 := by
    have := exp_le_one_add_mul_exp (show 0 ≤ 22 * L by linarith)
    have h2 : Real.exp (22 * L) ≤ Real.exp 198 := Real.exp_le_exp.2 h22
    nlinarith
  have hLN : L * N ≤ 27 := by rwa [le_div_iff₀ hN0] at hL
  have hE0 := Real.exp_pos 198
  have : N * x / 12 * (Real.exp (22 * L) - 1) ≤ 891 * Real.exp 198 := by
    calc N * x / 12 * (Real.exp (22 * L) - 1) ≤ N * x / 12 * (22 * L * Real.exp 198) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = x / 12 * 22 * Real.exp 198 * (L * N) := by ring
      _ ≤ 18 / 12 * 22 * Real.exp 198 * 27 := by gcongr
      _ = 891 * Real.exp 198 := by ring
  nlinarith

/-- Rows at index distance `≥ d` from a band row `k` (with the rows `k ± m`, `m < d`, in the band) lie at
distance `≥ (3/56)(d - 1)/N` from `t_k`. -/
theorem ringBand_far_dist {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {k d l : ℕ} (hd1 : 1 ≤ d) (hkd : lo + d ≤ k + 1)
    (hkd' : k + d ≤ hi + 1) (hl : l < ringK n) (hfar : l + d ≤ k ∨ k + d ≤ l) :
    3 / 56 * ((d - 1 : ℕ) : ℝ) / ringN n lo ≤ |ringHeight n k - ringHeight n l| := by
  have hN0 : (0 : ℝ) < ringN n lo := by
    have := three_le_ringN (n := n) (by omega) lo (by omega)
    exact_mod_cast (show 0 < ringN n lo by omega)
  have hmono : ∀ a b, a < b → b < ringK n → ringHeight n a ≤ ringHeight n b := fun a b hab hb => by
    have := ringHeight_sep hn hab hb
    have h3 : (3 : ℝ) ≤ ringN n a := by exact_mod_cast three_le_ringN (by omega) a (by omega)
    have h3' : (3 : ℝ) ≤ ringN n b := by exact_mod_cast three_le_ringN (by omega) b hb
    have : 0 < 3 / (112 * (ringN n a : ℝ)) := by positivity
    have : 0 < 3 / (112 * (ringN n b : ℝ)) := by positivity
    linarith
  rw [div_le_iff₀ hN0]
  rcases hfar with h | h
  · -- `l ≤ k - d < k - d + 1`
    have hge := ringBand_spacing_ge hn hhi hband (i := k + 1 - d) (j := k) (by omega) (by omega)
      (by omega)
    have h2 := hmono l (k + 1 - d) (by omega) (by omega)
    rw [show k - (k + 1 - d) = d - 1 by omega] at hge
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hge := ringBand_spacing_ge hn hhi hband (i := k) (j := k + d - 1) (by omega) (by omega)
      (by omega)
    have h2 := hmono (k + d - 1) l (by omega) hl
    rw [show k + d - 1 - k = d - 1 by omega] at hge
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith)]
    nlinarith

end Sphere

end SandierSerfaty

end
