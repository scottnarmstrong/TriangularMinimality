/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.InBand

/-!
# In-band spacing and the in-band interaction (sphere note, Lemma 5.11)

For a band `[lo, hi]` with count `N` (`n ≥ 102`):

* `Sphere.ringBand_spacing`: **Lemma 5.11**: for `lo ≤ i ≤ r ≤ j ≤ hi`,
  `|N (t_j - t_i) - (j - i) x_r| ≤ C_s (j - i)²/N` (`C_s = 2 · 1458 e^{54} + 5832`);
* `Sphere.ringBand_spacing_ge`: `N (t_j - t_i) ≥ (3/56)(j - i)`;
* `Sphere.ringBand_X`: **Lemma 5.11, the exact formula**: for band rows `i < j`,
  `X_{ij} = -N log |1 - (-1)^{j-i} e^{-N (t_j - t_i)}|`.
-/

open MeasureTheory Set Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `|x_q - x_r| ≤ 5832 m/N` along a band whenever `|q - r| ≤ m`. -/
theorem ringBand_aspect_drift' {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n)
    (hlo : RingBulk n lo) (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {q r : ℕ} (hq : lo ≤ q)
    (hqh : q ≤ hi) (hr : lo ≤ r) (hrh : r ≤ hi) {m : ℕ} (hm : q ≤ r + m) (hm' : r ≤ q + m) :
    |(ringRows n).aspect q - (ringRows n).aspect r| ≤ 5832 * m / ringN n lo := by
  have hN0 : (0 : ℝ) < ringN n lo := by
    exact_mod_cast (show 0 < ringN n lo by
      have := three_le_ringN (n := n) (by omega) lo (by omega); omega)
  rcases le_total q r with h | h
  · refine (ringBand_aspect_drift hn hhi hlo hband hq h hrh).trans ?_
    gcongr; exact_mod_cast (by omega : r - q ≤ m)
  · rw [abs_sub_comm]
    refine (ringBand_aspect_drift hn hhi hlo hband hr h hqh).trans ?_
    gcongr; exact_mod_cast (by omega : q - r ≤ m)

/-- One gap of a band: `|N (t_{Q+1} - t_Q) - x_r| ≤ C_s m/N` when `|Q - r|, |Q + 1 - r| ≤ m`. -/
theorem ringBand_gap {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n) (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {Q r m : ℕ} (hQ : lo ≤ Q) (hQh : Q + 1 ≤ hi)
    (hr : lo ≤ r) (hrh : r ≤ hi) (hm1 : 1 ≤ m) (h1 : Q ≤ r + m) (h2 : r ≤ Q + m) (h3 : Q + 1 ≤ r + m) :
    |(ringN n lo : ℝ) * (ringHeight n (Q + 1) - ringHeight n Q) - (ringRows n).aspect r| ≤
      (2 * (1458 * Real.exp 54) + 5832) * m / ringN n lo := by
  set N := (ringN n lo : ℝ)
  have hN0 : (0 : ℝ) < N := by
    have := three_le_ringN (n := n) (by omega) lo (by omega)
    simp only [N]; exact_mod_cast (show 0 < ringN n lo by omega)
  have hbQ := ringBand_bulk hlo hband Q hQ (by omega)
  have hbQ1 := ringBand_bulk hlo hband (Q + 1) (by omega) hQh
  obtain ⟨hQ1, hQK⟩ := ringBulk_interior (by omega) hbQ
  obtain ⟨-, hQK1⟩ := ringBulk_interior (by omega) hbQ1
  have hNQ : ringN n Q = ringN n lo := ringBand_N hband Q hQ (by omega)
  have hNQ1 : ringN n (Q + 1) = ringN n lo := ringBand_N hband (Q + 1) (by omega) hQh
  obtain ⟨-, a1⟩ := ringHalf_sub_le hn hQ1 hQK
  obtain ⟨a2, -⟩ := ringHalf_sub_le (n := n) (q := Q + 1) hn (by omega) hQK1
  rw [hNQ] at a1
  rw [hNQ1] at a2
  have d1 := ringBand_aspect_drift' hn hhi hlo hband (q := Q) (r := r) (m := m) hQ (by omega) hr hrh
    h1 h2
  have d2 := ringBand_aspect_drift' hn hhi hlo hband (q := Q + 1) (r := r) (m := m) (by omega) hQh hr
    hrh h3 (by omega)
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set β := ringQuantile n (ringState n (Q + 1)).1
  set xQ := (ringRows n).aspect Q
  set xQ1 := (ringRows n).aspect (Q + 1)
  set xr := (ringRows n).aspect r
  set u1 := N * (β - ringHeight n Q) - xQ / 2
  set u2 := N * (ringHeight n (Q + 1) - β) - xQ1 / 2
  have e : N * (ringHeight n (Q + 1) - ringHeight n Q) - xr = u1 + u2 + (xQ - xr) / 2 + (xQ1 - xr) / 2 := by
    simp only [u1, u2]; ring
  rw [e]
  have b : |u1 + u2 + (xQ - xr) / 2 + (xQ1 - xr) / 2| ≤ |u1| + |u2| + |xQ - xr| / 2 + |xQ1 - xr| / 2 := by
    have t1 := abs_add_le (u1 + u2 + (xQ - xr) / 2) ((xQ1 - xr) / 2)
    have t2 := abs_add_le (u1 + u2) ((xQ - xr) / 2)
    have t3 := abs_add_le u1 u2
    rw [abs_div, abs_two] at t1 t2
    linarith
  have hE := Real.exp_pos 54
  have hb1 : 1458 * Real.exp 54 / N ≤ 1458 * Real.exp 54 * m / N := by
    apply div_le_div_of_nonneg_right _ hN0.le; nlinarith
  have h' : (2 * (1458 * Real.exp 54) + 5832) * m / N =
      2 * (1458 * Real.exp 54 * m / N) + 5832 * m / N := by ring
  have h'' : 5832 * (m : ℝ) / N / 2 + 5832 * m / N / 2 = 5832 * m / N := by ring
  linarith

/-- **Lemma 5.11 (in-band spacing).** For `lo ≤ i ≤ r ≤ j ≤ hi` in a band with count `N`,
`|N (t_j - t_i) - (j - i) x_r| ≤ C_s (j - i)²/N`, `C_s = 2 · 1458 e^{54} + 5832`. -/
theorem ringBand_spacing {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n) (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {i r j : ℕ} (hi' : lo ≤ i) (hir : i ≤ r)
    (hrj : r ≤ j) (hj : j ≤ hi) :
    |(ringN n lo : ℝ) * (ringHeight n j - ringHeight n i) - ((j - i : ℕ) : ℝ) * (ringRows n).aspect r| ≤
      (2 * (1458 * Real.exp 54) + 5832) * ((j - i : ℕ) : ℝ) ^ 2 / ringN n lo := by
  set N := (ringN n lo : ℝ)
  set m := j - i
  set C := 2 * (1458 * Real.exp 54) + 5832
  have hterm : ∀ q < m, |N * (ringHeight n (i + q + 1) - ringHeight n (i + q)) - (ringRows n).aspect r|
      ≤ C * m / N := fun q hq =>
    ringBand_gap hn hhi hlo hband (Q := i + q) (r := r) (m := m) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have htel : N * (ringHeight n j - ringHeight n i) - (m : ℝ) * (ringRows n).aspect r =
      ∑ q ∈ range m, (N * (ringHeight n (i + q + 1) - ringHeight n (i + q)) - (ringRows n).aspect r) := by
    rw [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
    have := sum_range_sub (fun q => ringHeight n (i + q)) m
    simp only [show ∀ q, i + (q + 1) = i + q + 1 from fun q => rfl] at this
    rw [this, show i + m = j by omega, add_zero]
  rw [htel]
  calc _ ≤ ∑ q ∈ range m, |N * (ringHeight n (i + q + 1) - ringHeight n (i + q)) - (ringRows n).aspect r| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ range m, C * m / N := sum_le_sum fun q hq => hterm q (mem_range.1 hq)
    _ = C * (m : ℝ) ^ 2 / N := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **In-band spacing, lower bound**: `N (t_j - t_i) ≥ (3/56)(j - i)` along a band. -/
theorem ringBand_spacing_ge {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {i j : ℕ} (hi' : lo ≤ i) (hij : i ≤ j) (hj : j ≤ hi) :
    3 / 56 * ((j - i : ℕ) : ℝ) ≤ (ringN n lo : ℝ) * (ringHeight n j - ringHeight n i) := by
  set N := (ringN n lo : ℝ)
  set m := j - i
  have hN0 : (0 : ℝ) < N := by
    have := three_le_ringN (n := n) (by omega) lo (by omega)
    simp only [N]; exact_mod_cast (show 0 < ringN n lo by omega)
  have hterm : ∀ q < m, 3 / 56 ≤ N * (ringHeight n (i + q + 1) - ringHeight n (i + q)) := by
    intro q hq
    have hsep := ringHeight_sep hn (show i + q < i + q + 1 by omega) (show i + q + 1 < ringK n by omega)
    rw [ringBand_N hband (i + q) (by omega) (by omega), ringBand_N hband (i + q + 1) (by omega)
      (by omega)] at hsep
    have : (3 : ℝ) / 56 = N * (3 / (112 * N) + 3 / (112 * N)) := by field_simp; norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hN0.le
  have htel : N * (ringHeight n j - ringHeight n i) =
      ∑ q ∈ range m, N * (ringHeight n (i + q + 1) - ringHeight n (i + q)) := by
    rw [← mul_sum]
    have := sum_range_sub (fun q => ringHeight n (i + q)) m
    simp only [show ∀ q, i + (q + 1) = i + q + 1 from fun q => rfl] at this
    rw [this, show i + m = j by omega, add_zero]
  rw [htel]
  calc 3 / 56 * (m : ℝ) = ∑ _q ∈ range m, (3 / 56 : ℝ) := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum fun q hq => hterm q (mem_range.1 hq)

/-- **Lemma 5.11, the exact formula**: for band rows `i < j`,
`X_{ij} = -N log |1 - (-1)^{j-i} e^{-N (t_j - t_i)}|`. -/
theorem ringBand_X {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {i j : ℕ} (hi' : lo ≤ i) (hij : i < j) (hj : j ≤ hi) :
    (ringRows n).X i j =
      -(ringN n lo : ℝ) * ringLogFn (j - i) ((ringN n lo : ℝ) * (ringHeight n j - ringHeight n i)) := by
  have hNi : ringN n i = ringN n lo := ringBand_N hband i hi' (by omega)
  have hNj : ringN n j = ringN n lo := ringBand_N hband j (by omega) hj
  have hJi := ringBand_J hband i hi' (by omega)
  have hJj := ringBand_J hband j (by omega) hj
  have hN0 : (0 : ℝ) < ringN n lo := by
    have := three_le_ringN (n := n) (by omega) lo (by omega)
    exact_mod_cast (show 0 < ringN n lo by omega)
  have hlt : ringHeight n i < ringHeight n j := by
    have := ringHeight_sep hn hij (show j < ringK n by omega)
    have h3 : (3 : ℝ) ≤ ringN n i := by exact_mod_cast three_le_ringN (by omega) i (by omega)
    have h3' : (3 : ℝ) ≤ ringN n j := by exact_mod_cast three_le_ringN (by omega) j (by omega)
    have : 0 < 3 / (112 * (ringN n i : ℝ)) := by positivity
    have : 0 < 3 / (112 * (ringN n j : ℝ)) := by positivity
    linarith
  unfold RowConfig.X ringLogFn
  have eN : (ringRows n).N i = ringN n lo := hNi
  have eN' : (ringRows n).N j = ringN n lo := hNj
  have et : (ringRows n).t i = ringHeight n i := rfl
  have et' : (ringRows n).t j = ringHeight n j := rfl
  have eφ : (ringRows n).φ j - (ringRows n).φ i = ((j - i : ℕ) : ℝ) * Real.pi / ringN n lo := by
    show ringJ n j * Real.pi / ringN n j - ringJ n i * Real.pi / ringN n i = _
    rw [hNi, hNj, hJi, hJj]
    rw [show ringJ n lo + (j - lo) = (ringJ n lo + (i - lo)) + (j - i) by omega]
    push_cast; ring
  rw [eN, eN', et, et', Nat.gcd_self, Nat.lcm_self, eφ, abs_sub_comm, abs_of_pos (by linarith)]
  congr 1
  rw [show ((ringN n lo : ℕ) : ℝ) * (((j - i : ℕ) : ℝ) * Real.pi / ringN n lo) =
    ((j - i : ℕ) : ℝ) * Real.pi by field_simp]
  have hexp : Complex.exp ((((j - i : ℕ) : ℝ) * Real.pi : ℝ) * Complex.I) = (-1) ^ (j - i) := by
    rw [show (((((j - i : ℕ) : ℝ) * Real.pi : ℝ)) : ℂ) * Complex.I =
      ((j - i : ℕ) : ℂ) * (Real.pi * Complex.I) by push_cast; ring, Complex.exp_nat_mul,
      Complex.exp_pi_mul_I]
  rw [hexp, ← Complex.ofReal_exp]
  have e : (1 : ℂ) - (Real.exp (-((ringN n lo : ℝ) * (ringHeight n j - ringHeight n i))) : ℂ) *
      (-1) ^ (j - i) = ((1 - (-1) ^ (j - i) *
        Real.exp (-((ringN n lo : ℝ) * (ringHeight n j - ringHeight n i))) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]

end Sphere

end SandierSerfaty

end
