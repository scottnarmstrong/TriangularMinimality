/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Band
public import SandierSerfaty.Sphere.Ring.RingConstant

/-!
# Ingredients of the in-band spacing (sphere note, Lemma 5.11)

A *band* `[lo, hi]` is a run of rows whose first row is bulk and whose other rows are (C)-rows; all its
rows have the count `N = N_lo`. For `n ≥ 102`:

* `Sphere.ringHalf_sub_le`: for every interior row, `|N_q (t_q - τ(A_q)) - x_q/2|` and
  `|N_q (τ(A_{q+1}) - t_q) - x_q/2|` are at most `C₁/N_q` (`C₁ = 1458 e^{54}`);
* `Sphere.ringBand_dist_le`: along a band, `|t_q - t_r| ≤ 54 |q - r|/N`;
* `Sphere.ringBand_aspect_drift`: along a band, `|x_q - x_r| ≤ 5832 |q - r|/N`.

Lemma 5.11 itself is in `SandierSerfaty.Sphere.Ring.Spacing`.
-/

open MeasureTheory Set Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `log |1 - (-1)^m e^{-D}|`; `ringLogTerm x m = ringLogFn m (m x)`. -/
@[expose] noncomputable def ringLogFn (m : ℕ) (D : ℝ) : ℝ := Real.log (1 - (-1) ^ m * Real.exp (-D))

theorem ringLogTerm_eq (x : ℝ) (m : ℕ) : ringLogTerm x m = ringLogFn m (m * x) := rfl

/-- The aspect of a row of `Y_n`: `x_k = N_k²/ϱ(t_k)`. -/
theorem ringRows_aspect_eq (n k : ℕ) :
    (ringRows n).aspect k = (ringN n k : ℝ) ^ 2 / ringDensity n (ringHeight n k) := by
  rw [RowConfig.aspect, ringRows_card]; rfl

/-- On interior rows `1/3 ≤ x_k ≤ 18`. -/
theorem ringAspect_mem {n k : ℕ} (hn : 102 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    1 / 3 ≤ (ringRows n).aspect k ∧ (ringRows n).aspect k ≤ 18 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ0 := ringDensity_pos hn' (ringHeight n k)
  have hρ := ringDensity_height_le hn (show k < ringK n by omega)
  have hρ2 := (ringDensity_interior (by omega) hk1 hk (ringHeight_mem_Icc (by omega) hk1 hk)).2
  rw [ringRows_aspect_eq]
  constructor
  · rw [le_div_iff₀ hρ0]; linarith
  · rw [div_le_iff₀ hρ0]; linarith

/-- **Half-gaps**: for interior rows, `|N_q (t_q - α_q) - x_q/2| ≤ C₁/N_q` and
`|N_q (β_q - t_q) - x_q/2| ≤ C₁/N_q`, `C₁ = 1458 e^{54}`. -/
theorem ringHalf_sub_le {n q : ℕ} (hn : 102 ≤ n) (hq1 : 1 ≤ q) (hq : q + 1 < ringK n) :
    |(ringN n q : ℝ) * (ringHeight n q - ringQuantile n (ringState n q).1) - (ringRows n).aspect q / 2|
        ≤ 1458 * Real.exp 54 / ringN n q ∧
      |(ringN n q : ℝ) * (ringQuantile n (ringState n (q + 1)).1 - ringHeight n q) -
        (ringRows n).aspect q / 2| ≤ 1458 * Real.exp 54 / ringN n q := by
  obtain ⟨hN3, -, -, hb, ha0, hbn⟩ := ringInterior_facts (by omega) hq1 hq
  obtain ⟨-, hL⟩ := ringSlab_length_mem (by omega) hq1 hq
  obtain ⟨hs1, hs2⟩ := ringHeight_mem_Icc (by omega) hq1 hq
  obtain ⟨hx1, hx2⟩ := ringAspect_mem hn hq1 hq
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hhq := ringHeight_eq_slabBary (show q < ringK n by omega)
  have hNd : ((ringState n (q + 1)).1 : ℝ) - (ringState n q).1 = ringN n q := by rw [hb]; ring
  rw [hhq] at hs1 hs2
  obtain ⟨b1, b2, b3, b4⟩ := slabBary_bounds_exp ha0 (by linarith) hbn hs1 hs2
  rw [← hhq, hNd] at b1 b2 b3 b4
  rw [ringRows_aspect_eq] at hx1 hx2 ⊢
  set α := ringQuantile n (ringState n q).1
  set β := ringQuantile n (ringState n (q + 1)).1
  set L := β - α
  set N := (ringN n q : ℝ)
  set ρ := ringDensity n (ringHeight n q)
  set tq := ringHeight n q
  have hρ0 : 0 < ρ := ringDensity_pos hn' _
  have hN0 : 0 < N := by linarith
  have hL0 : 0 ≤ L := by simp only [L]; linarith
  have h6L : 6 * L ≤ 54 := by
    have : 27 / N ≤ 9 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  set x := N ^ 2 / ρ
  have hx : 1 / 3 ≤ x ∧ x ≤ 18 := ⟨hx1, hx2⟩
  -- `N · N/(2ρ) = x/2`
  have hNB : N * (N / (2 * ρ)) = x / 2 := by simp only [x]; field_simp
  have hE1 : Real.exp (6 * L) - 1 ≤ 6 * L * Real.exp 54 := by
    have := exp_le_one_add_mul_exp (show 0 ≤ 6 * L by linarith)
    have h2 : Real.exp (6 * L) ≤ Real.exp 54 := Real.exp_le_exp.2 h6L
    linarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 6 * L)]
  have hE2 : 1 - Real.exp (-(6 * L)) ≤ 6 * L * Real.exp 54 := by
    have := Real.add_one_le_exp (-(6 * L))
    have : 6 * L ≤ 6 * L * Real.exp 54 :=
      le_mul_of_one_le_right (by linarith) (Real.one_le_exp (by norm_num))
    linarith
  have key : ∀ y : ℝ, N / (2 * ρ) * Real.exp (-(6 * L)) ≤ y → y ≤ N / (2 * ρ) * Real.exp (6 * L) →
      |N * y - x / 2| ≤ 1458 * Real.exp 54 / N := by
    intro y hy1 hy2
    have h1 : x / 2 * Real.exp (-(6 * L)) ≤ N * y := by
      rw [← hNB]; have := mul_le_mul_of_nonneg_left hy1 hN0.le; linarith
    have h2 : N * y ≤ x / 2 * Real.exp (6 * L) := by
      rw [← hNB]; have := mul_le_mul_of_nonneg_left hy2 hN0.le; linarith
    have hbound : x / 2 * (6 * L * Real.exp 54) ≤ 1458 * Real.exp 54 / N := by
      rw [le_div_iff₀ hN0]
      have hLN : L * N ≤ 27 := by rwa [le_div_iff₀ hN0] at hL
      have hE := Real.exp_pos 54
      linarith [mul_le_mul_of_nonneg_left hLN (show 0 ≤ x * Real.exp 54 by positivity),
        mul_le_mul_of_nonneg_right hx.2 hE.le]
    rw [abs_le]
    constructor
    · have : x / 2 - x / 2 * Real.exp (-(6 * L)) ≤ x / 2 * (6 * L * Real.exp 54) := by
        have := mul_le_mul_of_nonneg_left hE2 (show 0 ≤ x / 2 by linarith)
        linarith
      linarith
    · have : x / 2 * Real.exp (6 * L) - x / 2 ≤ x / 2 * (6 * L * Real.exp 54) := by
        have := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ x / 2 by linarith)
        linarith
      linarith
  exact ⟨key _ b1 b2, key _ b3 b4⟩

/-- The gap between consecutive rows is at most `54/N` when both are interior with count `N`. -/
theorem ringHeight_succ_sub_le {n q : ℕ} (hn : 102 ≤ n) (hq1 : 1 ≤ q) (hq : q + 2 < ringK n)
    (hN : ringN n (q + 1) = ringN n q) :
    ringHeight n (q + 1) - ringHeight n q ≤ 54 / ringN n q := by
  obtain ⟨-, hL1⟩ := ringSlab_length_mem (by omega) hq1 (show q + 1 < ringK n by omega)
  obtain ⟨-, hL2⟩ := ringSlab_length_mem (n := n) (k := q + 1) (by omega) (by omega) hq
  obtain ⟨hs1, -⟩ := ringHeight_mem_Icc (by omega) hq1 (show q + 1 < ringK n by omega)
  obtain ⟨-, hs2⟩ := ringHeight_mem_Icc (n := n) (k := q + 1) (by omega) (by omega) hq
  rw [hN] at hL2
  have : (54 : ℝ) / ringN n q = 27 / ringN n q + 27 / ringN n q := by ring
  linarith

/-- Along a band, `|t_q - t_r| ≤ 54 |q - r|/N`. -/
theorem ringBand_dist_le {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n) (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {q r : ℕ} (hq : lo ≤ q) (hqr : q ≤ r) (hr : r ≤ hi) :
    ringHeight n r - ringHeight n q ≤ 54 * (r - q : ℕ) / ringN n lo := by
  induction r, hqr using Nat.le_induction with
  | base => simp
  | succ r hqr ih =>
    have ih' := ih (by omega)
    have hbulk := ringBand_bulk hlo hband r (by omega) (by omega)
    obtain ⟨hr1, hrK⟩ := ringBulk_interior (by omega) hbulk
    have hNr : ringN n r = ringN n lo := ringBand_N hband r (by omega) (by omega)
    have hNr1 : ringN n (r + 1) = ringN n lo := ringBand_N hband (r + 1) (by omega) hr
    have hstep := ringHeight_succ_sub_le hn hr1 (show r + 2 < ringK n by
      have := ringBulk_interior (n := n) (k := r + 1) (by omega)
        (ringBand_bulk hlo hband (r + 1) (by omega) hr)
      omega) (by rw [hNr, hNr1])
    rw [hNr] at hstep
    have e : ((r + 1 - q : ℕ) : ℝ) = ((r - q : ℕ) : ℝ) + 1 := by
      rw [show r + 1 - q = (r - q) + 1 by omega]; push_cast; ring
    rw [e]
    have : 54 * (((r - q : ℕ) : ℝ) + 1) / (ringN n lo : ℝ) =
        54 * ((r - q : ℕ) : ℝ) / ringN n lo + 54 / ringN n lo := by ring
    linarith

/-- **Aspect drift along a band**: `|x_q - x_r| ≤ 5832 |q - r|/N`. -/
theorem ringBand_aspect_drift {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n) (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {q r : ℕ} (hq : lo ≤ q) (hqr : q ≤ r) (hr : r ≤ hi) :
    |(ringRows n).aspect q - (ringRows n).aspect r| ≤ 5832 * (r - q : ℕ) / ringN n lo := by
  have hbq := ringBand_bulk hlo hband q hq (by omega)
  have hbr := ringBand_bulk hlo hband r (by omega) hr
  obtain ⟨hq1, hqK⟩ := ringBulk_interior (by omega) hbq
  obtain ⟨hr1, hrK⟩ := ringBulk_interior (by omega) hbr
  obtain ⟨hxq1, hxq2⟩ := ringAspect_mem hn hq1 hqK
  obtain ⟨hxr1, hxr2⟩ := ringAspect_mem hn hr1 hrK
  simp only [ringRows_aspect_eq] at hxq1 hxq2 hxr1 hxr2 ⊢
  have hd := ringBand_dist_le hn hhi hlo hband hq hqr hr
  have hsep : ringHeight n q ≤ ringHeight n r := by
    rcases hqr.eq_or_lt with h | h
    · rw [h]
    · have := ringHeight_sep hn h (show r < ringK n by omega)
      have h3 : (3 : ℝ) ≤ ringN n q := by exact_mod_cast three_le_ringN (by omega) q (by omega)
      have h3' : (3 : ℝ) ≤ ringN n r := by exact_mod_cast three_le_ringN (by omega) r (by omega)
      have : 0 < 3 / (112 * (ringN n q : ℝ)) := by positivity
      have : 0 < 3 / (112 * (ringN n r : ℝ)) := by positivity
      linarith
  have hNq : ringN n q = ringN n lo := ringBand_N hband q hq (by omega)
  have hNr : ringN n r = ringN n lo := ringBand_N hband r (by omega) hr
  have hN3 : (3 : ℝ) ≤ ringN n lo := by
    rw [← hNq]; exact_mod_cast three_le_ringN (by omega) q (by omega)
  rw [hNq] at hxq1 hxq2 ⊢
  rw [hNr] at hxr1 hxr2 ⊢
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set N := (ringN n lo : ℝ)
  set m := ((r - q : ℕ) : ℝ)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set y := 108 * m / N
  have hy0 : 0 ≤ y := by positivity
  have hΔ : 2 * |ringHeight n r - ringHeight n q| ≤ y := by
    have e : 2 * (54 * m / N) = y := by simp only [y]; ring
    rw [abs_of_nonneg (by linarith)]; linarith
  set ρq := ringDensity n (ringHeight n q)
  set ρr := ringDensity n (ringHeight n r)
  have hρq := ringDensity_pos hn' (ringHeight n q)
  have hρr := ringDensity_pos hn' (ringHeight n r)
  have hρq0 : ρq ≠ 0 := hρq.ne'
  have hρr0 : ρr ≠ 0 := hρr.ne'
  have h1 : ρr ≤ ρq * Real.exp y := (ringDensity_le_mul_exp hn'.le _ _).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hΔ) hρq.le)
  have h2 : ρq ≤ ρr * Real.exp y := (ringDensity_le_mul_exp hn'.le _ _).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by rw [abs_sub_comm]; exact hΔ)) hρr.le)
  have hEy := Real.exp_pos y
  have hdiff : |N ^ 2 / ρq - N ^ 2 / ρr| ≤ 18 * (Real.exp y - 1) := by
    have e : N ^ 2 / ρq - N ^ 2 / ρr = N ^ 2 / ρr * (ρr / ρq - 1) := by field_simp
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hq' : |ρr / ρq - 1| ≤ Real.exp y - 1 := by
      rw [abs_le]; constructor
      · have : ρq / Real.exp y ≤ ρr := by rw [div_le_iff₀ hEy]; exact h2
        have hinv : 1 - (Real.exp y - 1) ≤ 1 / Real.exp y := by
          rw [one_div, ← Real.exp_neg]
          have := Real.add_one_le_exp (-y)
          have := exp_le_one_add_mul_exp hy0
          have h3 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
          have h4 : y ≤ Real.exp y - 1 := by linarith [Real.add_one_le_exp y]
          linarith
        have : 1 / Real.exp y ≤ ρr / ρq := by
          calc 1 / Real.exp y = (ρq / Real.exp y) / ρq := by field_simp
            _ ≤ ρr / ρq := by gcongr
        linarith
      · have : ρr / ρq ≤ Real.exp y := by rw [div_le_iff₀ hρq]; linarith
        linarith
    have hE1 : 0 ≤ Real.exp y - 1 := by linarith [Real.add_one_le_exp y]
    exact mul_le_mul hxr2 hq' (abs_nonneg _) (by norm_num)
  have hcap : |N ^ 2 / ρq - N ^ 2 / ρr| ≤ 18 := by rw [abs_le]; constructor <;> linarith
  rcases le_total y 1 with hy1 | hy1
  · have h3 := exp_le_one_add_mul_exp hy0
    have h4 : Real.exp y ≤ 3 := by
      have := Real.exp_le_exp.2 hy1
      have := Real.exp_one_lt_d9
      linarith
    have : 18 * (Real.exp y - 1) ≤ 54 * y := by
      linarith [mul_le_mul_of_nonneg_left h4 hy0]
    calc _ ≤ 54 * y := hdiff.trans this
      _ = 5832 * m / N := by simp only [y]; ring
  · calc _ ≤ 18 := hcap
      _ ≤ 54 * y := by linarith
      _ = 5832 * m / N := by simp only [y]; ring

end Sphere

end SandierSerfaty

end
