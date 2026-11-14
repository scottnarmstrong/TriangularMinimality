/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Construction

/-!
# Geometry of the ring construction: rows near the target count (sphere note, Lemma 5.8 (G2))

Rows are indexed from `0`; the interior rows of the sphere note (`2 ≤ k ≤ K - 1`) are `1 ≤ k ≤ K - 2`
here, i.e. `1 ≤ k` and `k + 1 < K`.

* `Sphere.ringStep_cases`: a non-final step is a (C)-step or an (S)-step;
* `Sphere.four_le_ringTarget`: `N*(A_k) ≥ 4` on interior rows;
* `Sphere.abs_ringN_sub_le_tol`, `Sphere.abs_ringN_sub_le_half`, `Sphere.ringN_mem_Icc`,
  `Sphere.two_mul_ringN_le`: Lemma 5.8 (G2).
-/

public section

namespace SandierSerfaty

namespace Sphere

/-- The continuation condition of rule (C) at the state `s`. -/
@[expose] def RingCont (n : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  0 < s.2.1 ∧ (ringCap n : ℝ) ≤ ringTarget n s.1 ∧ (ringCap n : ℝ) ≤ ringTarget n (s.1 - s.2.1) ∧
    |(s.2.1 : ℝ) - ringTarget n s.1| ≤ ringTol n

/-- A non-final step is a (C)-step (repeat the previous count) or an (S)-step (count `ñ`). -/
theorem ringStep_cases {n : ℕ} {s : ℕ × ℕ × ℕ} (h : s.1 < n) (h' : (ringStep n s).1 < n) :
    2 * ringRound n s.1 + 3 < n - s.1 ∧
      ((RingCont n s ∧ ringStep n s = (s.1 + s.2.1, s.2.1, s.2.2 + 1)) ∨
        (¬ RingCont n s ∧ ringStep n s = (s.1 + ringRound n s.1, ringRound n s.1, 0))) := by
  have hlt : ¬ n ≤ s.1 := not_le.2 h
  have hF : ¬ n - s.1 ≤ 2 * ringRound n s.1 + 3 := by
    intro hF
    unfold ringStep at h'
    rw [ite_eq_right hlt, ite_eq_left hF] at h'
    exact lt_irrefl _ h'
  refine ⟨not_le.1 hF, ?_⟩
  unfold ringStep
  rw [ite_eq_right hlt, ite_eq_right hF]
  by_cases hC : RingCont n s
  · left
    refine ⟨hC, ?_⟩
    unfold RingCont at hC
    rw [ite_eq_left hC]
  · right
    refine ⟨hC, ?_⟩
    unfold RingCont at hC
    rw [ite_eq_right hC]

theorem one_le_ringTol {n : ℕ} (hn : 0 < n) : 1 ≤ ringTol n := by
  unfold ringTol
  exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)).ne'

theorem two_sqrt_three_pi_gt : 10.8 < 2 * Real.sqrt 3 * Real.pi := by
  have h3 : 1.732 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hπ := Real.pi_gt_d2
  nlinarith

/-- `|ñ(a) - N*(a)| ≤ ½` once `N*(a) ≥ 5/2`. -/
theorem abs_ringRound_sub_le {n a : ℕ} (h : 5 / 2 ≤ ringTarget n a) :
    |(ringRound n a : ℝ) - ringTarget n a| ≤ 1 / 2 := by
  have hfl : 3 ≤ ⌊ringTarget n a + 1 / 2⌋₊ := by
    rw [Nat.le_floor_iff (by linarith)]; push_cast; linarith
  have : ringRound n a = ⌊ringTarget n a + 1 / 2⌋₊ := by unfold ringRound; omega
  rw [this, abs_le]
  have h1 := Nat.floor_le (show 0 ≤ ringTarget n a + 1 / 2 by linarith)
  have h2 := Nat.lt_floor_add_one (ringTarget n a + 1 / 2)
  constructor <;> linarith

/-- On interior rows, `A_k ≥ 3`. -/
theorem three_le_ringState {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k < ringK n) :
    3 ≤ (ringState n k).1 := by
  rw [ringState_fst_eq_sum n k hk.le]
  calc 3 ≤ ringN n 0 := three_le_ringN hn 0 (by omega)
    _ = ∑ j ∈ Finset.range 1, ringN n j := by simp
    _ ≤ ∑ j ∈ Finset.range k, ringN n j :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hk1)

/-- On interior rows, `N*(A_k) ≥ 4`. -/
theorem four_le_ringTarget {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    4 ≤ ringTarget n (ringState n k).1 := by
  have hA := three_le_ringState hn hk1 (by omega : k < ringK n)
  have hs := ringStep_spec_at (n := n) (k := k) (by omega)
  have hlt : (ringState n (k + 1)).1 < n := ringState_lt_of_lt_ringK hk
  have h9 := (hs.2.2.2 hlt).2.1
  set a := (ringState n k).1
  have hsq := ringTarget_sq n a (by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha3 : (3 : ℝ) ≤ a := by exact_mod_cast hA
  have hna : (10 : ℝ) ≤ n - a := by
    have : 10 ≤ n - a := by omega
    have e : ((n - a : ℕ) : ℝ) = n - a := by push_cast [show a ≤ n by omega]; ring
    rw [← e]; exact_mod_cast this
  have hc := two_sqrt_three_pi_gt
  have hprod : (3 / 2 : ℝ) * n ≤ a * (n - a) := by nlinarith
  have h16 : 16 ≤ ringTarget n a ^ 2 := by
    rw [hsq, le_div_iff₀ hn']
    nlinarith
  nlinarith [ringTarget_nonneg n a]

/-- **(G2)**, bulk rows: `|N_k - N*(A_k)| ≤ T`. -/
theorem abs_ringN_sub_le_tol {n k : ℕ} (hn : 10 ≤ n) (hk : k + 1 < ringK n)
    (hb : (ringCap n : ℝ) ≤ ringTarget n (ringState n k).1) :
    |(ringN n k : ℝ) - ringTarget n (ringState n k).1| ≤ ringTol n := by
  have hlt0 : (ringState n k).1 < n := ringState_lt_of_lt_ringK (by omega)
  have hlt : (ringStep n (ringState n k)).1 < n := by
    rw [← ringState_succ]; exact ringState_lt_of_lt_ringK hk
  rcases (ringStep_cases hlt0 hlt).2 with ⟨hC, he⟩ | ⟨_, he⟩
  · have : ringN n k = (ringState n k).2.1 := by
      unfold ringN; rw [ringState_succ, he]
    rw [this]; exact hC.2.2.2
  · have : ringN n k = ringRound n (ringState n k).1 := by
      unfold ringN; rw [ringState_succ, he]
    rw [this]
    have hcap : (40 : ℝ) ≤ ringCap n := by
      have : 40 ≤ ringCap n := le_max_left _ _
      exact_mod_cast this
    have h1 : (1 : ℝ) ≤ ringTol n := by exact_mod_cast one_le_ringTol (by omega : 0 < n)
    have := abs_ringRound_sub_le (show 5 / 2 ≤ ringTarget n (ringState n k).1 by linarith)
    linarith

/-- **(G2)**, non-bulk rows: `|N_k - N*(A_k)| ≤ ½`. -/
theorem abs_ringN_sub_le_half {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n)
    (hb : ringTarget n (ringState n k).1 < ringCap n) :
    |(ringN n k : ℝ) - ringTarget n (ringState n k).1| ≤ 1 / 2 := by
  have hlt0 : (ringState n k).1 < n := ringState_lt_of_lt_ringK (by omega)
  have hlt : (ringStep n (ringState n k)).1 < n := by
    rw [← ringState_succ]; exact ringState_lt_of_lt_ringK hk
  rcases (ringStep_cases hlt0 hlt).2 with ⟨hC, _⟩ | ⟨_, he⟩
  · exact absurd hC.2.1 (not_le.2 hb)
  · have : ringN n k = ringRound n (ringState n k).1 := by
      unfold ringN; rw [ringState_succ, he]
    rw [this]
    have := four_le_ringTarget hn hk1 hk
    exact abs_ringRound_sub_le (by linarith)

/-- **(G2)**: on interior rows `N_k / N*(A_k) ∈ [3/4, 5/4]`. -/
theorem ringN_mem_Icc {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    3 / 4 * ringTarget n (ringState n k).1 ≤ ringN n k ∧
      (ringN n k : ℝ) ≤ 5 / 4 * ringTarget n (ringState n k).1 := by
  have h4 := four_le_ringTarget hn hk1 hk
  rcases le_or_gt (ringCap n : ℝ) (ringTarget n (ringState n k).1) with hb | hb
  · have h := abs_le.1 (abs_ringN_sub_le_tol hn hk hb)
    have hT4 : 4 * (ringTol n : ℝ) ≤ ringCap n := by
      have : 4 * ringTol n ≤ ringCap n := le_max_right _ _
      exact_mod_cast this
    constructor <;> linarith [h.1, h.2]
  · have h := abs_le.1 (abs_ringN_sub_le_half hn hk1 hk hb)
    constructor <;> linarith [h.1, h.2]

/-- **(G2)**: `N_k ≤ ½ (n - A_k)` for every non-final row. -/
theorem two_mul_ringN_le {n k : ℕ} (hk : k + 1 < ringK n) :
    2 * ringN n k ≤ n - (ringState n k).1 :=
  ((ringStep_spec_at (n := n) (k := k) (by omega)).2.2.2 (ringState_lt_of_lt_ringK hk)).1

/-! ### (G3) slab lengths -/

/-- `N*(a)² ≤ 2√3π a`. -/
theorem ringTarget_sq_le_left (n a : ℕ) (ha : a ≤ n) :
    ringTarget n a ^ 2 ≤ 2 * Real.sqrt 3 * Real.pi * a := by
  rw [ringTarget_sq n a ha]
  have hc := two_sqrt_three_pi_pos
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    subst this; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith [mul_nonneg (mul_nonneg hc.le h0) h0]

/-- `min(a, n - a) ≤ 2 N*(a)² / (2√3π)`. -/
theorem min_le_ringTarget_sq (n a : ℕ) (ha : a ≤ n) :
    2 * Real.sqrt 3 * Real.pi * min (a : ℝ) ((n : ℝ) - a) ≤ 2 * ringTarget n a ^ 2 := by
  rw [ringTarget_sq n a ha]
  have hc := two_sqrt_three_pi_pos
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    subst this; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    rw [show 2 * (2 * Real.sqrt 3 * Real.pi * a * ((n : ℝ) - a) / n) =
      2 * Real.sqrt 3 * Real.pi * (2 * a * ((n : ℝ) - a) / n) by ring]
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [le_div_iff₀ hn']
    rcases le_total (a : ℝ) ((n : ℝ) - a) with h | h
    · rw [min_eq_left h]; linarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ n - 2 * a)]
    · rw [min_eq_right h]
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n - a) (by linarith : (0 : ℝ) ≤ 2 * a - n)]

/-- `τ(b) - τ(a) = ½ (log (b/a) + log ((n - a)/(n - b)))`. -/
theorem ringQuantile_sub {n a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbn : b < n) :
    ringQuantile n b - ringQuantile n a =
      (Real.log (b / a) + Real.log ((n - a) / (n - b))) / 2 := by
  unfold ringQuantile
  have hb : 0 < b := by linarith
  rw [Real.log_div hb.ne' (by linarith), Real.log_div ha.ne' (by linarith),
    Real.log_div hb.ne' ha.ne', Real.log_div (by linarith) (by linarith)]
  ring

/-- The slab-length bounds, in real form: for `b = a + N`, `a ≥ N²/18`, `n - b ≥ N²/36`,
`min(a, n - a) ≤ N²/3` and `N ≥ 3`, `3/(4N) ≤ τ(b) - τ(a) ≤ 27/N`. -/
theorem ringQuantile_sub_mem {n a N : ℝ} (hN : 3 ≤ N) (ha : N ^ 2 / 18 ≤ a)
    (hb : N ^ 2 / 36 ≤ n - (a + N)) (hmin : min a (n - a) ≤ N ^ 2 / 3) :
    3 / (4 * N) ≤ ringQuantile n (a + N) - ringQuantile n a ∧
      ringQuantile n (a + N) - ringQuantile n a ≤ 27 / N := by
  have hN0 : 0 < N := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hb0 : 0 < n - (a + N) := lt_of_lt_of_le (by positivity) hb
  rw [ringQuantile_sub ha0 (by linarith) (by linarith)]
  have hna : 0 < n - a := by linarith
  -- the two logarithms are nonnegative
  have hl1 : 0 ≤ Real.log ((a + N) / a) := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hl2 : 0 ≤ Real.log ((n - a) / (n - (a + N))) :=
    Real.log_nonneg (by rw [le_div_iff₀ hb0]; linarith)
  constructor
  · rcases le_total a (n - a) with h | h
    · rw [min_eq_left h] at hmin
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (a + N) / a by positivity)
      have e : 1 - ((a + N) / a)⁻¹ = N / (a + N) := by field_simp; ring
      rw [e] at this
      have : 3 / (2 * N) ≤ N / (a + N) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [mul_le_mul_of_nonneg_right hN hN0.le]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 3 / (2 * N) ≤ Real.log ((a + N) / a) := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      linarith [mul_nonneg hl2 (by positivity : (0 : ℝ) ≤ 4 * N)]
    · rw [min_eq_right h] at hmin
      have := Real.one_sub_inv_le_log_of_pos (show 0 < (n - a) / (n - (a + N)) by positivity)
      have e : 1 - ((n - a) / (n - (a + N)))⁻¹ = N / (n - a) := by field_simp; ring
      rw [e] at this
      have : 3 / (2 * N) ≤ N / (n - a) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 3 / (2 * N) ≤ Real.log ((n - a) / (n - (a + N))) := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      linarith [mul_nonneg hl1 (by positivity : (0 : ℝ) ≤ 4 * N)]
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < (a + N) / a by positivity)
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (n - a) / (n - (a + N)) by positivity)
    have e1 : (a + N) / a - 1 = N / a := by field_simp; ring
    have e2 : (n - a) / (n - (a + N)) - 1 = N / (n - (a + N)) := by field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    have h3 : N / a ≤ 18 / N := by
      rw [div_le_div_iff₀ ha0 hN0]; linarith
    have h4 : N / (n - (a + N)) ≤ 36 / N := by
      rw [div_le_div_iff₀ hb0 hN0]; linarith
    have : 27 / N = (18 / N + 36 / N) / 2 := by field_simp; norm_num
    rw [this]
    linarith

/-- **(G3)**: for interior rows, `3/(4 N_k) ≤ |I_k| = τ(A_{k+1}) - τ(A_k) ≤ 27/N_k`. -/
theorem ringSlab_length_mem {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    3 / (4 * ringN n k) ≤
        ringQuantile n (ringState n (k + 1)).1 - ringQuantile n (ringState n k).1 ∧
      ringQuantile n (ringState n (k + 1)).1 - ringQuantile n (ringState n k).1 ≤
        27 / ringN n k := by
  have hs := ringStep_spec_at (n := n) (k := k) (by omega)
  have hlt : (ringState n (k + 1)).1 < n := ringState_lt_of_lt_ringK hk
  have hle : (ringState n k).1 ≤ n := by omega
  have h2 := two_mul_ringN_le hk
  have hN3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN hn k (by omega)
  obtain ⟨hlo, hhi⟩ := ringN_mem_Icc hn hk1 hk
  set a := (ringState n k).1
  set N := ringN n k
  set x := ringTarget n a
  have hc := two_sqrt_three_pi_lt
  have hc' := two_sqrt_three_pi_gt
  have hx0 := ringTarget_nonneg n a
  have hb : ((ringState n (k + 1)).1 : ℝ) = a + N := by rw [hs.1]; push_cast; ring
  have hna : ((n - a : ℕ) : ℝ) = n - a := by push_cast [hle]; ring
  have h2' : 2 * (N : ℝ) ≤ n - a := by rw [← hna]; exact_mod_cast h2
  have hsq1 := ringTarget_sq_le_left n a hle
  have hsq2 := ringTarget_sq_le n a hle
  have hmin := min_le_ringTarget_sq n a hle
  rw [hb]
  apply ringQuantile_sub_mem hN3
  · -- `a ≥ N*²/(2√3π) ≥ (4N/5)²/10.9`
    have : (4 / 5 * N) ^ 2 ≤ x ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    linarith [mul_le_mul_of_nonneg_right hc.le (Nat.cast_nonneg a : (0 : ℝ) ≤ a),
      sq_nonneg (N : ℝ)]
  · have : (4 / 5 * N) ^ 2 ≤ x ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    linarith [mul_le_mul_of_nonneg_right hc.le (by linarith : (0 : ℝ) ≤ n - a),
      sq_nonneg (N : ℝ)]
  · have : x ^ 2 ≤ (4 / 3 * N) ^ 2 := by
      apply pow_le_pow_left₀ hx0; linarith
    have hm0 : 0 ≤ min (a : ℝ) ((n : ℝ) - a) := le_min (Nat.cast_nonneg _) (by linarith)
    linarith [mul_le_mul_of_nonneg_right hc'.le hm0, sq_nonneg (N : ℝ)]

end Sphere

end SandierSerfaty

end
