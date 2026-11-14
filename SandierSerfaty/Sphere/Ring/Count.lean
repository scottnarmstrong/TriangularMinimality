/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Band
public import SandierSerfaty.Sphere.Ring.Polar

/-!
# Counting the rows of `Y_n` (sphere note, Lemma 5.8 (G6))

Write `A_k = (ringState n k).1` for the mass below row `k` and `N* = ringTarget n`.

* `Sphere.card_le_of_one_le_abs_sub`: a set of indices on which a function `u ∈ [0, M]` takes values
  pairwise at distance `≥ 1` has at most `M + 1` elements;
* `Sphere.three_mul_le_ringState`, `Sphere.three_mul_sub_le`: `3k ≤ A_k` and `3 (K - k) ≤ n - A_k`;
* `Sphere.ringN_sq_lower`: on interior rows `N_k² ≥ 3 min(A_k, n - A_k)`;
* `Sphere.ringK_le`: **(G6), rows**: `K ≤ 4 √n + 4`. Instead of the sphere note's integral of `N(t)`,
  the count is done in the mass variable: `√A_k` grows by `≥ ½` per row on the southern half and
  `√(n - A_k)` decreases by `≥ ½` per row on the northern half;
* `Sphere.ringN_sq_le`: on interior rows `N_k² ≤ 9 n`;
* `Sphere.not_bulk_index`: a non-bulk row has `k ≤ N_cap²` or `K ≤ k + N_cap²`;
* `Sphere.ringN_le_of_not_bulk`: a non-bulk row has `N_k ≤ (5/4) N_cap + 51`;
* `Sphere.sum_ringN_not_bulk_le`: **(G6), non-bulk points**: at most
  `(2 N_cap² + 1)((5/4) N_cap + 51)` points lie in non-bulk rows. (The sphere note has `C N_cap²`; this
  cruder `O(N_cap³) = O(n^{3/4})` suffices for Theorem 5.13.)
-/

open Finset
open scoped Classical

public section

namespace SandierSerfaty

namespace Sphere

/-- A set of indices on which `u ∈ [0, M]` takes values pairwise at distance `≥ 1` has at most
`M + 1` elements. -/
theorem card_le_of_one_le_abs_sub {s : Finset ℕ} {u : ℕ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (h0 : ∀ k ∈ s, 0 ≤ u k) (hM : ∀ k ∈ s, u k ≤ M)
    (hgap : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → 1 ≤ |u k - u l|) : (s.card : ℝ) ≤ M + 1 := by
  have hinj : Set.InjOn (fun k => ⌊u k⌋₊) s := by
    intro k hk l hl he
    by_contra hne
    have h1 := hgap k hk l hl hne
    have he' : (⌊u k⌋₊ : ℝ) = ⌊u l⌋₊ := by exact_mod_cast he
    have a1 := Nat.floor_le (h0 k hk)
    have a2 := Nat.lt_floor_add_one (u k)
    have a3 := Nat.floor_le (h0 l hl)
    have a4 := Nat.lt_floor_add_one (u l)
    rw [le_abs] at h1
    rcases h1 with h1 | h1 <;> linarith
  have hmaps : ∀ k ∈ s, ⌊u k⌋₊ ∈ range (⌊M⌋₊ + 1) := fun k hk =>
    mem_range.2 (Nat.lt_succ_of_le (Nat.floor_le_floor (hM k hk)))
  have h := card_le_card_of_injOn _ hmaps hinj
  rw [card_range] at h
  have h' : (s.card : ℝ) ≤ (⌊M⌋₊ : ℝ) + 1 := by exact_mod_cast h
  linarith [Nat.floor_le hM0]

/-! ### Masses -/

theorem ringState_le_n {n k : ℕ} (hk : k ≤ ringK n) : ((ringState n k).1 : ℝ) ≤ n := by
  have := ringState_cast_le (n := n) hk
  rwa [ringState_ringK] at this

/-- `3k ≤ A_k`. -/
theorem three_mul_le_ringState {n k : ℕ} (hn : 10 ≤ n) (hk : k ≤ ringK n) :
    3 * k ≤ (ringState n k).1 := by
  rw [ringState_fst_eq_sum n k hk]
  have := card_nsmul_le_sum (range k) (fun j => ringN n j) 3
    (fun j hj => three_le_ringN hn j (by have := mem_range.1 hj; omega))
  simpa [mul_comm] using this

/-- `3 (K - k) + A_k ≤ n`. -/
theorem three_mul_sub_le {n k : ℕ} (hn : 10 ≤ n) (hk : k ≤ ringK n) :
    3 * (ringK n - k) + (ringState n k).1 ≤ n := by
  have hK := ringState_fst_eq_sum n (ringK n) le_rfl
  rw [ringState_ringK, ← sum_range_add_sum_Ico _ hk, ← ringState_fst_eq_sum n k hk] at hK
  have := card_nsmul_le_sum (Ico k (ringK n)) (fun j => ringN n j) 3
    (fun j hj => three_le_ringN hn j (mem_Ico.1 hj).2)
  rw [Nat.card_Ico, smul_eq_mul] at this
  omega

/-- `N*(a)² ≥ (2√3π/2) min(a, n - a)` in the two halves. -/
theorem ringTarget_sq_ge {n a : ℕ} (ha : a ≤ n) (hn : 0 < n) :
    ((2 * a ≤ n) → 5.4 * (a : ℝ) ≤ ringTarget n a ^ 2) ∧
      (n ≤ 2 * a → 5.4 * ((n : ℝ) - a) ≤ ringTarget n a ^ 2) := by
  have hsq := ringTarget_sq n a ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := two_sqrt_three_pi_gt
  have ha' : (a : ℝ) ≤ n := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  rw [hsq, le_div_iff₀ hn', le_div_iff₀ hn']
  set c := 2 * Real.sqrt 3 * Real.pi
  constructor
  · intro h
    have h' : 2 * (a : ℝ) ≤ n := by exact_mod_cast h
    have hna : 0 ≤ (n : ℝ) - a := by linarith
    calc 5.4 * (a : ℝ) * n = 10.8 * ((a : ℝ) * (n / 2)) := by ring
      _ ≤ 10.8 * ((a : ℝ) * (n - a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) ha0) (by norm_num)
      _ ≤ c * ((a : ℝ) * (n - a)) := mul_le_mul_of_nonneg_right hc.le (mul_nonneg ha0 hna)
      _ = c * a * (n - a) := by ring
  · intro h
    have h' : (n : ℝ) ≤ 2 * a := by exact_mod_cast h
    have hna : 0 ≤ (n : ℝ) - a := by linarith
    calc 5.4 * ((n : ℝ) - a) * n = 10.8 * (((n : ℝ) - a) * (n / 2)) := by ring
      _ ≤ 10.8 * (((n : ℝ) - a) * a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hna) (by norm_num)
      _ ≤ c * (((n : ℝ) - a) * a) := mul_le_mul_of_nonneg_right hc.le (mul_nonneg hna ha0)
      _ = c * a * (n - a) := by ring

/-- On interior rows, `N_k² ≥ 3 A_k` on the southern half and `N_k² ≥ 3 (n - A_k)` on the northern
half. -/
theorem ringN_sq_lower {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    (2 * (ringState n k).1 ≤ n → 3 * ((ringState n k).1 : ℝ) ≤ (ringN n k : ℝ) ^ 2) ∧
      (n ≤ 2 * (ringState n k).1 → 3 * ((n : ℝ) - (ringState n k).1) ≤ (ringN n k : ℝ) ^ 2) := by
  have ha : (ringState n k).1 ≤ n := by
    have := ringState_lt_of_lt_ringK (show k < ringK n by omega); omega
  obtain ⟨h1, h2⟩ := ringTarget_sq_ge ha (by omega)
  obtain ⟨hlo, -⟩ := ringN_mem_Icc hn hk1 hk
  have hx := ringTarget_nonneg n (ringState n k).1
  have hsq : 9 / 16 * ringTarget n (ringState n k).1 ^ 2 ≤ (ringN n k : ℝ) ^ 2 := by nlinarith
  have ha' : ((ringState n k).1 : ℝ) ≤ n := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ (ringState n k).1 := Nat.cast_nonneg _
  exact ⟨fun h => by linarith [h1 h], fun h => by linarith [h2 h]⟩

/-! ### (G6): the number of rows -/

theorem ringK_le_two_add {n : ℕ} (hn : 10 ≤ n) :
    (ringK n : ℝ) ≤ 2 + ((Ico 1 (ringK n - 1)).filter fun k => 2 * (ringState n k).1 ≤ n).card +
      ((Ico 1 (ringK n - 1)).filter fun k => ¬ 2 * (ringState n k).1 ≤ n).card := by
  have h2 := two_le_ringK hn
  have := card_filter_add_card_filter_not (s := Ico 1 (ringK n - 1))
    (fun k => 2 * (ringState n k).1 ≤ n)
  rw [Nat.card_Ico] at this
  have hnat : ringK n ≤ 2 + ((Ico 1 (ringK n - 1)).filter fun k => 2 * (ringState n k).1 ≤ n).card +
      ((Ico 1 (ringK n - 1)).filter fun k => ¬ 2 * (ringState n k).1 ≤ n).card := by omega
  exact_mod_cast hnat

/-- Southern rows: `√A_{k+1} ≥ √A_k + ½`. -/
theorem sqrt_ringState_succ_ge {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n)
    (hs : 2 * (ringState n k).1 ≤ n) :
    Real.sqrt ((ringState n k).1) + 1 / 2 ≤ Real.sqrt ((ringState n (k + 1)).1) := by
  have hN := (ringN_sq_lower hn hk1 hk).1 hs
  have hA3 : (3 : ℝ) ≤ (ringState n k).1 := by
    exact_mod_cast three_le_ringState hn hk1 (by omega)
  have e : ((ringState n (k + 1)).1 : ℝ) = (ringState n k).1 + ringN n k := by
    rw [(ringStep_spec_at (n := n) (k := k) (by omega)).1]; push_cast; ring
  set s := Real.sqrt ((ringState n k).1)
  have hs2 : s ^ 2 = (ringState n k).1 := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hN0 : (0 : ℝ) ≤ ringN n k := Nat.cast_nonneg _
  have hNs : s + 1 / 4 ≤ ringN n k := by nlinarith
  rw [e, Real.le_sqrt (by linarith) (by linarith)]
  linarith

/-- Northern rows: `√(n - A_{k+1}) + ½ ≤ √(n - A_k)`. -/
theorem sqrt_sub_ringState_succ_le {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n)
    (hs : n ≤ 2 * (ringState n k).1) :
    Real.sqrt ((n : ℝ) - (ringState n (k + 1)).1) + 1 / 2 ≤ Real.sqrt ((n : ℝ) - (ringState n k).1) := by
  have hN := (ringN_sq_lower hn hk1 hk).2 hs
  have hspec := ringStep_spec_at (n := n) (k := k) (by omega)
  have h9 := (hspec.2.2.2 (ringState_lt_of_lt_ringK hk)).2.1
  have hb : (9 : ℝ) ≤ (n : ℝ) - (ringState n k).1 := by
    have : 9 + (ringState n k).1 ≤ n := by omega
    have : (9 : ℝ) + (ringState n k).1 ≤ n := by exact_mod_cast this
    linarith
  have e : ((ringState n (k + 1)).1 : ℝ) = (ringState n k).1 + ringN n k := by
    rw [hspec.1]; push_cast; ring
  have hle := ringState_le_n (n := n) (k := k + 1) hk.le
  set s := Real.sqrt ((n : ℝ) - (ringState n k).1)
  have hs2 : s ^ 2 = (n : ℝ) - (ringState n k).1 := Real.sq_sqrt (by linarith)
  have hs3 : 3 ≤ s := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hN0 : (0 : ℝ) ≤ ringN n k := Nat.cast_nonneg _
  have hNs : s ≤ ringN n k := by nlinarith
  have h1 : (n : ℝ) - (ringState n (k + 1)).1 ≤ (s - 1 / 2) ^ 2 := by rw [e]; linarith
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by linarith)] at h2
  linarith

/-- **(G6), rows**: `K ≤ 4 √n + 4`. -/
theorem ringK_le {n : ℕ} (hn : 10 ≤ n) : (ringK n : ℝ) ≤ 4 * Real.sqrt n + 4 := by
  have hK := ringK_le_two_add hn
  have hsq0 := Real.sqrt_nonneg (n : ℝ)
  -- the southern half
  have hS : (((Ico 1 (ringK n - 1)).filter fun k => 2 * (ringState n k).1 ≤ n).card : ℝ) ≤
      2 * Real.sqrt n + 1 := by
    refine card_le_of_one_le_abs_sub (u := fun k => 2 * Real.sqrt ((ringState n k).1))
      (by positivity) (fun k _ => by positivity) (fun k hk => ?_) (fun k hk l hl hkl => ?_)
    · have := ringState_le_n (n := n) (k := k) (by have := (mem_Ico.1 (mem_filter.1 hk).1).2; omega)
      have := Real.sqrt_le_sqrt this
      linarith
    · -- `k < l` or `l < k`
      have key : ∀ k l, k ∈ (Ico 1 (ringK n - 1)).filter (fun k => 2 * (ringState n k).1 ≤ n) →
          l ∈ (Ico 1 (ringK n - 1)).filter (fun k => 2 * (ringState n k).1 ≤ n) → k < l →
          2 * Real.sqrt ((ringState n k).1) + 1 ≤ 2 * Real.sqrt ((ringState n l).1) := by
        intro k l hk hl hkl
        obtain ⟨hk', hks⟩ := mem_filter.1 hk
        obtain ⟨hl', -⟩ := mem_filter.1 hl
        have hk1 := (mem_Ico.1 hk').1
        have hkK := (mem_Ico.1 hk').2
        have hlK := (mem_Ico.1 hl').2
        have h1 := sqrt_ringState_succ_ge hn hk1 (by omega) hks
        have h2 := Real.sqrt_le_sqrt (ringState_cast_le (n := n) (show k + 1 ≤ l by omega))
        linarith
      rcases lt_or_gt_of_ne hkl with h | h
      · have := key k l hk hl h; rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have := key l k hl hk h; rw [abs_of_nonneg (by linarith)]; linarith
  -- the northern half
  have hN : (((Ico 1 (ringK n - 1)).filter fun k => ¬ 2 * (ringState n k).1 ≤ n).card : ℝ) ≤
      2 * Real.sqrt n + 1 := by
    refine card_le_of_one_le_abs_sub (u := fun k => 2 * Real.sqrt ((n : ℝ) - (ringState n k).1))
      (by positivity) (fun k _ => by positivity) (fun k hk => ?_) (fun k hk l hl hkl => ?_)
    · have : (n : ℝ) - (ringState n k).1 ≤ n := by
        have : (0 : ℝ) ≤ (ringState n k).1 := Nat.cast_nonneg _
        linarith
      have := Real.sqrt_le_sqrt this
      linarith
    · have key : ∀ k l, k ∈ (Ico 1 (ringK n - 1)).filter (fun k => ¬ 2 * (ringState n k).1 ≤ n) →
          l ∈ (Ico 1 (ringK n - 1)).filter (fun k => ¬ 2 * (ringState n k).1 ≤ n) → k < l →
          2 * Real.sqrt ((n : ℝ) - (ringState n l).1) + 1 ≤
            2 * Real.sqrt ((n : ℝ) - (ringState n k).1) := by
        intro k l hk hl hkl
        obtain ⟨hk', hks⟩ := mem_filter.1 hk
        obtain ⟨hl', -⟩ := mem_filter.1 hl
        have hk1 := (mem_Ico.1 hk').1
        have hkK := (mem_Ico.1 hk').2
        have hlK := (mem_Ico.1 hl').2
        have h1 := sqrt_sub_ringState_succ_le hn hk1 (by omega) (by omega)
        have h2 := Real.sqrt_le_sqrt (show (n : ℝ) - (ringState n l).1 ≤
          (n : ℝ) - (ringState n (k + 1)).1 by
            linarith [ringState_cast_le (n := n) (show k + 1 ≤ l by omega)])
        linarith
      rcases lt_or_gt_of_ne hkl with h | h
      · have := key k l hk hl h; rw [abs_of_nonneg (by linarith)]; linarith
      · have := key l k hl hk h; rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  linarith

/-! ### Counts -/

/-- On interior rows, `N_k² ≤ 9 n`. -/
theorem ringN_sq_le {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    (ringN n k : ℝ) ^ 2 ≤ 9 * n := by
  have ha : (ringState n k).1 ≤ n := by
    have := ringState_lt_of_lt_ringK (show k < ringK n by omega); omega
  obtain ⟨hlo, hhi⟩ := ringN_mem_Icc hn hk1 hk
  have hsq := ringTarget_sq n _ ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := two_sqrt_three_pi_lt
  have hc0 := two_sqrt_three_pi_pos
  have ha' : ((ringState n k).1 : ℝ) ≤ n := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ (ringState n k).1 := Nat.cast_nonneg _
  have hprod : ((ringState n k).1 : ℝ) * ((n : ℝ) - (ringState n k).1) ≤ (n : ℝ) ^ 2 / 4 := by
    linarith [sq_nonneg ((n : ℝ) - 2 * (ringState n k).1)]
  have hT : ringTarget n (ringState n k).1 ^ 2 ≤ 10.9 / 4 * n := by
    rw [hsq, div_le_iff₀ hn']
    have : 2 * Real.sqrt 3 * Real.pi * ((ringState n k).1 : ℝ) * ((n : ℝ) - (ringState n k).1) ≤
        10.9 * ((n : ℝ) ^ 2 / 4) := by
      have h0 : 0 ≤ ((ringState n k).1 : ℝ) * ((n : ℝ) - (ringState n k).1) :=
        mul_nonneg ha0 (by linarith)
      calc 2 * Real.sqrt 3 * Real.pi * ((ringState n k).1 : ℝ) * ((n : ℝ) - (ringState n k).1)
          = 2 * Real.sqrt 3 * Real.pi * (((ringState n k).1 : ℝ) * ((n : ℝ) - (ringState n k).1)) := by
            ring
        _ ≤ 10.9 * ((n : ℝ) ^ 2 / 4) := mul_le_mul hc.le hprod h0 (by norm_num)
    linarith
  have hN0 : (0 : ℝ) ≤ ringN n k := Nat.cast_nonneg _
  have hx := ringTarget_nonneg n (ringState n k).1
  nlinarith

/-- A non-bulk row has `k ≤ N_cap²` or `K ≤ k + N_cap²`. -/
theorem not_bulk_index {n k : ℕ} (hn : 10 ≤ n) (hk : k < ringK n) (hb : ¬ RingBulk n k) :
    k ≤ ringCap n ^ 2 ∨ ringK n ≤ k + ringCap n ^ 2 := by
  unfold RingBulk at hb
  push Not at hb
  have ha : (ringState n k).1 ≤ n := by
    have := ringState_lt_of_lt_ringK hk; omega
  have hx := ringTarget_nonneg n (ringState n k).1
  have hsq : ringTarget n (ringState n k).1 ^ 2 < (ringCap n : ℝ) ^ 2 := by
    have := pow_lt_pow_left₀ hb hx (by norm_num : (2 : ℕ) ≠ 0)
    exact this
  obtain ⟨h1, h2⟩ := ringTarget_sq_ge ha (by omega)
  have h3k := three_mul_le_ringState hn hk.le
  have h3K := three_mul_sub_le hn hk.le
  rcases le_total (2 * (ringState n k).1) n with h | h
  · left
    have := h1 h
    have h3k' : (3 * k : ℝ) ≤ (ringState n k).1 := by exact_mod_cast h3k
    have : (k : ℝ) < ((ringCap n ^ 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this.le
  · right
    have := h2 h
    have h3K' : 3 * ((ringK n - k : ℕ) : ℝ) + (ringState n k).1 ≤ n := by exact_mod_cast h3K
    have : ((ringK n - k : ℕ) : ℝ) < (ringCap n : ℝ) ^ 2 := by linarith
    have : ringK n - k < ringCap n ^ 2 := by exact_mod_cast this
    omega

/-- A non-bulk row has `N_k ≤ (5/4) N_cap + 51`. -/
theorem ringN_le_of_not_bulk {n k : ℕ} (hn : 10 ≤ n) (hk : k < ringK n) (hb : ¬ RingBulk n k) :
    (ringN n k : ℝ) ≤ 5 / 4 * ringCap n + 51 := by
  have hcap : (0 : ℝ) ≤ ringCap n := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [ringN_zero hn]; norm_num; linarith
  rcases lt_or_eq_of_le (show k + 1 ≤ ringK n by omega) with hk' | hk'
  · obtain ⟨-, hhi⟩ := ringN_mem_Icc hn hk1 hk'
    unfold RingBulk at hb
    push Not at hb
    linarith
  · have := ringN_last_le (n := n) (by omega)
    rw [show ringK n - 1 = k by omega] at this
    have : (ringN n k : ℝ) ≤ 51 := by exact_mod_cast this
    linarith

/-- **(G6), non-bulk points**: `∑_{k non-bulk} N_k ≤ (2 N_cap² + 1)((5/4) N_cap + 51)`. -/
theorem sum_ringN_not_bulk_le {n : ℕ} (hn : 10 ≤ n) :
    ∑ k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k), (ringN n k : ℝ) ≤
      (2 * (ringCap n : ℝ) ^ 2 + 1) * (5 / 4 * ringCap n + 51) := by
  set c := ringCap n ^ 2
  have hsub : (range (ringK n)).filter (fun k => ¬ RingBulk n k) ⊆
      range (c + 1) ∪ Ico (ringK n - c) (ringK n) := by
    intro k hk
    obtain ⟨hk, hb⟩ := mem_filter.1 hk
    have hk := mem_range.1 hk
    rcases not_bulk_index hn hk hb with h | h
    · exact mem_union_left _ (mem_range.2 (by omega))
    · exact mem_union_right _ (mem_Ico.2 ⟨by omega, hk⟩)
  have hcard : (((range (ringK n)).filter (fun k => ¬ RingBulk n k)).card : ℝ) ≤
      2 * (ringCap n : ℝ) ^ 2 + 1 := by
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range, Nat.card_Ico] at h1
    have h2 : c + 1 + (ringK n - (ringK n - c)) ≤ 2 * c + 1 := by omega
    have h3 : (((range (ringK n)).filter (fun k => ¬ RingBulk n k)).card : ℝ) ≤ (2 * c + 1 : ℕ) := by
      exact_mod_cast h1.trans h2
    simpa [c] using h3
  have hcap : (0 : ℝ) ≤ 5 / 4 * ringCap n + 51 := by positivity
  calc ∑ k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k), (ringN n k : ℝ)
      ≤ ∑ _k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k), (5 / 4 * (ringCap n : ℝ) + 51) :=
        sum_le_sum fun k hk => by
          obtain ⟨hk, hb⟩ := mem_filter.1 hk
          exact ringN_le_of_not_bulk hn (mem_range.1 hk) hb
    _ = (((range (ringK n)).filter (fun k => ¬ RingBulk n k)).card : ℝ) * (5 / 4 * ringCap n + 51) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hcap

end Sphere

end SandierSerfaty

end
