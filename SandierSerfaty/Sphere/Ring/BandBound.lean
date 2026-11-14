/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.PerRowBand

/-!
# Proposition 5.12 (ii): the per-row bound in a band

For a band `[lo, hi]` of `Y_n` (`n ≥ 102`) and `k ∈ [lo, hi]`, with `d = min(k - lo + 1, hi - k + 1)`,
`B_k ≤ N_k e(x_k) + C + C N_k e^{-d/C}` (`Sphere.ringRows_rowB_le_band`).

The interaction sum is split into the rows `k ± m`, `1 ≤ m < d` (in the band; Lemma 5.11 and
`Sphere.ringBand_X_le`), and the others (at distance `≥ (3/56)(d - 1)/N`; Lemma 5.10).
-/

open Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- The in-band rows `k ± m`, `1 ≤ m < d`, as a union of two intervals. -/
theorem erase_filter_near_eq {K k d : ℕ} (hd : d ≤ k + 1) (hK : k + d ≤ K) :
    ((range K).erase k).filter (fun l => k < l + d ∧ l < k + d) =
      Ico (k + 1 - d) k ∪ Ico (k + 1) (k + d) := by
  ext l
  simp only [mem_filter, mem_erase, mem_range, mem_union, mem_Ico]
  omega

/-- The in-band part of the interaction sum. -/
theorem ringBand_near_sum {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n) (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {k d : ℕ} (hd1 : 1 ≤ d) (hkd : lo + d ≤ k + 1)
    (hkd' : k + d ≤ hi + 1) :
    ∑ l ∈ ((range (ringK n)).erase k).filter (fun l => k < l + d ∧ l < k + d), (ringRows n).X k l ≤
      -(2 * (ringN n lo : ℝ)) * ∑ m ∈ range (d - 1), ringLogTerm ((ringRows n).aspect k) (m + 1) +
        2 * ringK1 * ∑ m ∈ range (d - 1),
          ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ))) := by
  have heq : -(2 * (ringN n lo : ℝ)) * ∑ m ∈ range (d - 1), ringLogTerm ((ringRows n).aspect k) (m + 1) +
      2 * ringK1 * ∑ m ∈ range (d - 1),
        ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ))) =
      ∑ m ∈ range (d - 1), (2 * (-(ringN n lo : ℝ) * ringLogTerm ((ringRows n).aspect k) (m + 1)) +
        2 * (ringK1 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ))))) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  rw [heq, erase_filter_near_eq (by omega) (by omega), sum_union (by
    rw [disjoint_left]; intro l h1 h2; simp only [mem_Ico] at h1 h2; omega)]
  rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, show k - (k + 1 - d) = d - 1 by omega,
    show k + d - (k + 1) = d - 1 by omega]
  rw [← sum_range_reflect (fun m => (ringRows n).X k (k + 1 - d + m)) (d - 1), ← sum_add_distrib]
  refine sum_le_sum fun m hm => ?_
  have hm' := mem_range.1 hm
  rw [show k + 1 - d + (d - 1 - 1 - m) = k - (m + 1) by omega]
  have h1 := ringBand_X_le hn hhi hlo hband (i := k) (r := k) (j := k + 1 + m) (by omega) le_rfl
    (by omega) (by omega) (by omega)
  have h2 := ringBand_X_le hn hhi hlo hband (i := k - (m + 1)) (r := k) (j := k) (by omega) (by omega)
    le_rfl (by omega) (by omega)
  rw [show k + 1 + m - k = m + 1 by omega] at h1
  rw [show k - (k - (m + 1)) = m + 1 by omega] at h2
  rw [(ringRows n).X_comm k (k - (m + 1))]
  linarith

/-- The far part of the interaction sum is dominated by the row-sum of Lemma 5.10 beyond
`u₀ = (3/56)(d - 1)/N`. -/
theorem ringBand_far_sum {n lo hi : ℕ} (hn : 102 ≤ n) (hhi : hi < ringK n)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) {k d : ℕ} (hk : k < ringK n) (hd1 : 1 ≤ d)
    (hkd : lo + d ≤ k + 1) (hkd' : k + d ≤ hi + 1) :
    ∑ l ∈ ((range (ringK n)).erase k).filter (fun l => ¬ (k < l + d ∧ l < k + d)), (ringRows n).X k l ≤
      ∑ l ∈ ((range (ringK n)).erase k).filter
          (fun l => 3 / 56 * ((d - 1 : ℕ) : ℝ) / ringN n lo ≤ |ringHeight n k - ringHeight n l|),
        ((min (ringN n k) (ringN n l) : ℕ) : ℝ) *
          ringTheta (((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l|) := by
  have hpos : ∀ l ∈ (range (ringK n)).erase k, 0 ≤ ((min (ringN n k) (ringN n l) : ℕ) : ℝ) *
      ringTheta (((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l|) := by
    intro l hl
    obtain ⟨hlk, hlK⟩ := mem_erase.1 hl
    have hd := ringHeight_dist_ge hn hk (mem_range.1 hlK) (Ne.symm hlk)
    have h3 : (3 : ℝ) ≤ ringN n l := by exact_mod_cast three_le_ringN (by omega) l (mem_range.1 hlK)
    have hM : (0 : ℝ) < ((max (ringN n k) (ringN n l) : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < max (ringN n k) (ringN n l) by
        have := three_le_ringN (n := n) (by omega) l (mem_range.1 hlK); omega)
    have : 0 < 3 / (112 * (ringN n l : ℝ)) := by positivity
    exact mul_nonneg (Nat.cast_nonneg _) (ringTheta_nonneg (mul_pos hM (by linarith)))
  calc _ ≤ ∑ l ∈ ((range (ringK n)).erase k).filter (fun l => ¬ (k < l + d ∧ l < k + d)),
        ((min (ringN n k) (ringN n l) : ℕ) : ℝ) *
          ringTheta (((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l|) := by
        refine sum_le_sum fun l hl => ?_
        obtain ⟨hl1, -⟩ := mem_filter.1 hl
        obtain ⟨hlk, hlK⟩ := mem_erase.1 hl1
        exact ringRows_X_le hn hk (mem_range.1 hlK) (Ne.symm hlk)
    _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro l hl
          obtain ⟨hl1, hfar⟩ := mem_filter.1 hl
          obtain ⟨hlk, hlK⟩ := mem_erase.1 hl1
          refine mem_filter.2 ⟨hl1, ringBand_far_dist hn hhi hband hd1 hkd hkd' (mem_range.1 hlK)
            (by omega)⟩
        · intro l hl _
          exact hpos l (mem_filter.1 hl).1

/-- `S₂ = ∑_{m ≥ 1} m² e^{-(3/56) m}`. -/
@[expose] noncomputable def ringS2 : ℝ :=
  ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ)))

theorem summable_ringS2 :
    Summable fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ))) := by
  have he1 : Real.exp (-(3 / 56)) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have h := summable_pow_mul_geometric_of_norm_lt_one 2 (r := Real.exp (-(3 / 56)))
    (by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact he1)
  refine ((summable_nat_add_iff 1).2 h).congr fun m => ?_
  rw [← Real.exp_nat_mul]; push_cast; ring_nf

theorem sum_le_ringS2 (d : ℕ) :
    ∑ m ∈ range d, ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ))) ≤ ringS2 :=
  summable_ringS2.sum_le_tsum _ fun m _ => by positivity

/-- The partial lattice sum versus the full series: for `x ≥ 1/3`,
`-2N ∑_{m < d-1} log |1 - (-1)^{m+1} e^{-(m+1)x}| ≤ -2N ∑_{m ≥ 1} … + 2N e^{-d/3}/(1 - e^{-1/3})²`. -/
theorem partial_ringLogTerm_le {x N : ℝ} (hx : 1 / 3 ≤ x) (hN : 0 ≤ N) {d : ℕ} (hd : 1 ≤ d) :
    -(2 * N) * ∑ m ∈ range (d - 1), ringLogTerm x (m + 1) ≤
      -(2 * N) * ∑' m : ℕ, ringLogTerm x (m + 1) +
        2 * N * (Real.exp (-(d / 3 : ℝ)) / (1 - Real.exp (-(1 / 3))) ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hs := summable_ringLogTerm hx0
  have hsplit := hs.sum_add_tsum_nat_add (d - 1)
  have htail := abs_tsum_ringLogTerm_tail_le hx0 (d - 1)
  have e : ∀ i, ringLogTerm x (i + (d - 1) + 1) = (fun m => ringLogTerm x (m + 1)) (i + (d - 1)) :=
    fun i => rfl
  rw [show d - 1 + 1 = d by omega] at htail
  set tail := ∑' i : ℕ, ringLogTerm x (i + (d - 1) + 1)
  have hq1 : 0 < 1 - Real.exp (-(1 / 3)) := one_sub_exp_neg_pos (by norm_num)
  have hqx : 1 - Real.exp (-(1 / 3)) ≤ 1 - Real.exp (-x) := by
    have : Real.exp (-x) ≤ Real.exp (-(1 / 3)) := Real.exp_le_exp.2 (by linarith)
    linarith
  have hb : |tail| ≤ Real.exp (-(d / 3 : ℝ)) / (1 - Real.exp (-(1 / 3))) ^ 2 := by
    refine htail.trans ?_
    apply div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.2 ?_) (by positivity)
      (pow_le_pow_left₀ hq1.le hqx 2)
    have : (d : ℝ) / 3 ≤ d * x := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      linarith [mul_le_mul_of_nonneg_left hx this]
    linarith
  have : ∑ m ∈ range (d - 1), ringLogTerm x (m + 1) = ∑' m : ℕ, ringLogTerm x (m + 1) - tail := by
    linarith
  rw [this]
  have h2 : tail ≤ Real.exp (-(d / 3 : ℝ)) / (1 - Real.exp (-(1 / 3))) ^ 2 := (le_abs_self _).trans hb
  have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * N by linarith)
  linarith

/-- **Proposition 5.12 (ii).** There is an absolute `C` such that for every band `[lo, hi]` of `Y_n`,
`n ≥ 102`, and every `k ∈ [lo, hi]`, with `d = min(k - lo + 1, hi - k + 1)`,
`B_k ≤ N_k e(x_k) + C + C N_k e^{-d/C}`. -/
theorem ringRows_rowB_le_band : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n → ∀ lo hi k : ℕ, hi < ringK n →
    RingBulk n lo → (∀ j, lo < j → j ≤ hi → RingCRow n j) → lo ≤ k → k ≤ hi →
    (ringRows n).rowB k ≤ (ringN n k : ℝ) * ringAspectEnergy ((ringRows n).aspect k) + C +
      C * ringN n k * Real.exp (-(((min (k - lo + 1) (hi - k + 1) : ℕ) : ℝ) / C)) := by
  obtain ⟨CX, hCX, hRS⟩ := ringRowSum_le
  have hq1 : 0 < 1 - Real.exp (-(1 / 3)) := one_sub_exp_neg_pos (by norm_num)
  have hS2 : 0 ≤ ringS2 := tsum_nonneg fun m => by positivity
  set A := 891 * Real.exp 198 + 2 * ringK1 * ringS2
  set B := 2 / (1 - Real.exp (-(1 / 3))) ^ 2 + CX * Real.exp (3 / 112)
  have hA : 0 ≤ A := by have := ringK1_pos; positivity
  have hB : 0 ≤ B := by positivity
  refine ⟨A + B + 112 / 3, by positivity, fun n hn lo hi k hhi hlo hband hlok hkhi => ?_⟩
  set C := A + B + 112 / 3
  set d := min (k - lo + 1) (hi - k + 1)
  have hd1 : 1 ≤ d := by simp only [d]; omega
  have hkd : lo + d ≤ k + 1 := by simp only [d]; omega
  have hkd' : k + d ≤ hi + 1 := by simp only [d]; omega
  have hbk := ringBand_bulk hlo hband k hlok hkhi
  obtain ⟨hk1, hkK⟩ := ringBulk_interior (by omega) hbk
  have hNk : ringN n k = ringN n lo := ringBand_N hband k hlok hkhi
  obtain ⟨hx1, hx2⟩ := ringAspect_mem hn hk1 hkK
  set x := (ringRows n).aspect k
  set N := (ringN n lo : ℝ)
  have hN3 : (3 : ℝ) ≤ N := by
    simp only [N]; rw [← hNk]; exact_mod_cast three_le_ringN (by omega) k (by omega)
  -- the pieces
  have hcell := ringCell_le_bulk hn hk1 hkK
  have hnear := ringBand_near_sum hn hhi hlo hband hd1 hkd hkd'
  have hfar := ringBand_far_sum hn hhi hband (show k < ringK n by omega) hd1 hkd hkd'
  have hrs := hRS n hn k (by omega) (3 / 56 * ((d - 1 : ℕ) : ℝ) / ringN n lo) (by positivity)
  rw [hNk] at hcell hfar hrs
  have hpart := partial_ringLogTerm_le hx1 (show 0 ≤ N by linarith) hd1
  have hS := sum_le_ringS2 (d - 1)
  set E := Real.exp (-((d : ℝ) / C))
  have hE0 : 0 < E := Real.exp_pos _
  have hexp1 : Real.exp (-(d / 3 : ℝ)) ≤ E :=
    Real.exp_le_exp.2 (by
      have : (3 : ℝ) ≤ C := by simp only [C]; linarith
      have : (d : ℝ) / C ≤ d / 3 := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) this
      linarith)
  have hexp2 : CX * N * Real.exp (-(N * (3 / 56 * ((d - 1 : ℕ) : ℝ) / N) / 2)) ≤
      CX * Real.exp (3 / 112) * N * E := by
    have e1 : N * (3 / 56 * ((d - 1 : ℕ) : ℝ) / N) / 2 = 3 / 112 * ((d : ℝ) - 1) := by
      rw [Nat.cast_sub hd1]; field_simp; push_cast; ring
    rw [e1]
    have : Real.exp (-(3 / 112 * ((d : ℝ) - 1))) ≤ Real.exp (3 / 112) * E := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hC112 : (112 / 3 : ℝ) ≤ C := by simp only [C]; linarith
      have : (d : ℝ) / C ≤ 3 / 112 * d := by
        rw [div_le_iff₀ (by linarith)]
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        linarith [mul_le_mul_of_nonneg_left hC112 this]
      linarith
    calc CX * N * Real.exp (-(3 / 112 * ((d : ℝ) - 1))) ≤ CX * N * (Real.exp (3 / 112) * E) := by
          gcongr
      _ = _ := by ring
  have t1 : 2 * ringK1 * ∑ m ∈ range (d - 1),
      ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(3 / 56 * ((m + 1 : ℕ) : ℝ))) ≤ 2 * ringK1 * ringS2 :=
    mul_le_mul_of_nonneg_left hS (by have := ringK1_pos; positivity)
  have t2 : 2 * N * (Real.exp (-(d / 3 : ℝ)) / (1 - Real.exp (-(1 / 3))) ^ 2) ≤
      2 * N / (1 - Real.exp (-(1 / 3))) ^ 2 * E := by
    rw [show 2 * N * (Real.exp (-(d / 3 : ℝ)) / (1 - Real.exp (-(1 / 3))) ^ 2) =
      2 * N / (1 - Real.exp (-(1 / 3))) ^ 2 * Real.exp (-(d / 3 : ℝ)) by ring]
    exact mul_le_mul_of_nonneg_left hexp1 (by positivity)
  have t4 : 2 * N / (1 - Real.exp (-(1 / 3))) ^ 2 * E + CX * Real.exp (3 / 112) * N * E ≤ C * N * E := by
    have : 2 * N / (1 - Real.exp (-(1 / 3))) ^ 2 * E + CX * Real.exp (3 / 112) * N * E = B * N * E := by
      simp only [B]; ring
    rw [this]
    have hBC : B ≤ C := by simp only [C]; linarith
    have : 0 ≤ N * E := by positivity
    linarith [mul_le_mul_of_nonneg_right hBC this]
  -- assemble
  unfold RowConfig.rowB
  have eN : (ringRows n).N k = ringN n k := rfl
  have eK : (ringRows n).K = ringK n := rfl
  rw [eN, eK, hNk, ← sum_filter_add_sum_filter_not ((range (ringK n)).erase k)
    (fun l => k < l + d ∧ l < k + d)]
  unfold ringAspectEnergy
  have expand : N * (-(Real.log x / 2) + x / 12 - 2 * ∑' m : ℕ, ringLogTerm x (m + 1)) =
      -(N / 2 * Real.log x) + N * x / 12 - 2 * N * ∑' m : ℕ, ringLogTerm x (m + 1) := by ring
  have hAC : A ≤ C := by simp only [C]; linarith
  have hA' : A = 891 * Real.exp 198 + 2 * ringK1 * ringS2 := rfl
  linarith

end Sphere

end SandierSerfaty

end
