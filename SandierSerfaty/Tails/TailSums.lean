/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Splitting double sums off the finite block (paper §6.5)

For `q ≥ 0` summable, the sum of `q_i q_j` over the pairs `(i, j)` **not** in the block `{i, j < 39}` is
`2AΔ + Δ²` with `A = ∑_{i<39} q_i` and `Δ = ∑_j q_{j+39}` (`tsum_rest`): the paper's `8N𝔞 + 16𝔞²`.

* `notBlock ij`: the predicate `¬ (ij.1 < 39 ∧ ij.2 < 39)`;
* `summable_rest`: summability of `q_i q_j` on the complement of the block, and of any term dominated by it;
* `exists_bound_finite`: uniform bound of finitely many continuous functions on a compact set.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

/-- `q_i q_j` off the finite block, `0` on it. -/
@[expose] def rest (q : ℕ → ℝ) (ij : ℕ × ℕ) : ℝ :=
  if ij.1 < 39 ∧ ij.2 < 39 then 0 else q ij.1 * q ij.2

theorem summable_prodq {q : ℕ → ℝ} (hq : ∀ i, 0 ≤ q i) (hs : Summable q) :
    Summable fun ij : ℕ × ℕ => q ij.1 * q ij.2 :=
  Summable.mul_of_nonneg hs hs hq hq

theorem rest_nonneg {q : ℕ → ℝ} (hq : ∀ i, 0 ≤ q i) (ij : ℕ × ℕ) : 0 ≤ rest q ij := by
  unfold rest; split_ifs
  · exact le_rfl
  · exact mul_nonneg (hq _) (hq _)

theorem rest_le {q : ℕ → ℝ} (hq : ∀ i, 0 ≤ q i) (ij : ℕ × ℕ) : rest q ij ≤ q ij.1 * q ij.2 := by
  unfold rest; split_ifs
  · exact mul_nonneg (hq _) (hq _)
  · exact le_rfl

theorem summable_rest {q : ℕ → ℝ} (hq : ∀ i, 0 ≤ q i) (hs : Summable q) : Summable (rest q) :=
  Summable.of_nonneg_of_le (rest_nonneg hq) (rest_le hq) (summable_prodq hq hs)

theorem tsum_rest {q : ℕ → ℝ} (hq : ∀ i, 0 ≤ q i) (hs : Summable q) :
    ∑' ij, rest q ij =
      2 * (∑ i ∈ Finset.range 39, q i) * (∑' j, q (j + 39)) + (∑' j, q (j + 39)) ^ 2 := by
  classical
  set blk : ℕ × ℕ → ℝ := fun ij => if ij.1 < 39 ∧ ij.2 < 39 then q ij.1 * q ij.2 else 0 with hblk
  have e : (fun ij : ℕ × ℕ => q ij.1 * q ij.2) = fun ij => blk ij + rest q ij := by
    funext ij; unfold blk rest; split_ifs <;> simp
  have hblk0 : ∀ ij ∉ (Finset.range 39 ×ˢ Finset.range 39), blk ij = 0 := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, not_and] at hij
    unfold blk
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hij h1 h2
  have hbs : Summable blk := summable_of_ne_finset_zero hblk0
  have hbt : ∑' ij, blk ij = (∑ i ∈ Finset.range 39, q i) ^ 2 := by
    rw [tsum_eq_sum hblk0, Finset.sum_product, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    simp [blk, hi', hj']
  have hT : ∑ i ∈ Finset.range 39, q i + ∑' j, q (j + 39) = ∑' i, q i := hs.sum_add_tsum_nat_add 39
  have hfull : (∑' i, q i) * (∑' i, q i) = ∑' ij : ℕ × ℕ, q ij.1 * q ij.2 :=
    tsum_mul_tsum_of_summable_norm (hs.abs.congr fun _ => (Real.norm_eq_abs _).symm)
      (hs.abs.congr fun _ => (Real.norm_eq_abs _).symm)
  have hsum : ∑' ij : ℕ × ℕ, q ij.1 * q ij.2 = ∑' ij, blk ij + ∑' ij, rest q ij := by
    rw [e]; exact hbs.tsum_add (summable_rest hq hs)
  rw [hbt, ← hfull, ← hT] at hsum
  nlinarith [hsum]

/-- Finitely many continuous functions are uniformly bounded on a compact set. -/
theorem exists_bound_finite {K : Set ℝ} (hK : IsCompact K) (n : ℕ) {F : ℕ → ℝ → ℝ}
    (hF : ∀ i < n, ContinuousOn (F i) K) : ∃ C, 0 ≤ C ∧ ∀ i < n, ∀ t ∈ K, |F i t| ≤ C := by
  induction n with
  | zero => exact ⟨0, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨C, hC0, hC⟩ := ih fun i hi => hF i (by omega)
    obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn (hF n (by omega))
    refine ⟨max C (max C' 0), le_max_of_le_right (le_max_right _ _), fun i hi t ht => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact (hC i h t ht).trans (le_max_left _ _)
    · subst h
      have := hC' t ht
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans (le_max_right _ _))

end Tails

end SandierSerfaty

end
