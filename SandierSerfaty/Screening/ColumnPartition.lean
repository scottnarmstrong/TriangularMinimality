/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Integer-mass partitions of an interval (screening note, Lemma 4.18, one-dimensional core)

The screening note, Lemma 4.18 (`lem:cuts`), the construction step: on
`[x, L]` with a continuous cumulative mass `μ` whose increments over every window of width `ℓ` are at
least `1`, cut greedily: while `L - u_{k-1} ≥ 3ℓ`, choose `u_k ∈ [u_{k-1} + ℓ, u_{k-1} + 2ℓ]` with
`μ(u_k) - μ(u_{k-1}) ∈ ℤ` (intermediate value theorem); the last step `[u_{K-1}, L]` has width in
`[ℓ, 3ℓ)`.

* `SandierSerfaty.Screening.IsPartition ℓ x L K u`: `x = u 0`, `u K = L`, `K ≥ 1`, the steps
  `u (k+1) - u k` in `[ℓ, 2ℓ]` for `k + 1 < K` and the last step in `[ℓ, 3ℓ)`;
* `exists_partition`: the greedy cut, with integer increments of `μ` on all non-last steps;
* `IsPartition.mono`, `IsPartition.mem_Icc`, `IsPartition.le_pred_last`: monotonicity and position.
-/

open Set

public section

namespace SandierSerfaty.Screening

/-- A partition `x = u 0 < u 1 < ⋯ < u K = L` (`K ≥ 1`) with steps in `[ℓ, 2ℓ]`, except the last step,
in `[ℓ, 3ℓ)` (screening note, Lemma 4.18(a)). -/
structure IsPartition (ℓ x L : ℝ) (K : ℕ) (u : ℕ → ℝ) : Prop where
  one_le : 1 ≤ K
  zero : u 0 = x
  last : u K = L
  step : ∀ k, k + 1 < K → u (k + 1) - u k ∈ Icc ℓ (2 * ℓ)
  stepLast : u K - u (K - 1) ∈ Ico ℓ (3 * ℓ)

namespace IsPartition

variable {ℓ x L : ℝ} {K : ℕ} {u : ℕ → ℝ}

/-- Every step (last one included) has width in `[ℓ, 3ℓ)`; in particular at least `ℓ`. -/
theorem step_mem (h : IsPartition ℓ x L K u) (hℓ : 0 ≤ ℓ) {k : ℕ} (hk : k + 1 ≤ K) :
    u (k + 1) - u k ∈ Icc ℓ (3 * ℓ) := by
  rcases lt_or_eq_of_le hk with hk | hk
  · have := h.step k hk; exact ⟨this.1, this.2.trans (by linarith)⟩
  · have := h.stepLast
    rw [← hk, Nat.add_sub_cancel] at this
    exact ⟨this.1, this.2.le⟩

theorem mono (h : IsPartition ℓ x L K u) (hℓ : 0 ≤ ℓ) {k k' : ℕ} (hkk' : k ≤ k') (hk' : k' ≤ K) :
    u k ≤ u k' := by
  induction k', hkk' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have := (h.step_mem hℓ hk').1
    linarith [ih (by omega)]

theorem mem_Icc (h : IsPartition ℓ x L K u) (hℓ : 0 ≤ ℓ) {k : ℕ} (hk : k ≤ K) :
    u k ∈ Icc x L := by
  refine ⟨?_, ?_⟩
  · rw [← h.zero]; exact h.mono hℓ (Nat.zero_le k) hk
  · rw [← h.last]; exact h.mono hℓ hk le_rfl

/-- The non-last points lie left of `u (K - 1)`. -/
theorem le_pred_last (h : IsPartition ℓ x L K u) (hℓ : 0 ≤ ℓ) {k : ℕ} (hk : k ≤ K - 1) :
    u k ≤ u (K - 1) :=
  h.mono hℓ hk (Nat.sub_le K 1)

/-- The non-last increments of a function with integer increments add up to an integer. -/
theorem exists_int_sub_of_int_steps (_h : IsPartition ℓ x L K u) {μ : ℝ → ℝ}
    (hI : ∀ k, k + 1 < K → ∃ z : ℤ, μ (u (k + 1)) - μ (u k) = z) :
    ∃ Z : ℤ, μ (u (K - 1)) - μ (u 0) = Z := by
  suffices H : ∀ n, n ≤ K - 1 → ∃ Z : ℤ, μ (u n) - μ (u 0) = Z from H _ le_rfl
  intro n hn
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨Z, hZ⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hI n (by omega)
    exact ⟨Z + z, by push_cast; linarith⟩

end IsPartition

/-- The single-step partition `[x, L]` when `L - x ∈ [ℓ, 3ℓ)`. -/
theorem isPartition_single {ℓ x L : ℝ} (h1 : ℓ ≤ L - x) (h2 : L - x < 3 * ℓ) :
    IsPartition ℓ x L 1 (fun k => if k = 0 then x else L) where
  one_le := le_rfl
  zero := by simp
  last := by simp
  step k hk := by omega
  stepLast := by simpa using ⟨h1, h2⟩

/-- **The greedy integer cut** (screening note, Lemma 4.18, construction): if `μ` is continuous on `[x₀, L]`,
`L - x₀ ≥ ℓ > 0`, and `μ(y + 2ℓ) - μ(y + ℓ) ≥ 1` whenever `x₀ ≤ y`, `y + 2ℓ ≤ L`, then there is a
partition of `[x₀, L]` (`IsPartition`) such that `μ` has integer increments on all non-last steps. -/
theorem exists_partition {ℓ x₀ L : ℝ} (hℓ : 0 < ℓ) {μ : ℝ → ℝ} (hμ : ContinuousOn μ (Icc x₀ L))
    (hinc : ∀ y, x₀ ≤ y → y + 2 * ℓ ≤ L → 1 ≤ μ (y + 2 * ℓ) - μ (y + ℓ)) (hL : ℓ ≤ L - x₀) :
    ∃ K u, IsPartition ℓ x₀ L K u ∧ ∀ k, k + 1 < K → ∃ z : ℤ, μ (u (k + 1)) - μ (u k) = z := by
  suffices H : ∀ n : ℕ, ∀ x, x₀ ≤ x → ℓ ≤ L - x → L - x < (n + 3) * ℓ →
      ∃ K u, IsPartition ℓ x L K u ∧ ∀ k, k + 1 < K → ∃ z : ℤ, μ (u (k + 1)) - μ (u k) = z by
    obtain ⟨n, hn⟩ := exists_nat_gt ((L - x₀) / ℓ)
    refine H n x₀ le_rfl hL ?_
    rw [div_lt_iff₀ hℓ] at hn
    nlinarith
  have base : ∀ x, ℓ ≤ L - x → L - x < 3 * ℓ →
      ∃ K u, IsPartition ℓ x L K u ∧ ∀ k, k + 1 < K → ∃ z : ℤ, μ (u (k + 1)) - μ (u k) = z :=
    fun x h1 h2 => ⟨1, _, isPartition_single h1 h2, fun k hk => by omega⟩
  intro n
  induction n with
  | zero =>
    intro x _ h1 h2
    exact base x h1 (by simpa using h2)
  | succ n ih =>
    intro x hx h1 h2
    by_cases h3 : L - x < 3 * ℓ
    · exact base x h1 h3
    push Not at h3
    -- the intermediate value step on `[x + ℓ, x + 2ℓ]`
    have hcont : ContinuousOn (fun y => μ y - μ x) (Icc (x + ℓ) (x + 2 * ℓ)) :=
      (hμ.mono (Icc_subset_Icc (by linarith) (by linarith))).sub continuousOn_const
    have hgap := hinc x hx (by linarith)
    set a := μ (x + ℓ) - μ x
    set z : ℤ := ⌈a⌉
    have hz1 : a ≤ z := Int.le_ceil a
    have hz2 : (z : ℝ) ≤ μ (x + 2 * ℓ) - μ x := by
      have := Int.ceil_lt_add_one a
      linarith
    obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc (by linarith) hcont ⟨hz1, hz2⟩
    obtain ⟨K, u, hP, hI⟩ := ih y (by linarith [hy.1]) (by linarith [hy.2])
      (by push_cast at h2 ⊢; linarith [hy.1])
    refine ⟨K + 1, fun k => if k = 0 then x else u (k - 1), ⟨by omega, by simp, ?_, ?_, ?_⟩, ?_⟩
    · simp [hP.last]
    · intro k hk
      rcases k with _ | k
      · simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self, hP.zero]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        exact hP.step k (by omega)
    · have hK := hP.one_le
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      simpa using hP.stepLast
    · intro k hk
      rcases k with _ | k
      · refine ⟨z, ?_⟩
        simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self, hP.zero]
        exact hfy
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        exact hI k (by omega)

end SandierSerfaty.Screening

end
