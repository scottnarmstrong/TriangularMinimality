/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Cuts at prescribed masses (screening note, Lemma 4.21, one-dimensional core)

The screening note, Lemma 4.21 (`lem:fillpart`): the rows and the pieces of a
filler part are cut where a cumulative mass reaches prescribed values ("inverse cumulative masses").

* `exists_mass_cuts`: if `F` is continuous on `[a, b]`, `F a = 0`, with slope bounds
  `c₁ (y - x) ≤ F y - F x ≤ c₂ (y - x)` (`c₁ > 0`), and `T : ℕ → ℝ` is nondecreasing on `[0, N]` from
  `T 0 = 0` to `T N = F b`, then there are `a = x 0 ≤ x 1 ≤ ⋯ ≤ x N = b` with `F (x k) = T k`; hence
  `c₁ (x (k+1) - x k) ≤ T (k+1) - T k ≤ c₂ (x (k+1) - x k)`;
* `exists_mem_Icc_of_monotone`: a nondecreasing sequence `x 0 ≤ ⋯ ≤ x N` covers `[x 0, x N]` by the
  intervals `[x k, x (k+1)]`;
* `le_of_monotone_seq`: `x (k+1) ≤ x k'` for `k < k' ≤ N` (disjoint interiors).
-/

open Set

public section

namespace SandierSerfaty.Screening

/-- **Cuts at prescribed masses.** -/
theorem exists_mass_cuts {a b c₁ c₂ : ℝ} {F : ℝ → ℝ} (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hFa : F a = 0) (hc₁ : 0 < c₁)
    (hslope : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      c₁ * (y - x) ≤ F y - F x ∧ F y - F x ≤ c₂ * (y - x))
    {N : ℕ} {T : ℕ → ℝ} (hT0 : T 0 = 0) (hTN : T N = F b) (hTmono : ∀ k < N, T k ≤ T (k + 1)) :
    ∃ x : ℕ → ℝ, x 0 = a ∧ x N = b ∧ (∀ k ≤ N, x k ∈ Icc a b ∧ F (x k) = T k) ∧
      ∀ k < N, x k ≤ x (k + 1) ∧ c₁ * (x (k + 1) - x k) ≤ T (k + 1) - T k ∧
        T (k + 1) - T k ≤ c₂ * (x (k + 1) - x k) := by
  -- the targets lie in `[F a, F b]`
  have hTrange : ∀ k ≤ N, T k ∈ Icc (F a) (F b) := by
    intro k hk
    have hmono : ∀ i j, i ≤ j → j ≤ N → T i ≤ T j := by
      intro i j hij hj
      induction j, hij using Nat.le_induction with
      | base => exact le_rfl
      | succ n hn ih => exact (ih (by omega)).trans (hTmono n (by omega))
    exact ⟨hFa ▸ hT0 ▸ hmono 0 k (Nat.zero_le k) hk, hTN ▸ hmono k N hk le_rfl⟩
  have hivt : ∀ k, ∃ y ∈ Icc a b, k ≤ N → F y = T k := by
    intro k
    by_cases hk : k ≤ N
    · obtain ⟨y, hy, hFy⟩ := intermediate_value_Icc hab hF (hTrange k hk)
      exact ⟨y, hy, fun _ => hFy⟩
    · exact ⟨a, ⟨le_rfl, hab⟩, fun h => absurd h hk⟩
  choose x hxI hxF using hivt
  -- `F` is injective on `[a, b]`
  have hinj : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, F u = F v → u = v := by
    intro u hu v hv huv
    rcases le_total u v with h | h
    · have := (hslope u hu v hv h).1
      nlinarith
    · have := (hslope v hv u hu h).1
      nlinarith
  refine ⟨x, hinj _ (hxI 0) a ⟨le_rfl, hab⟩ (by rw [hxF 0 (Nat.zero_le _), hT0, hFa]),
    hinj _ (hxI N) b ⟨hab, le_rfl⟩ (by rw [hxF N le_rfl, hTN]),
    fun k hk => ⟨hxI k, hxF k hk⟩, fun k hk => ?_⟩
  have hk1 := hxF (k + 1) hk
  have hk0 := hxF k hk.le
  have hle : x k ≤ x (k + 1) := by
    by_contra hlt
    push Not at hlt
    have := (hslope (x (k + 1)) (hxI _) (x k) (hxI _) hlt.le).1
    have := hTmono k hk
    nlinarith
  have := hslope (x k) (hxI _) (x (k + 1)) (hxI _) hle
  rw [hk1, hk0] at this
  exact ⟨hle, this.1, this.2⟩

/-- A nondecreasing sequence `x 0 ≤ ⋯ ≤ x N` (`N ≥ 1`) covers `[x 0, x N]` by the `[x k, x (k+1)]`. -/
theorem exists_mem_Icc_of_monotone {x : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hmono : ∀ k < N, x k ≤ x (k + 1)) {y : ℝ} (hy : y ∈ Icc (x 0) (x N)) :
    ∃ k < N, y ∈ Icc (x k) (x (k + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => exact ⟨0, zero_lt_one, hy⟩
  | succ n hn ih =>
    by_cases h : y ≤ x n
    · obtain ⟨k, hk, hyk⟩ := ih (fun k hk => hmono k (by omega)) ⟨hy.1, h⟩
      exact ⟨k, by omega, hyk⟩
    · exact ⟨n, by omega, ⟨(not_le.1 h).le, hy.2⟩⟩

/-- For a nondecreasing sequence, `x (k+1) ≤ x k'` whenever `k < k' ≤ N`. -/
theorem le_of_monotone_seq {x : ℕ → ℝ} {N : ℕ} (hmono : ∀ k < N, x k ≤ x (k + 1)) {k k' : ℕ}
    (hkk' : k < k') (hk' : k' ≤ N) : x (k + 1) ≤ x k' := by
  induction k', hkk' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (hmono n (by omega))

end SandierSerfaty.Screening

end
