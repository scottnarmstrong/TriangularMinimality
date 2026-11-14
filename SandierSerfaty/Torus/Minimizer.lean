/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.GreenBounds
public import SandierSerfaty.Torus.PairEnergy

/-!
# Existence of minimizers of the torus energy

Paper Lemma `geo:existence` (the last assertion): for `n ≥ 1` the energy
`𝒲_n(a) = π n R_n + π ∑_{i ≠ j} G_n (aᵢ - aⱼ)` attains its minimum over configurations of `n` points
with pairwise distinct classes modulo `√n ℤ[i]`.

The pair energy is `SandierSerfaty.Torus.pairSum`. The proof is a compactness argument on the pair
sum. Since `G_n` is bounded below by a constant `c`, a configuration (reduced modulo the lattice to the
box `[0, √n]²`) whose pair sum is at most a fixed value `M` has every pair term `≤ B` for an explicit
`B`; since `G_n → +∞` at the lattice, all lattice distances `‖aᵢ - aⱼ - γ‖` are then `≥ δ > 0`. This
confines the minimizing sequence to a compact set on which the pair sum is continuous (a lower
semicontinuous extension by `+∞` is not needed).

* `SandierSerfaty.Torus.exists_isMinOn_pairSum`: the pair sum attains its minimum;
* `SandierSerfaty.exists_forall_torusEnergy_le`: the same for `torusEnergy (squareLattice n)`.
-/

open Filter Topology Metric Set Finset

public section

namespace SandierSerfaty

namespace Torus

/-- The pair sum `∑_{i ≠ j} G_Γ (aᵢ - aⱼ)` of a configuration. -/
@[expose] noncomputable def pairSum (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, torusGreen Γ (a i - a j)

section Reduction

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}

/-- The pair sum is invariant under moving the points by lattice vectors. -/
theorem pairSum_sub_lattice (a : Fin N → ℂ) (γ : Fin N → ℂ) (hγ : ∀ i, γ i ∈ Γ) :
    pairSum Γ (fun i => a i - γ i) = pairSum Γ a := by
  unfold pairSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (a i - γ i) - (a j - γ j) = (a i - a j) - (γ i - γ j) := by ring
  rw [this]
  exact torusGreen_sub_period Γ (Γ.sub_mem (hγ i) (hγ j)) _

end Reduction

section Square

variable (n : ℕ) [NeZero n]

/-- Reduction modulo the lattice: every configuration is congruent to one in the box `[0, √n]²`,
with the same distinct-class pattern and the same pair sum. -/
theorem exists_box_rep (b : Fin n → ℂ) :
    ∃ b' : Fin n → ℂ, (∀ i, b' i ∈ box n) ∧
      (∀ i j, b' i - b' j ∈ squareLattice n ↔ b i - b j ∈ squareLattice n) ∧
      pairSum (squareLattice n) b' = pairSum (squareLattice n) b := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  choose γ hγ hbox using fun i => exists_sub_mem_box hn (b i)
  refine ⟨fun i => b i - γ i, hbox, fun i j => ?_, pairSum_sub_lattice _ b γ hγ⟩
  have : (b i - γ i) - (b j - γ j) = (b i - b j) - (γ i - γ j) := by ring
  rw [this]
  constructor
  · intro h
    have := (squareLattice n).add_mem h ((squareLattice n).sub_mem (hγ i) (hγ j))
    simpa using this
  · intro h
    exact (squareLattice n).sub_mem h ((squareLattice n).sub_mem (hγ i) (hγ j))

omit [NeZero n] in
/-- A single term is bounded by the total plus a multiple of `-c` when all terms are `≥ c`. -/
theorem le_sum_add_of_forall_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) {c : ℝ} (hc : c ≤ 0)
    (hf : ∀ i ∈ s, c ≤ f i) {i₀ : ι} (hi₀ : i₀ ∈ s) {N : ℕ} (hN : s.card ≤ N) :
    f i₀ ≤ ∑ i ∈ s, f i + N * (-c) := by
  have h1 : ∑ i ∈ s, f i = f i₀ + ∑ i ∈ s.erase i₀, f i := (Finset.add_sum_erase _ _ hi₀).symm
  have h2 : (s.erase i₀).card • c ≤ ∑ i ∈ s.erase i₀, f i :=
    Finset.card_nsmul_le_sum _ _ _ fun i hi => hf i (Finset.mem_of_mem_erase hi)
  have h3 : (s.erase i₀).card ≤ N := (Finset.card_erase_le).trans hN
  have h4 : ((s.erase i₀).card : ℝ) ≤ N := by exact_mod_cast h3
  rw [nsmul_eq_mul] at h2
  nlinarith

/-- **Existence of a minimizing configuration for the pair sum.** -/
theorem exists_isMinOn_pairSum :
    ∃ a : Fin n → ℂ, (∀ i j, a i - a j ∈ squareLattice n → i = j) ∧
      ∀ b : Fin n → ℂ, (∀ i j, b i - b j ∈ squareLattice n → i = j) →
        pairSum (squareLattice n) a ≤ pairSum (squareLattice n) b := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  set Γ := squareLattice n with hΓ
  obtain ⟨c₀, hc₀⟩ := exists_forall_le_torusGreen n
  set c := min c₀ 0 with hcdef
  have hc : ∀ x, c ≤ torusGreen Γ x := fun x => (min_le_left _ _).trans (hc₀ x)
  have hc0 : c ≤ 0 := min_le_right _ _
  -- a reference configuration in the box
  obtain ⟨a₀, ha₀⟩ := exists_distinct (n := n) hn
  obtain ⟨a₁, hbox₁, hiff₁, hsum₁⟩ := exists_box_rep n a₀
  have hdist₁ : ∀ i j, a₁ i - a₁ j ∈ Γ → i = j := fun i j h => ha₀ i j ((hiff₁ i j).1 h)
  set M := pairSum Γ a₁ with hM
  set B : ℝ := M + ((n : ℝ) * n + n) * (-c) with hB
  -- pair terms of configurations of pair sum `≤ M` are `≤ B`
  have hterm : ∀ a : Fin n → ℂ, pairSum Γ a ≤ M → ∀ i j, i ≠ j →
      torusGreen Γ (a i - a j) ≤ B := by
    intro a hP i j hij
    have hjmem : j ∈ univ.erase i := Finset.mem_erase.2 ⟨hij.symm, mem_univ _⟩
    have hcard : (univ.erase i : Finset (Fin n)).card ≤ n := by
      calc _ ≤ (univ : Finset (Fin n)).card := Finset.card_erase_le
        _ = n := by simp
    have h1 := le_sum_add_of_forall_le (univ.erase i) (fun j => torusGreen Γ (a i - a j)) hc0
      (fun j _ => hc _) hjmem hcard
    have hrow : ∀ i', (n : ℝ) * c ≤ ∑ j ∈ univ.erase i', torusGreen Γ (a i' - a j) := by
      intro i'
      have h2 : (univ.erase i').card • c ≤ ∑ j ∈ univ.erase i', torusGreen Γ (a i' - a j) :=
        Finset.card_nsmul_le_sum _ _ _ fun j _ => hc _
      rw [nsmul_eq_mul] at h2
      have h3 : ((univ.erase i').card : ℝ) ≤ n := by
        have : (univ.erase i').card ≤ n := by
          calc _ ≤ (univ : Finset (Fin n)).card := Finset.card_erase_le
            _ = n := by simp
        exact_mod_cast this
      nlinarith
    have h4 := le_sum_add_of_forall_le (univ : Finset (Fin n))
      (fun i' => ∑ j ∈ univ.erase i', torusGreen Γ (a i' - a j)) (c := (n : ℝ) * c)
      (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (fun i' _ => hrow i') (mem_univ i)
      (N := n) (by simp)
    have h5 : ∑ i' : Fin n, ∑ j ∈ univ.erase i', torusGreen Γ (a i' - a j) = pairSum Γ a := rfl
    simp only [h5] at h4
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  -- separation from the lattice
  obtain ⟨δ, hδ, hδG⟩ := exists_lt_torusGreen_of_norm_sub_lt Γ B
  have hsep : ∀ a : Fin n → ℂ, (∀ i j, a i - a j ∈ Γ → i = j) → pairSum Γ a ≤ M →
      ∀ i j, i ≠ j → δ ≤ infDist (a i - a j) (Γ : Set ℂ) := by
    intro a hd hP i j hij
    rw [le_infDist (⟨0, Γ.zero_mem⟩ : (Γ : Set ℂ).Nonempty)]
    intro γ hγ
    rw [dist_eq_norm]
    by_contra hlt
    push Not at hlt
    have hx : a i - a j ∉ Γ := fun h => hij (hd i j h)
    have := hδG (a i - a j) γ hγ hx hlt
    linarith [hterm a hP i j hij]
  -- the compact set
  set S : Set (Fin n → ℂ) := (Set.pi univ fun _ => box n) ∩
    {a | ∀ i j, i ≠ j → δ ≤ infDist (a i - a j) (Γ : Set ℂ)} with hS
  have hSc : IsCompact S := by
    refine (isCompact_univ_pi fun _ => isCompact_box n).inter_right ?_
    have : {a : Fin n → ℂ | ∀ i j, i ≠ j → δ ≤ infDist (a i - a j) (Γ : Set ℂ)} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {a | δ ≤ infDist (a i - a j) (Γ : Set ℂ)} := by
      ext a; simp
    rw [this]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
    exact isClosed_le continuous_const
      ((continuous_infDist_lattice Γ).comp
        ((continuous_apply i).sub (continuous_apply j)))
  have hSne : ∀ a ∈ S, ∀ i j, i ≠ j → a i - a j ∉ Γ := by
    intro a ha i j hij hmem
    have h1 := ha.2 i j hij
    have h2 : infDist (a i - a j) (Γ : Set ℂ) = 0 := infDist_zero_of_mem hmem
    linarith
  have hcont : ContinuousOn (pairSum Γ) S := by
    intro a ha
    refine ContinuousAt.continuousWithinAt ?_
    unfold pairSum
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j hj => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hG : ContinuousAt (torusGreen Γ) (a i - a j) :=
      (contDiffAt_torusGreen Γ (hSne a ha i j hij)).continuousAt
    exact hG.comp (f := fun a : Fin n → ℂ => a i - a j)
      ((continuous_apply i).sub (continuous_apply j)).continuousAt
  have ha₁S : a₁ ∈ S := ⟨fun i _ => hbox₁ i, hsep a₁ hdist₁ le_rfl⟩
  obtain ⟨a, haS, hamin⟩ := hSc.exists_isMinOn ⟨a₁, ha₁S⟩ hcont
  have hadist : ∀ i j, a i - a j ∈ Γ → i = j := by
    intro i j h
    by_contra hij
    exact hSne a haS i j hij h
  refine ⟨a, hadist, fun b hb => ?_⟩
  obtain ⟨b', hbox', hiff', hsum'⟩ := exists_box_rep n b
  have hdist' : ∀ i j, b' i - b' j ∈ Γ → i = j := fun i j h => hb i j ((hiff' i j).1 h)
  rw [← hsum']
  by_cases hle : pairSum Γ b' ≤ M
  · have hb'S : b' ∈ S := ⟨fun i _ => hbox' i, hsep b' hdist' hle⟩
    exact hamin hb'S
  · push Not at hle
    have : pairSum Γ a ≤ M := hamin ha₁S
    linarith

end Square

end Torus

/-- **Existence of a minimizer** (paper Lemma `geo:existence`): for `n ≥ 1` the torus energy
`𝒲_n` attains its minimum over configurations of `n` points with distinct classes modulo
`√n ℤ[i]`. -/
theorem exists_forall_torusEnergy_le (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Fin n → ℂ, (∀ i j, a i - a j ∈ squareLattice n → i = j) ∧
      ∀ b : Fin n → ℂ, (∀ i j, b i - b j ∈ squareLattice n → i = j) →
        torusEnergy (squareLattice n) a ≤ torusEnergy (squareLattice n) b := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨a, ha, hmin⟩ := Torus.exists_isMinOn_pairSum n
  refine ⟨a, ha, fun b hb => ?_⟩
  have hcov : ZLattice.covolume (squareLattice n) = n := Torus.covolume_squareLattice n
  rw [torusEnergy_eq_pairEnergy hcov a ha, torusEnergy_eq_pairEnergy hcov b hb]
  have := hmin b hb
  unfold Torus.pairSum at this
  have hpi := Real.pi_pos
  nlinarith

end SandierSerfaty

end
