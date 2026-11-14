/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.PairEnergySetup

/-!
# The punctured set and its interaction with the bumps

`punctureSet Γ a η = ⋃ i, ⋃ γ ∈ Γ, B(a i + γ, η)`: the periodic union of the `η`-balls around the
charge points. For `η ≤ ρ` the periodized bump is `1` on it, and near the charge `a i` it is just the
ball `B(a i, η)`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

/-- The union of the `η`-balls around all charge points `a i + γ`. -/
@[expose] def punctureSet (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (η : ℝ) : Set ℂ :=
  ⋃ i, ⋃ γ ∈ Γ, ball (a i + γ) η

variable {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ}

theorem mem_punctureSet {η : ℝ} {x : ℂ} :
    x ∈ punctureSet Γ a η ↔ ∃ i, ∃ γ ∈ Γ, ‖x - (a i + γ)‖ < η := by
  simp [punctureSet, mem_ball, dist_eq_norm]

theorem isOpen_punctureSet (η : ℝ) : IsOpen (punctureSet Γ a η) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem punctureSet_add_period {η : ℝ} {δ : ℂ} (hδ : δ ∈ Γ) (x : ℂ) :
    x + δ ∈ punctureSet Γ a η ↔ x ∈ punctureSet Γ a η := by
  rw [mem_punctureSet, mem_punctureSet]
  constructor
  · rintro ⟨i, γ, hγ, h⟩
    refine ⟨i, γ - δ, Γ.sub_mem hγ hδ, ?_⟩
    have : x - (a i + (γ - δ)) = x + δ - (a i + γ) := by ring
    rwa [this]
  · rintro ⟨i, γ, hγ, h⟩
    refine ⟨i, γ + δ, Γ.add_mem hγ hδ, ?_⟩
    have : x + δ - (a i + (γ + δ)) = x - (a i + γ) := by ring
    rwa [this]

/-- Charge points belong to the charge set. -/
theorem add_mem_chargeSet' {i : Fin N} {γ : ℂ} (hγ : γ ∈ Γ) : a i + γ ∈ chargeSet Γ a :=
  ⟨i, by simpa using hγ⟩

variable [DiscreteTopology Γ] [IsZLattice ℝ Γ]

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
/-- The periodized bump is `1` on the puncture set for `η ≤ ρ`. -/
theorem periodizedBump_eq_one_of_mem_punctureSet {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ρ ≤ ‖q - a i‖)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) {η : ℝ} (hη : η ≤ ρ) {x : ℂ}
    (hx : x ∈ punctureSet Γ a η) : periodizedBump Γ hρ a x = 1 := by
  obtain ⟨i, γ, hγ, hlt⟩ := mem_punctureSet.1 hx
  exact periodizedBump_eq_one hρ hsep ha (add_mem_chargeSet' hγ) (hlt.trans_le hη)

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
/-- Near the charge `a i` the puncture set is the ball `B(a i, η)`. -/
theorem mem_punctureSet_iff_of_near {ρ : ℝ}
    (hsep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ρ ≤ ‖q - a i‖) {η : ℝ} (hηρ : η ≤ ρ) (hρ : 0 < ρ)
    (i : Fin N) {x : ℂ} (hx : ‖x - a i‖ < 2 * ρ) :
    x ∈ punctureSet Γ a η ↔ ‖x - a i‖ < η := by
  constructor
  · intro h
    obtain ⟨j, γ, hγ, hlt⟩ := mem_punctureSet.1 h
    have hP : a j + γ ∈ chargeSet Γ a := add_mem_chargeSet' hγ
    by_cases hq : a j + γ = a i
    · rw [← hq]; exact hlt
    · have h1 := hsep i _ hP hq
      have h2 : ‖(a j + γ) - a i‖ ≤ ‖x - (a j + γ)‖ + ‖x - a i‖ := by
        calc ‖(a j + γ) - a i‖ = ‖(x - a i) - (x - (a j + γ))‖ := by ring_nf
          _ ≤ ‖x - a i‖ + ‖x - (a j + γ)‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      linarith
  · intro h
    exact mem_punctureSet.2 ⟨i, 0, Γ.zero_mem, by simpa using h⟩

end Torus

end SandierSerfaty

end
