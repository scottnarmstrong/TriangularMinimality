/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The charge set of a lattice torus

For a lattice `Γ ⊆ ℂ` and charges `a : Fin N → ℂ`, the charge set `{x | ∃ i, x - a i ∈ Γ}` is the
preimage of the charges in `ℂ`. It is closed, countable and consists of isolated points.
-/

open Filter Topology Metric

public section

namespace SandierSerfaty

namespace Torus

/-- The lattice `Γ` is closed in `ℂ`. -/
theorem isClosed_lattice (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] : IsClosed (Γ : Set ℂ) := by
  have : DiscreteTopology Γ.toAddSubgroup := inferInstanceAs (DiscreteTopology Γ)
  exact AddSubgroup.isClosed_of_discreteTopology (U := Γ.toAddSubgroup)

/-- A discrete lattice has a positive minimal norm. -/
theorem exists_norm_lt_imp_eq_zero (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] :
    ∃ ε > 0, ∀ γ ∈ Γ, ‖γ‖ < ε → γ = 0 := by
  have h0 : IsOpen ({0} : Set Γ) := isOpen_discrete _
  obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 h0 0 rfl
  refine ⟨ε, hε, fun γ hγ hn => ?_⟩
  have hmem : (⟨γ, hγ⟩ : Γ) ∈ ball (0 : Γ) ε := by
    rw [mem_ball, dist_zero_right]; exact hn
  have := h hmem
  simpa using congrArg Subtype.val this

/-- The set of points at lattice distance zero from some charge. -/
@[expose] def chargeSet (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) : Set ℂ :=
  {x | ∃ i, x - a i ∈ Γ}

theorem notMem_chargeSet_iff {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} {x : ℂ} :
    x ∉ chargeSet Γ a ↔ ∀ i, x - a i ∉ Γ := by
  simp [chargeSet]

theorem isClosed_chargeSet (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] {N : ℕ} (a : Fin N → ℂ) :
    IsClosed (chargeSet Γ a) := by
  have : chargeSet Γ a = ⋃ i, (fun x : ℂ => x - a i) ⁻¹' (Γ : Set ℂ) := by
    ext x; simp [chargeSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => (isClosed_lattice Γ).preimage (by fun_prop)

theorem countable_chargeSet (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}
    (a : Fin N → ℂ) : (chargeSet Γ a).Countable := by
  have hc : Countable (Γ : Set ℂ) := inferInstanceAs (Countable Γ)
  have hΓ : (Γ : Set ℂ).Countable := Set.countable_coe_iff.1 hc
  have : chargeSet Γ a ⊆ ⋃ i, (fun γ : ℂ => a i + γ) '' (Γ : Set ℂ) := by
    intro x ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, ⟨x - a i, hi, by ring⟩⟩
  exact (Set.countable_iUnion fun i => hΓ.image _).mono this

/-- The points of the charge set are isolated. -/
theorem eventually_notMem_chargeSet (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] {N : ℕ}
    (a : Fin N → ℂ) (p : ℂ) : ∀ᶠ q in 𝓝[≠] p, q ∉ chargeSet Γ a := by
  obtain ⟨ε, hε, hε'⟩ := exists_norm_lt_imp_eq_zero Γ
  have key : ∀ i, ∀ᶠ q in 𝓝[≠] p, q - a i ∉ Γ := by
    intro i
    by_cases hpi : p - a i ∈ Γ
    · have h1 : ∀ᶠ q in 𝓝[≠] p, q ∈ ball p ε ∧ q ≠ p :=
        (eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds p hε)).and self_mem_nhdsWithin
      filter_upwards [h1] with q hq hqΓ
      have hd : q - p ∈ Γ := by
        have := Γ.sub_mem hqΓ hpi
        simpa using this
      have := hε' _ hd (by simpa [dist_eq_norm] using hq.1)
      exact hq.2 (sub_eq_zero.1 this)
    · have ho : IsOpen ((fun q : ℂ => q - a i) ⁻¹' (Γ : Set ℂ)ᶜ) :=
        (isClosed_lattice Γ).isOpen_compl.preimage (by fun_prop)
      exact eventually_nhdsWithin_of_eventually_nhds (ho.mem_nhds hpi)
  filter_upwards [eventually_all.2 key] with q hq hqP
  obtain ⟨i, hi⟩ := hqP
  exact hq i hi

end Torus

end SandierSerfaty

end
