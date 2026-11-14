/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.SquareLattice
public import SandierSerfaty.Torus.Lattice
public import SandierSerfaty.Torus.ChargeSet
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Geometry of the square lattice `√n ℤ[i]`

Elementary facts about `squareLattice n = √n ℤ[i] ⊆ ℂ` used for the minimizers of the torus energy
(paper Lemmas `geo:existence` and `geo:separation`):

* membership: `γ ∈ squareLattice n ↔ ∃ p q : ℤ, γ = p √n + i q √n`;
* the shortest nonzero lattice vector has length `√n` (`sqrt_le_norm_of_mem_squareLattice`);
* every point is congruent modulo the lattice to a point of the compact box `[0, √n]²`
  (`exists_sub_mem_box`, `isCompact_box`);
* the lattice distance `Metric.infDist z Γ` is `Γ`-periodic and equals `‖z - γ₀‖` when `‖z - γ₀‖ < √n / 2`;
* existence of `n` points with pairwise distinct classes.
-/

open Filter Topology Metric Set

public section

namespace SandierSerfaty

namespace Torus

/-- The closed box `[0, √n] × [0, √n]`, a fundamental box of `squareLattice n`. -/
@[expose] def box (n : ℕ) : Set ℂ := {z | z.re ∈ Icc 0 (√n) ∧ z.im ∈ Icc 0 (√n)}

theorem isClosed_box (n : ℕ) : IsClosed (box n) := by
  have : box n = (Complex.re ⁻¹' Icc 0 (√n)) ∩ (Complex.im ⁻¹' Icc 0 (√n)) := by
    ext z; simp [box]
  rw [this]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

theorem isCompact_box (n : ℕ) : IsCompact (box n) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_box n) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * √n)).subset ?_
  intro z hz
  simp only [box, mem_Icc] at hz
  rw [mem_closedBall, dist_zero_right]
  have h := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hz.1.1, abs_of_nonneg hz.2.1] at h
  linarith [hz.1.2, hz.2.2]

section Lattice

variable {n : ℕ}

theorem mem_squareLattice_iff {γ : ℂ} :
    γ ∈ squareLattice n ↔ ∃ p q : ℤ, γ = ⟨p * √n, q * √n⟩ := by
  unfold squareLattice
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, rfl⟩
    exact ⟨p, q, by apply Complex.ext <;> simp⟩
  · rintro ⟨p, q, rfl⟩
    exact ⟨p, q, by apply Complex.ext <;> simp⟩

theorem mk_mem_squareLattice (p q : ℤ) : (⟨p * √n, q * √n⟩ : ℂ) ∈ squareLattice n :=
  mem_squareLattice_iff.2 ⟨p, q, rfl⟩

/-- The shortest nonzero vector of `√n ℤ[i]` has length `√n`. -/
theorem sqrt_le_norm_of_mem_squareLattice {γ : ℂ} (hγ : γ ∈ squareLattice n) (h0 : γ ≠ 0) :
    √n ≤ ‖γ‖ := by
  obtain ⟨p, q, rfl⟩ := mem_squareLattice_iff.1 hγ
  have hpq : (p ≠ 0 ∨ q ≠ 0) := by
    by_contra h
    push Not at h
    apply h0
    apply Complex.ext <;> simp [h.1, h.2]
  have h1 : (1 : ℝ) ≤ (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
    rcases hpq with h | h
    · have : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ p ^ 2 := by nlinarith [sq_pos_of_ne_zero h]
        exact_mod_cast this
      nlinarith [sq_nonneg (q : ℝ)]
    · have : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ q ^ 2 := by nlinarith [sq_pos_of_ne_zero h]
        exact_mod_cast this
      nlinarith [sq_nonneg (p : ℝ)]
  have hL : (0 : ℝ) ≤ √n := Real.sqrt_nonneg _
  rw [Complex.norm_def, Complex.normSq_mk]
  apply Real.le_sqrt_of_sq_le
  have : (√n) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith [mul_nonneg hL hL]

/-- Every point is congruent modulo `√n ℤ[i]` to a point of the box `[0, √n]²`. -/
theorem exists_sub_mem_box (hn : 1 ≤ n) (x : ℂ) : ∃ γ ∈ squareLattice n, x - γ ∈ box n := by
  have hLpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  refine ⟨⟨⌊x.re / √n⌋ * √n, ⌊x.im / √n⌋ * √n⟩, mk_mem_squareLattice _ _, ?_⟩
  have h1 := Int.floor_le (x.re / √n)
  have h2 := Int.lt_floor_add_one (x.re / √n)
  have h3 := Int.floor_le (x.im / √n)
  have h4 := Int.lt_floor_add_one (x.im / √n)
  rw [le_div_iff₀ hLpos] at h1 h3
  rw [div_lt_iff₀ hLpos] at h2 h4
  simp only [box, mem_ofPred_eq, mem_Icc, Complex.sub_re, Complex.sub_im]
  refine ⟨⟨by linarith, by nlinarith⟩, ⟨by linarith, by nlinarith⟩⟩

/-- There are `n` points with pairwise distinct classes modulo `√n ℤ[i]`. -/
theorem exists_distinct (hn : 1 ≤ n) :
    ∃ a : Fin n → ℂ, ∀ i j, a i - a j ∈ squareLattice n → i = j := by
  have hLpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun i => ⟨(i : ℕ) * √n / n, 0⟩, fun i j hij => ?_⟩
  obtain ⟨p, q, h⟩ := mem_squareLattice_iff.1 hij
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re] at hre
  have h2 : ((i : ℕ) : ℝ) - (j : ℕ) = p * n := by
    field_simp at hre
    nlinarith [hre]
  have h3 : ((i : ℕ) : ℤ) - (j : ℕ) = p * n := by exact_mod_cast h2
  have hi := i.2
  have hj := j.2
  have hp : p = 0 := by
    by_contra hp
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    rcases lt_or_gt_of_ne hp with h | h
    · have : p ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ p := by omega
      nlinarith
  subst hp
  apply Fin.ext
  omega

end Lattice

section InfDist

variable (Γ : Submodule ℤ ℂ)

theorem infDist_add_mem {γ : ℂ} (hγ : γ ∈ Γ) (z : ℂ) :
    infDist (z + γ) (Γ : Set ℂ) = infDist z (Γ : Set ℂ) := by
  have hne : (Γ : Set ℂ).Nonempty := ⟨0, Γ.zero_mem⟩
  have key : ∀ (w : ℂ) (δ : ℂ), δ ∈ Γ → infDist w (Γ : Set ℂ) ≤ infDist (w + δ) (Γ : Set ℂ) := by
    intro w δ hδ
    rw [le_infDist hne]
    intro y hy
    have : infDist w (Γ : Set ℂ) ≤ dist w (y - δ) := infDist_le_dist_of_mem (Γ.sub_mem hy hδ)
    calc infDist w (Γ : Set ℂ) ≤ dist w (y - δ) := this
      _ = dist (w + δ) y := by rw [dist_eq_norm, dist_eq_norm]; congr 1; ring_nf
  refine le_antisymm ?_ (key z γ hγ)
  have := key (z + γ) (-γ) (Γ.neg_mem hγ)
  simpa using this

theorem infDist_le_norm_sub {γ : ℂ} (hγ : γ ∈ Γ) (z : ℂ) : infDist z (Γ : Set ℂ) ≤ ‖z - γ‖ := by
  rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hγ

theorem exists_norm_sub_lt_of_infDist_lt {z : ℂ} {r : ℝ} (h : infDist z (Γ : Set ℂ) < r) :
    ∃ γ ∈ Γ, ‖z - γ‖ < r := by
  obtain ⟨y, hy, hd⟩ := (infDist_lt_iff (⟨0, Γ.zero_mem⟩ : (Γ : Set ℂ).Nonempty)).1 h
  exact ⟨y, hy, by rwa [← dist_eq_norm]⟩

theorem infDist_pos_of_notMem [DiscreteTopology Γ] {z : ℂ} (hz : z ∉ Γ) :
    0 < infDist z (Γ : Set ℂ) :=
  ((isClosed_lattice Γ).notMem_iff_infDist_pos (⟨0, Γ.zero_mem⟩ : (Γ : Set ℂ).Nonempty)).1 hz

theorem continuous_infDist_lattice : Continuous fun z : ℂ => infDist z (Γ : Set ℂ) :=
  continuous_infDist_pt _

end InfDist

section InfDistSquare

variable {n : ℕ}

/-- Near a lattice point `γ₀` (within `√n / 2`) the lattice distance is the distance to `γ₀`. -/
theorem infDist_eq_norm_sub {z γ₀ : ℂ} (hγ₀ : γ₀ ∈ squareLattice n) (h : ‖z - γ₀‖ < √n / 2) :
    infDist z (squareLattice n : Set ℂ) = ‖z - γ₀‖ := by
  refine le_antisymm (infDist_le_norm_sub _ hγ₀ z) ?_
  rw [le_infDist (⟨0, (squareLattice n).zero_mem⟩ : (squareLattice n : Set ℂ).Nonempty)]
  intro y hy
  by_cases hyγ : y = γ₀
  · subst hyγ; simp [dist_eq_norm]
  · have h1 := sqrt_le_norm_of_mem_squareLattice ((squareLattice n).sub_mem hy hγ₀)
      (sub_ne_zero.2 hyγ)
    have h2 : ‖y - γ₀‖ ≤ ‖z - y‖ + ‖z - γ₀‖ := by
      calc ‖y - γ₀‖ = ‖(z - γ₀) - (z - y)‖ := by congr 1; ring
        _ ≤ ‖z - γ₀‖ + ‖z - y‖ := norm_sub_le _ _
        _ = _ := by ring
    rw [dist_eq_norm]
    linarith

end InfDistSquare

end Torus

end SandierSerfaty

end
