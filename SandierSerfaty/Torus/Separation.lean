/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.SeparationCore
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy

/-!
# Minimizers of the torus energy are separated by `r_* = 1/√π`

Paper Lemma `geo:separation`.

* `SandierSerfaty.one_div_sqrt_pi_le_norm_sub_sub_of_isMin` (**separation**): for `n ≥ 2` and a minimizing
  configuration `a` of `torusEnergy (squareLattice n)` over configurations with distinct classes, all
  lifted distances are at least `1/√π`: `1/√π ≤ ‖a i - a j - γ‖` for all `i, j` and `γ ∈ √n ℤ[i]`
  with `a i - a j - γ ≠ 0` (including different period translates of one point, `i = j`).
* `SandierSerfaty.IsSeparatedConfig`: distinct classes and all lifted distances `≥ 1/√π`.
* `SandierSerfaty.exists_isSeparatedConfig_isMin`: a separated minimizer exists (`n ≥ 2`).
* `SandierSerfaty.mul_triangularEnergy_le_torusEnergy_of_separated` (**the reduction used for the square-torus bound**): if
  `n · W_tri ≤ 𝒲(b)` for every separated configuration `b`, then it holds for every configuration with
  distinct classes. This is how the theorem `mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2) reduces to
  separated configurations.

The proof of separation is `SandierSerfaty.Torus.rStar_le_infDist_of_isMin` (the screening argument),
applied to the global minimum property `Φ(a i) ≤ Φ(x)` obtained from the swap identity.
-/

open Filter Topology Metric Set Finset

public section

namespace SandierSerfaty

/-- A configuration of `n` points of `T_n = ℂ/√n ℤ[i]` is *separated* if the points have pairwise
distinct classes and all lifted distances `‖aᵢ - aⱼ - γ‖`, `γ ∈ √n ℤ[i]`, which do not vanish are at
least `r_* = 1/√π`. -/
@[expose] def IsSeparatedConfig (n : ℕ) (a : Fin n → ℂ) : Prop :=
  (∀ i j, a i - a j ∈ squareLattice n → i = j) ∧
    ∀ (i j : Fin n) (γ : ℂ), γ ∈ squareLattice n → a i - a j - γ ≠ 0 →
      1 / √Real.pi ≤ ‖a i - a j - γ‖

/-- **Separation of minimizers** (paper Lemma `geo:separation`): a minimizing configuration of the
torus energy has all lifted distances at least `r_* = 1/√π`. -/
theorem one_div_sqrt_pi_le_norm_sub_sub_of_isMin (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j)
    (hmin : ∀ b : Fin n → ℂ, (∀ i j, b i - b j ∈ squareLattice n → i = j) →
      torusEnergy (squareLattice n) a ≤ torusEnergy (squareLattice n) b)
    (i j : Fin n) (γ : ℂ) (hγ : γ ∈ squareLattice n) (h : a i - a j - γ ≠ 0) :
    1 / √Real.pi ≤ ‖a i - a j - γ‖ := by
  classical
  have : NeZero n := ⟨by omega⟩
  set Γ := squareLattice n with hΓ
  have hr : Torus.rStar = 1 / √Real.pi := by simp [Torus.rStar]
  rw [← hr]
  by_cases hij : i = j
  · subst hij
    have hγ0 : γ ≠ 0 := fun h0 => h (by rw [h0]; ring)
    have h1 := Torus.sqrt_le_norm_of_mem_squareLattice hγ hγ0
    have h2 := Torus.rStar_lt_sqrt_div_two hn
    have h3 := Torus.rStar_pos
    rw [sub_self, zero_sub, norm_neg]
    linarith
  · -- the global minimum property of `Φ` at `a i`
    have hcov : ZLattice.covolume Γ = n := Torus.covolume_squareLattice n
    have hΦ : ∀ x : ℂ, (∀ p ∈ univ.erase i, x - a p ∉ Γ) →
        ∑ p ∈ univ.erase i, torusGreen Γ (a i - a p) ≤ ∑ p ∈ univ.erase i, torusGreen Γ (x - a p) := by
      intro x hx
      have hb : ∀ p q, Function.update a i x p - Function.update a i x q ∈ Γ → p = q := by
        intro p q hpq
        by_cases hp : p = i <;> by_cases hq : q = i
        · rw [hp, hq]
        · subst hp
          simp only [Function.update_self, Function.update_of_ne hq] at hpq
          exact absurd hpq (hx q (Finset.mem_erase.2 ⟨hq, mem_univ _⟩))
        · subst hq
          simp only [Function.update_self, Function.update_of_ne hp] at hpq
          refine absurd ?_ (hx p (Finset.mem_erase.2 ⟨hp, mem_univ _⟩))
          have := Γ.neg_mem hpq
          simpa using this
        · simp only [Function.update_of_ne hp, Function.update_of_ne hq] at hpq
          exact ha p q hpq
      have hE := hmin _ hb
      rw [torusEnergy_eq_pairEnergy hcov a ha, torusEnergy_eq_pairEnergy hcov _ hb] at hE
      have hpi := Real.pi_pos
      have hP : Torus.pairSum Γ a ≤ Torus.pairSum Γ (Function.update a i x) := by
        unfold Torus.pairSum
        nlinarith
      have := Torus.pairSum_update_sub Γ a i x
      linarith
    have key := Torus.rStar_le_infDist_of_isMin n hn a ha i hΦ j
      (Finset.mem_erase.2 ⟨Ne.symm hij, mem_univ _⟩)
    exact key.trans (Torus.infDist_le_norm_sub Γ hγ _)

/-- A minimizing configuration (over distinct classes) is separated. -/
theorem isSeparatedConfig_of_isMin (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j)
    (hmin : ∀ b : Fin n → ℂ, (∀ i j, b i - b j ∈ squareLattice n → i = j) →
      torusEnergy (squareLattice n) a ≤ torusEnergy (squareLattice n) b) :
    IsSeparatedConfig n a :=
  ⟨ha, fun i j γ hγ h => one_div_sqrt_pi_le_norm_sub_sub_of_isMin n hn a ha hmin i j γ hγ h⟩

/-- There is a separated minimizer of the torus energy (`n ≥ 2`). -/
theorem exists_isSeparatedConfig_isMin (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : Fin n → ℂ, IsSeparatedConfig n a ∧
      ∀ b : Fin n → ℂ, (∀ i j, b i - b j ∈ squareLattice n → i = j) →
        torusEnergy (squareLattice n) a ≤ torusEnergy (squareLattice n) b := by
  obtain ⟨a, ha, hmin⟩ := exists_forall_torusEnergy_le n (by omega)
  exact ⟨a, isSeparatedConfig_of_isMin n hn a ha hmin, hmin⟩

end SandierSerfaty

end
