/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.ScreenedGreen
public import SandierSerfaty.Torus.Minimizer

/-!
# The screening argument for the separation of minimizers

Paper proof of Lemma `geo:separation`. Fix `n ≥ 2`, a configuration `a`
of `n` points with distinct classes modulo `Γ = √n ℤ[i]`, and one point `q = a k`. Put
`Φ(x) = Σ_{p ≠ k} G(x - a p)` and suppose `Φ(a k) ≤ Φ(x)` for all admissible `x` (the *global
minimum* hypothesis `hΦ`, which follows from minimality of the energy by the swap identity
`SandierSerfaty.Torus.pairSum_update_sub`). We prove: for every `p ≠ k`, the lattice distance
`dist(a k - a p, Γ)` is at least `r_* = 1/√π`.

The paper argues with the strict minimum principle on each connected component of the union `Ω` of the
disks `B(a p + γ, r_*)`. We argue instead with the global minimum of the *screened potential*
`Ψ(x) = Σ_{p ≠ k} K(x - a p)`, `K = G - Σ_γ φ(· - γ)` (`SandierSerfaty.Torus.screenedGreen`), which exists
since `Ψ` is continuous and `Γ`-periodic:

* if the minimum point `x₀` of `Ψ` is outside `Ω`, then `Ψ(x₀) = Φ(x₀) ≥ Φ(a k) > Ψ(a k)` when `a k ∈ Ω`,
  contradicting minimality of `x₀`;
* if `x₀ ∈ Ω`, a smooth comparison function `T ≥ Ψ` with `T(x₀) = Ψ(x₀)` has a local minimum at `x₀`
  and `Δ T (x₀) ≤ -2π/n < 0`, contradicting `SandierSerfaty.Analysis.laplacian_nonneg_of_isLocalMin`.

No connected components, no area bound `|Ω| < n`, and no Sobolev space are needed.
-/

open Filter Topology Metric Set Finset Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

section Swap

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem pairSum_split (c : Fin N → ℂ) (k : Fin N) :
    pairSum Γ c = ∑ j ∈ univ.erase k, torusGreen Γ (c k - c j) +
      ∑ i ∈ univ.erase k, (torusGreen Γ (c i - c k) +
        ∑ j ∈ (univ.erase i).erase k, torusGreen Γ (c i - c j)) := by
  unfold pairSum
  rw [← Finset.add_sum_erase univ _ (mem_univ k)]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≠ k := Finset.ne_of_mem_erase hi
  have hk : k ∈ univ.erase i := Finset.mem_erase.2 ⟨hik.symm, mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hk]

/-- **Swap identity**: moving the `k`-th point to `x` changes the pair sum by
`2 (Φ(x) - Φ(c k))`, `Φ(y) = Σ_{p ≠ k} G(y - c p)`. -/
theorem pairSum_update_sub (c : Fin N → ℂ) (k : Fin N) (x : ℂ) :
    pairSum Γ (Function.update c k x) - pairSum Γ c =
      2 * (∑ p ∈ univ.erase k, torusGreen Γ (x - c p) -
        ∑ p ∈ univ.erase k, torusGreen Γ (c k - c p)) := by
  rw [pairSum_split Γ (Function.update c k x) k, pairSum_split Γ c k]
  have h1 : ∀ j ∈ univ.erase k, Function.update c k x j = c j := fun j hj =>
    Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have e1 : ∑ j ∈ univ.erase k, torusGreen Γ (Function.update c k x k - Function.update c k x j) =
      ∑ j ∈ univ.erase k, torusGreen Γ (x - c j) :=
    Finset.sum_congr rfl fun j hj => by rw [h1 j hj]; simp
  have e2 : ∑ i ∈ univ.erase k, (torusGreen Γ (Function.update c k x i - Function.update c k x k) +
        ∑ j ∈ (univ.erase i).erase k, torusGreen Γ (Function.update c k x i - Function.update c k x j)) =
      ∑ i ∈ univ.erase k, (torusGreen Γ (c i - x) +
        ∑ j ∈ (univ.erase i).erase k, torusGreen Γ (c i - c j)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h1 i hi]
    simp only [Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [h1 j (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hj, mem_univ _⟩)]
  rw [e1, e2]
  have e3 : ∑ i ∈ univ.erase k, torusGreen Γ (c i - x) =
      ∑ i ∈ univ.erase k, torusGreen Γ (x - c i) :=
    Finset.sum_congr rfl fun i _ => by
      have := torusGreen_neg Γ (x - c i)
      rwa [neg_sub] at this
  have e4 : ∑ i ∈ univ.erase k, torusGreen Γ (c i - c k) =
      ∑ i ∈ univ.erase k, torusGreen Γ (c k - c i) :=
    Finset.sum_congr rfl fun i _ => by
      have := torusGreen_neg Γ (c k - c i)
      rwa [neg_sub] at this
  simp only [Finset.sum_add_distrib]
  linarith

end Swap

section Core

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
/-- A function on the plane that is continuous and `Γ`-periodic attains its minimum. -/
theorem exists_isMin_of_periodic (hn : 1 ≤ n) {f : ℂ → ℝ} (hf : Continuous f)
    (hper : ∀ γ ∈ squareLattice n, ∀ x, f (x - γ) = f x) : ∃ x₀, ∀ x, f x₀ ≤ f x := by
  have hne : (box n).Nonempty := ⟨0, by simp [box, Real.sqrt_nonneg]⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_box n).exists_isMinOn hne hf.continuousOn
  refine ⟨x₀, fun x => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := exists_sub_mem_box hn x
  rw [← hper γ hγ x]
  exact hmin hb

omit [NeZero n] in
/-- A short vector is either `0` or not in the lattice. -/
theorem eq_zero_or_notMem_of_norm_lt (hn : 2 ≤ n) {w : ℂ} (hw : ‖w‖ < rStar) :
    w = 0 ∨ w ∉ squareLattice n := by
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  · refine Or.inr fun hmem => ?_
    have := sqrt_le_norm_of_mem_squareLattice hmem hw0
    have := rStar_lt_sqrt_div_two hn
    have := rStar_pos
    linarith

theorem contDiffAt_comp_sub {f : ℂ → ℝ} {m : WithTop ℕ∞} {c x : ℂ} (h : ContDiffAt ℝ m f (x - c)) :
    ContDiffAt ℝ m (fun y => f (y - c)) x :=
  h.comp x (contDiffAt_id.sub contDiffAt_const)

/-- **The screening argument.** If `Φ(a k) ≤ Φ(x)` for all admissible `x`, then every other point `a p`
is at lattice distance `≥ r_*` from `a k`. -/
theorem rStar_le_infDist_of_isMin (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) (k : Fin n)
    (hΦ : ∀ x : ℂ, (∀ p ∈ univ.erase k, x - a p ∉ squareLattice n) →
      ∑ p ∈ univ.erase k, torusGreen (squareLattice n) (a k - a p) ≤
        ∑ p ∈ univ.erase k, torusGreen (squareLattice n) (x - a p)) :
    ∀ p ∈ univ.erase k, rStar ≤ infDist (a k - a p) (squareLattice n : Set ℂ) := by
  classical
  set Γ := squareLattice n with hΓ
  have hn1 : 1 ≤ n := by omega
  have hcov : ZLattice.covolume Γ = n := covolume_squareLattice n
  have hr := rStar_pos
  have hKc := continuous_screenedGreen n hn
  set Ψ : ℂ → ℝ := fun x => ∑ p ∈ univ.erase k, screenedGreen Γ (x - a p) with hΨ
  have hΨc : Continuous Ψ :=
    continuous_finsetSum _ fun p _ => hKc.comp (continuous_id.sub continuous_const)
  have hΨper : ∀ γ ∈ Γ, ∀ x, Ψ (x - γ) = Ψ x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun p _ => ?_
    have := screenedGreen_add_period Γ hγ (x - a p - γ)
    rw [sub_add_cancel] at this
    rw [show x - γ - a p = x - a p - γ by ring, ← this]
  obtain ⟨x₀, hx₀⟩ := exists_isMin_of_periodic n hn1 hΨc hΨper
  by_contra hcon
  push Not at hcon
  obtain ⟨p₁, hp₁k, hp₁⟩ := hcon
  by_cases hA : ∀ p ∈ univ.erase k, rStar ≤ infDist (x₀ - a p) (Γ : Set ℂ)
  · -- the minimum point is outside the screened disks
    have hx₀Γ : ∀ p ∈ univ.erase k, x₀ - a p ∉ Γ := fun p hp hmem => by
      have := hA p hp
      rw [infDist_zero_of_mem hmem] at this
      linarith
    have hΨx₀ : Ψ x₀ = ∑ p ∈ univ.erase k, torusGreen Γ (x₀ - a p) :=
      Finset.sum_congr rfl fun p hp => by
        rw [screenedGreen_of_notMem Γ (hx₀Γ p hp), screenFn_eq_zero Γ (hA p hp)]; ring
    have hdist : ∀ p ∈ univ.erase k, a k - a p ∉ Γ := fun p hp hmem =>
      Finset.ne_of_mem_erase hp (ha k p hmem).symm
    have hΨk : Ψ (a k) < ∑ p ∈ univ.erase k, torusGreen Γ (a k - a p) := by
      have : Ψ (a k) = ∑ p ∈ univ.erase k, (torusGreen Γ (a k - a p) - screenFn Γ (a k - a p)) :=
        Finset.sum_congr rfl fun p hp => screenedGreen_of_notMem Γ (hdist p hp)
      rw [this]
      refine Finset.sum_lt_sum (fun p hp => ?_) ⟨p₁, hp₁k, ?_⟩
      · linarith [screenFn_nonneg Γ (hdist p hp)]
      · linarith [screenFn_pos Γ (hdist p₁ hp₁k) hp₁]
    have h1 := hΦ x₀ hx₀Γ
    have h2 := hx₀ (a k)
    linarith
  · -- the minimum point is inside a screened disk: smooth comparison
    push Not at hA
    obtain ⟨p₂, hp₂k, hp₂⟩ := hA
    set P₀ : Finset (Fin n) := (univ.erase k).filter fun p => infDist (x₀ - a p) (Γ : Set ℂ) < rStar
      with hP₀
    have hP₀ne : P₀.Nonempty := ⟨p₂, Finset.mem_filter.2 ⟨hp₂k, hp₂⟩⟩
    have hP₀sub : P₀ ⊆ univ.erase k := Finset.filter_subset _ _
    have hγex : ∀ p, p ∈ P₀ → ∃ γ, γ ∈ Γ ∧ ‖x₀ - a p - γ‖ < rStar := fun p hp => by
      obtain ⟨γ, hγ, h⟩ := exists_norm_sub_lt_of_infDist_lt Γ (Finset.mem_filter.1 hp).2
      exact ⟨γ, hγ, h⟩
    choose! γ hγΓ hγlt using hγex
    have hnP₀ : ∀ p ∈ univ.erase k, p ∉ P₀ → rStar ≤ infDist (x₀ - a p) (Γ : Set ℂ) := fun p hp hnp => by
      by_contra h
      exact hnp (Finset.mem_filter.2 ⟨hp, not_le.1 h⟩)
    have hnP₀Γ : ∀ p ∈ univ.erase k, p ∉ P₀ → x₀ - a p ∉ Γ := fun p hp hnp hmem => by
      have := hnP₀ p hp hnp
      rw [infDist_zero_of_mem hmem] at this
      linarith
    set g : Fin n → ℂ → ℝ := fun p x =>
      if p ∈ P₀ then screenedLocal Γ (x - (a p + γ p)) else torusGreen Γ (x - a p) with hg
    set T : ℂ → ℝ := fun x => ∑ p ∈ univ.erase k, g p x with hT
    -- smoothness of each summand at `x₀`
    have hgs : ∀ p ∈ univ.erase k, ContDiffAt ℝ 2 (g p) x₀ := by
      intro p hp
      by_cases hpP : p ∈ P₀
      · have hlt' : ‖x₀ - (a p + γ p)‖ < rStar := by rw [← sub_sub]; exact hγlt p hpP
        have hsm := contDiffAt_screenedLocal Γ (eq_zero_or_notMem_of_norm_lt n hn hlt')
        have := contDiffAt_comp_sub (m := 2) (c := a p + γ p) (hsm.of_le (by norm_cast))
        simpa [hg, hpP] using this
      · have := (contDiffAt_torusGreen Γ (hnP₀Γ p hp hpP)).of_le (m := 2) (by norm_cast)
        have := contDiffAt_comp_sub (m := 2) (c := a p) this
        simpa [hg, hpP] using this
    have hTs : ContDiffAt ℝ 2 T x₀ := ContDiffAt.sum hgs
    -- the Laplacian of `T` at `x₀`
    have hgl : ∀ p ∈ univ.erase k,
        Δ (g p) x₀ = 2 * Real.pi / n - (if p ∈ P₀ then 2 * Real.pi else 0) := by
      intro p hp
      by_cases hpP : p ∈ P₀
      · have hlt' : ‖x₀ - (a p + γ p)‖ < rStar := by rw [← sub_sub]; exact hγlt p hpP
        have e : g p = fun x => screenedLocal Γ (x - (a p + γ p)) := by
          funext x; simp [hg, hpP]
        rw [e, Analysis.laplacian_comp_sub, laplacian_screenedLocal Γ
          (eq_zero_or_notMem_of_norm_lt n hn hlt'), hcov]
        simp [hpP]
      · have e : g p = fun x => torusGreen Γ (x - a p) := by
          funext x; simp [hg, hpP]
        rw [e, Analysis.laplacian_comp_sub, laplacian_torusGreen Γ (hnP₀Γ p hp hpP), hcov]
        simp [hpP]
    have hlap : Δ T x₀ = (n - 1 : ℝ) * (2 * Real.pi / n) - 2 * Real.pi * P₀.card := by
      have h1 : Δ T x₀ = ∑ p ∈ univ.erase k, Δ (g p) x₀ :=
        Analysis.laplacian_finset_sum _ _ _ hgs
      rw [h1, Finset.sum_congr rfl hgl, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.sum_ite_mem, Finset.inter_eq_right.2 hP₀sub, Finset.sum_const,
        Finset.card_erase_of_mem (mem_univ k)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hn1]
      simp
      ring
    -- `T` has a local minimum at `x₀`
    have hKle : ∀ᶠ x in 𝓝 x₀, ∀ p ∈ univ.erase k, screenedGreen Γ (x - a p) ≤ g p x := by
      rw [Filter.eventually_all_finset]
      intro p hp
      by_cases hpP : p ∈ P₀
      · have hc : ContinuousAt (fun x : ℂ => ‖x - a p - γ p‖) x₀ := by fun_prop
        have hev := hc.eventually_lt (continuousAt_const (y := rStar)) (hγlt p hpP)
        filter_upwards [hev] with x hx
        have := screenedGreen_eq_local n hn (hγΓ p hpP) (z := x - a p) hx
        simp only [hg, hpP, ite_true]
        rw [this, sub_sub]
      · have hopen : ∀ᶠ x in 𝓝 x₀, x - a p ∉ Γ :=
          ((isClosed_lattice Γ).isOpen_compl.preimage (continuous_id.sub continuous_const)).mem_nhds
            (hnP₀Γ p hp hpP)
        filter_upwards [hopen] with x hx
        simp only [hg, hpP, ite_false]
        rw [screenedGreen_of_notMem Γ hx]
        linarith [screenFn_nonneg Γ hx]
    have hΨT : Ψ x₀ = T x₀ := by
      refine Finset.sum_congr rfl fun p hp => ?_
      by_cases hpP : p ∈ P₀
      · have hlt' : ‖x₀ - a p - γ p‖ < rStar := hγlt p hpP
        have := screenedGreen_eq_local n hn (hγΓ p hpP) (z := x₀ - a p) hlt'
        simp only [hg, hpP, ite_true]
        rw [this, sub_sub]
      · simp only [hg, hpP, ite_false]
        rw [screenedGreen_of_notMem Γ (hnP₀Γ p hp hpP), screenFn_eq_zero Γ (hnP₀ p hp hpP)]
        ring
    have hmin : IsLocalMin T x₀ := by
      filter_upwards [hKle] with x hx
      calc T x₀ = Ψ x₀ := hΨT.symm
        _ ≤ Ψ x := hx₀ x
        _ ≤ T x := Finset.sum_le_sum hx
    have hnn := Analysis.laplacian_nonneg_of_isLocalMin hTs hmin
    rw [hlap] at hnn
    have hcard : (1 : ℝ) ≤ P₀.card := by exact_mod_cast hP₀ne.card_pos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpi := Real.pi_pos
    have : (n - 1 : ℝ) * (2 * Real.pi / n) - 2 * Real.pi * P₀.card ≤ -(2 * Real.pi / n) := by
      have e : (n - 1 : ℝ) * (2 * Real.pi / n) - 2 * Real.pi = -(2 * Real.pi / n) := by
        field_simp; ring
      nlinarith [e, mul_le_mul_of_nonneg_left hcard (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    have : 0 < 2 * Real.pi / n := by positivity
    linarith

end Core

end Torus

end SandierSerfaty

end
