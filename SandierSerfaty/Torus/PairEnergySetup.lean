/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.GreenRepr
public import SandierSerfaty.Torus.Periodize
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Set-up for the pair-energy identity

For a lattice `Γ` of covolume `N` and charges `a` with distinct classes, write `u = greenSum Γ a`
(equal to `torusPotential Γ a` off the charges). This file fixes a separation radius `ρ`
(`exists_sep`), bump functions `β i` equal to `1` on `B(a i, ρ)` and supported in `B(a i, 2ρ)`, and
the smooth periodic function `B = periodize Γ (∑ i, β i)`, which is `1` near every charge point
(`periodizedBump_eq_one`). The pair-energy identity splits the cell integral with `B`.
-/

open MeasureTheory Filter Topology Metric Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ}

/-- A uniform separation radius for the charge points. -/
theorem exists_sep (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ} (a : Fin N → ℂ) :
    ∃ ρ > 0, ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ρ ≤ ‖q - a i‖ := by
  have key : ∀ i : Fin N, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ε ≤ ‖q - a i‖ := by
    intro i
    have h := eventually_notMem_chargeSet Γ a (a i)
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhdsWithin_iff.1 h
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ / 4 :=
      (eventually_lt_nhds (by positivity : (0 : ℝ) < ε₀ / 4)).filter_mono nhdsWithin_le_nhds
    filter_upwards [this] with ε hε q hq hqne
    by_contra hcon
    have hcon := not_le.1 hcon
    have hmem : q ∈ ball (a i) ε₀ ∩ {a i}ᶜ := by
      refine ⟨?_, hqne⟩
      rw [mem_ball, dist_eq_norm]
      linarith
    exact hball hmem hq
  obtain ⟨ε, hε, hpos⟩ := ((eventually_all.2 key).and self_mem_nhdsWithin).exists
  exact ⟨ε, hpos, hε⟩

/-- The bump function at `c`: `1` on `closedBall c ρ`, supported in `ball c (2ρ)`. -/
@[expose] noncomputable def bumpFn (ρ : ℝ) (hρ : 0 < ρ) (c : ℂ) : ℂ → ℝ := fun x =>
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c) x

theorem contDiff_bumpFn {ρ : ℝ} (hρ : 0 < ρ) (c : ℂ) : ContDiff ℝ ∞ (bumpFn ρ hρ c) :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).contDiff

theorem bumpFn_eq_one {ρ : ℝ} (hρ : 0 < ρ) {c x : ℂ} (hx : ‖x - c‖ ≤ ρ) : bumpFn ρ hρ c x = 1 :=
  (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).one_of_mem_closedBall
    (by simpa [mem_closedBall, dist_eq_norm] using hx)

theorem bumpFn_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {c x : ℂ} (hx : 2 * ρ ≤ ‖x - c‖) :
    bumpFn ρ hρ c x = 0 := by
  have := (⟨ρ, 2 * ρ, hρ, by linarith⟩ : ContDiffBump c).zero_of_le_dist (x := x)
    (by simpa [dist_eq_norm] using hx)
  exact this

/-- The sum of the bumps at the charges. -/
@[expose] noncomputable def bumpSum (ρ : ℝ) (hρ : 0 < ρ) (a : Fin N → ℂ) (y : ℂ) : ℝ :=
  ∑ i, bumpFn ρ hρ (a i) y

theorem contDiff_bumpSum {ρ : ℝ} (hρ : 0 < ρ) (a : Fin N → ℂ) : ContDiff ℝ ∞ (bumpSum ρ hρ a) :=
  ContDiff.sum fun i _ => contDiff_bumpFn hρ (a i)

theorem bumpSum_eq_zero {ρ : ℝ} (hρ : 0 < ρ) (a : Fin N → ℂ)
    {y : ℂ} (hy : (∑ i, ‖a i‖) + 2 * ρ < ‖y‖) : bumpSum ρ hρ a y = 0 := by
  unfold bumpSum
  refine Finset.sum_eq_zero fun i _ => bumpFn_eq_zero hρ ?_
  have h1 : ‖a i‖ ≤ ∑ j, ‖a j‖ :=
    Finset.single_le_sum (f := fun j => ‖a j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : ‖y‖ - ‖a i‖ ≤ ‖y - a i‖ := by
    have := norm_sub_norm_le y (y - a i)
    simp only [sub_sub_cancel] at this
    linarith
  linarith

/-- The periodized bump: smooth, periodic, `= 1` near every charge point. -/
@[expose] noncomputable def periodizedBump (Γ : Submodule ℤ ℂ) {ρ : ℝ} (hρ : 0 < ρ) (a : Fin N → ℂ) : ℂ → ℝ :=
  periodize Γ (bumpSum ρ hρ a)

omit [IsZLattice ℝ Γ] in
theorem contDiff_periodizedBump {ρ : ℝ} (hρ : 0 < ρ) (a : Fin N → ℂ) :
    ContDiff ℝ ∞ (periodizedBump Γ hρ a) :=
  contDiff_periodize (c := 0) (ρ := (∑ i, ‖a i‖) + 2 * ρ) (contDiff_bumpSum hρ a)
    fun y hy => bumpSum_eq_zero hρ a (by simpa using hy)

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem periodizedBump_add_period {ρ : ℝ} (hρ : 0 < ρ) (a : Fin N → ℂ) {γ : ℂ} (hγ : γ ∈ Γ)
    (x : ℂ) : periodizedBump Γ hρ a (x + γ) = periodizedBump Γ hρ a x :=
  periodize_add_period _ hγ x

omit [IsZLattice ℝ Γ] in
theorem fderiv_periodizedBump {ρ : ℝ} (hρ : 0 < ρ) (a : Fin N → ℂ) (x v : ℂ) :
    fderiv ℝ (periodizedBump Γ hρ a) x v =
      ∑' γ : Γ, fderiv ℝ (bumpSum ρ hρ a) ((γ : ℂ) + x) v :=
  fderiv_periodize (c := 0) (ρ := (∑ i, ‖a i‖) + 2 * ρ) (contDiff_bumpSum hρ a)
    (fun y hy => bumpSum_eq_zero hρ a (by simpa using hy)) x v

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
/-- The periodized bump is `1` on the ball of radius `ρ` around every charge point. -/
theorem periodizedBump_eq_one {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ρ ≤ ‖q - a i‖)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) {q : ℂ} (hq : q ∈ chargeSet Γ a) {x : ℂ}
    (hx : ‖x - q‖ < ρ) : periodizedBump Γ hρ a x = 1 := by
  classical
  obtain ⟨j, hj⟩ := hq
  set δ₀ : Γ := ⟨q - a j, hj⟩ with hδ₀
  -- the unique contributing translate is `-δ₀`
  have hvan : ∀ (γ : Γ) (i : Fin N), (γ ≠ -δ₀ ∨ i ≠ j) → bumpFn ρ hρ (a i) ((γ : ℂ) + x) = 0 := by
    intro γ i hne
    refine bumpFn_eq_zero hρ ?_
    by_contra hlt
    rw [not_le] at hlt
    -- the point `γ + q` is a charge point within `3ρ` of `a i`
    have hP : (γ : ℂ) + q ∈ chargeSet Γ a := by
      refine ⟨j, ?_⟩
      have : (γ : ℂ) + q - a j = (γ : ℂ) + (q - a j) := by ring
      rw [this]
      exact Γ.add_mem γ.2 hj
    have hclose : ‖(γ : ℂ) + q - a i‖ < 4 * ρ := by
      have : (γ : ℂ) + q - a i = ((γ : ℂ) + x - a i) + (q - x) := by ring
      rw [this]
      calc ‖((γ : ℂ) + x - a i) + (q - x)‖ ≤ ‖(γ : ℂ) + x - a i‖ + ‖q - x‖ := norm_add_le _ _
        _ < 2 * ρ + ρ := by
          rw [norm_sub_rev q x]; exact add_lt_add hlt hx
        _ ≤ 4 * ρ := by linarith
    have heq : (γ : ℂ) + q = a i := by
      by_contra hne'
      have := hsep i _ hP hne'
      linarith
    -- so `a i - a j = γ + (q - a j) ∈ Γ`, hence `i = j` and `γ = -δ₀`
    have hmem : a i - a j ∈ Γ := by
      have : a i - a j = (γ : ℂ) + (q - a j) := by rw [← heq]; ring
      rw [this]; exact Γ.add_mem γ.2 hj
    have hij : i = j := ha i j hmem
    subst hij
    have hγ : (γ : ℂ) + (q - a i) = 0 := by rw [← heq]; ring
    apply hne.elim
    · intro h; apply h
      apply Subtype.ext
      simp only [hδ₀, Submodule.coe_neg]
      linear_combination hγ
    · intro h; exact h rfl
  unfold periodizedBump periodize
  rw [tsum_eq_single (-δ₀)]
  · unfold bumpSum
    rw [Finset.sum_eq_single j]
    · exact bumpFn_eq_one hρ (by
        have : ((-δ₀ : Γ) : ℂ) + x - a j = x - q := by
          simp only [hδ₀, Submodule.coe_neg]; ring
        rw [this]; exact hx.le)
    · intro i _ hij; exact hvan _ i (Or.inr hij)
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro γ hγ
    unfold bumpSum
    exact Finset.sum_eq_zero fun i _ => hvan γ i (Or.inl hγ)

end Torus

end SandierSerfaty

end
