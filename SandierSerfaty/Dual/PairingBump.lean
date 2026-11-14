/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.PairingCell
public import SandierSerfaty.Dual.Bump
public import SandierSerfaty.Torus.PairEnergySetup

/-!
# The periodized cut-off at scale `ε`

`Bsum ε a = ∑ᵢ cutBump ε (a i)` and `Bper Γ ε a = periodize Γ (Bsum ε a)`. For `ε` below a quarter of
the minimal distance between charges, `Bper` is `1` on the `ε`-balls about the charges, smooth,
periodic, and vanishes at distance `≥ 2ε` from the charges (`cutOff_Bper`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Torus

variable {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} {ε : ℝ}

/-- The sum of the cut-off bumps at the charges. -/
@[expose] noncomputable def Bsum (ε : ℝ) (a : Fin N → ℂ) (y : ℂ) : ℝ := ∑ i, cutBump ε (a i) y

/-- The periodized cut-off. -/
@[expose] noncomputable def Bper (Γ : Submodule ℤ ℂ) (ε : ℝ) (a : Fin N → ℂ) : ℂ → ℝ :=
  periodize Γ (Bsum ε a)

theorem contDiff_Bsum (hε : 0 < ε) : ContDiff ℝ ∞ (Bsum ε a) :=
  ContDiff.sum fun _i _ => contDiff_cutBump hε

theorem Bsum_eq_zero (hε : 0 < ε) {y : ℂ} (hy : (∑ i, ‖a i‖) + 2 * ε < ‖y - 0‖) :
    Bsum ε a y = 0 := by
  unfold Bsum
  refine Finset.sum_eq_zero fun i _ => cutBump_eq_zero hε ?_
  have h1 : ‖a i‖ ≤ ∑ j, ‖a j‖ :=
    Finset.single_le_sum (f := fun j => ‖a j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : ‖y‖ - ‖a i‖ ≤ ‖y - a i‖ := by
    have := norm_sub_norm_le y (y - a i)
    simp only [sub_sub_cancel] at this
    linarith
  rw [sub_zero] at hy
  linarith

theorem contDiff_Bper [DiscreteTopology Γ] (hε : 0 < ε) : ContDiff ℝ ∞ (Bper Γ ε a) :=
  contDiff_periodize (c := 0) (ρ := (∑ i, ‖a i‖) + 2 * ε) (contDiff_Bsum hε)
    fun _y hy => Bsum_eq_zero hε hy

theorem Bper_add_period (_hε : 0 < ε) {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    Bper Γ ε a (x + γ) = Bper Γ ε a x :=
  periodize_add_period _ hγ x

/-- `Bper = 1` on the `ε`-balls about the charges. -/
theorem Bper_eq_one [DiscreteTopology Γ] (hε : 0 < ε)
    (hsep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ε ≤ ‖q - a i‖)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) {q : ℂ} (hq : q ∈ chargeSet Γ a) {x : ℂ}
    (hx : ‖x - q‖ < ε) : Bper Γ ε a x = 1 := by
  classical
  obtain ⟨j, hj⟩ := hq
  set δ₀ : Γ := ⟨q - a j, hj⟩ with hδ₀
  have hvan : ∀ (γ : Γ) (i : Fin N), (γ ≠ -δ₀ ∨ i ≠ j) → cutBump ε (a i) ((γ : ℂ) + x) = 0 := by
    intro γ i hne
    refine cutBump_eq_zero hε ?_
    by_contra hlt
    rw [not_le] at hlt
    have hP : (γ : ℂ) + q ∈ chargeSet Γ a := by
      refine ⟨j, ?_⟩
      have : (γ : ℂ) + q - a j = (γ : ℂ) + (q - a j) := by ring
      rw [this]
      exact Γ.add_mem γ.2 hj
    have hclose : ‖(γ : ℂ) + q - a i‖ < 4 * ε := by
      have : (γ : ℂ) + q - a i = ((γ : ℂ) + x - a i) + (q - x) := by ring
      rw [this]
      calc ‖((γ : ℂ) + x - a i) + (q - x)‖ ≤ ‖(γ : ℂ) + x - a i‖ + ‖q - x‖ := norm_add_le _ _
        _ < 2 * ε + ε := by
          rw [norm_sub_rev q x]; exact add_lt_add hlt hx
        _ ≤ 4 * ε := by linarith
    have heq : (γ : ℂ) + q = a i := by
      by_contra hne'
      have := hsep i _ hP hne'
      linarith
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
  unfold Bper periodize
  rw [tsum_eq_single (-δ₀)]
  · unfold Bsum
    rw [Finset.sum_eq_single j]
    · exact cutBump_eq_one hε (by
        have : ((-δ₀ : Γ) : ℂ) + x - a j = x - q := by
          simp only [hδ₀, Submodule.coe_neg]; ring
        rw [this]; exact hx.le)
    · intro i _ hij; exact hvan _ i (Or.inr hij)
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro γ hγ
    unfold Bsum
    exact Finset.sum_eq_zero fun i _ => hvan γ i (Or.inl hγ)

theorem cutOff_Bper [DiscreteTopology Γ] (hε : 0 < ε)
    (hsep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ε ≤ ‖q - a i‖)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) : CutOff Γ a (Bper Γ ε a) :=
  { contDiff := (contDiff_Bper hε).of_le (by norm_cast)
    periodic := fun _ hγ x => Bper_add_period hε hγ x
    eq_one := fun q hq => by
      filter_upwards [ball_mem_nhds q hε] with x hx
      exact Bper_eq_one hε hsep ha hq (by simpa [dist_eq_norm] using hx) }

end Dual

end SandierSerfaty

end
