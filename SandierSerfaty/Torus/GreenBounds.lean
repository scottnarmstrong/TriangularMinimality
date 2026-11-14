/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.Green
public import SandierSerfaty.Torus.SquareLatticeGeometry

/-!
# Bounds for the Green function of the square torus

Paper proof of Lemma `geo:existence`: "the function `G_n` is bounded
below on its punctured torus and tends to `+∞` at the origin."

* `SandierSerfaty.Torus.tendsto_torusGreen_nhdsNE_atTop`: `G_Γ → +∞` at `0`, for every lattice `Γ`;
* `SandierSerfaty.Torus.exists_lt_torusGreen`: quantitative form, also at every lattice point;
* `SandierSerfaty.Torus.exists_forall_le_torusGreen`: for `Γ = √n ℤ[i]`, `G_Γ` is bounded below on `ℂ`.
-/

open Filter Topology Metric Set

public section

namespace SandierSerfaty

namespace Torus

section General

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- `G_Γ x → +∞` as `x → 0`. -/
theorem tendsto_torusGreen_nhdsNE_atTop : Tendsto (torusGreen Γ) (𝓝[≠] (0 : ℂ)) atTop := by
  have h1 := tendsto_torusGreen_add_log Γ
  have h2 : Tendsto (fun x : ℂ => -Real.log ‖x‖) (𝓝[≠] (0 : ℂ)) atTop := by
    have : Tendsto (fun x : ℂ => ‖x‖) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((continuous_norm (E := ℂ)).tendsto (0 : ℂ)).mono_left
          (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact norm_ne_zero_iff.2 hx
    exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp this)
  have := h2.atTop_add h1
  refine this.congr' ?_
  filter_upwards with x
  ring

/-- Near the origin `G_Γ` exceeds any given bound. -/
theorem exists_lt_torusGreen (M : ℝ) :
    ∃ δ > 0, ∀ x : ℂ, x ≠ 0 → ‖x‖ < δ → M < torusGreen Γ x := by
  have h := (tendsto_atTop.1 (tendsto_torusGreen_nhdsNE_atTop Γ) (M + 1))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hx⟩ := h
  exact ⟨δ, hδ, fun x hx0 hxδ => by
    have := hx (y := x) (by simpa [dist_zero_right] using hxδ) hx0
    linarith⟩

/-- Near every lattice point `γ`, `G_Γ` exceeds any given bound (off the lattice). -/
theorem exists_lt_torusGreen_of_norm_sub_lt (M : ℝ) :
    ∃ δ > 0, ∀ x γ : ℂ, γ ∈ Γ → x ∉ Γ → ‖x - γ‖ < δ → M < torusGreen Γ x := by
  obtain ⟨δ, hδ, h⟩ := exists_lt_torusGreen Γ M
  refine ⟨δ, hδ, fun x γ hγ hx hxδ => ?_⟩
  have hne : x - γ ≠ 0 := fun h0 => hx (by rw [sub_eq_zero.1 h0]; exact hγ)
  have := h (x - γ) hne hxδ
  rwa [show torusGreen Γ (x - γ) = torusGreen Γ x by
    have := torusGreen_add_period Γ hγ (x - γ)
    simpa using this.symm] at this

/-- Periodicity of `G_Γ` under subtraction of a lattice vector. -/
theorem torusGreen_sub_period {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    torusGreen Γ (x - γ) = torusGreen Γ x := by
  have := torusGreen_add_period Γ hγ (x - γ)
  simpa using this.symm

end General

section Square

variable (n : ℕ) [NeZero n]

/-- `G_n` is bounded below on `ℂ` (paper `geo:existence`). -/
theorem exists_forall_le_torusGreen :
    ∃ c : ℝ, ∀ x : ℂ, c ≤ torusGreen (squareLattice n) x := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  set Γ := squareLattice n with hΓ
  obtain ⟨δ, hδ, hδG⟩ := exists_lt_torusGreen Γ 0
  set S : Set ℂ := box n ∩ {x | δ ≤ infDist x (Γ : Set ℂ)} with hS
  have hSc : IsCompact S :=
    (isCompact_box n).inter_right
      (isClosed_le continuous_const (continuous_infDist_lattice Γ))
  have hSΓ : ∀ x ∈ S, x ∉ Γ := by
    intro x hx hxΓ
    have : infDist x (Γ : Set ℂ) = 0 := infDist_zero_of_mem hxΓ
    have := hx.2
    simp only [mem_ofPred_eq] at this
    linarith [‹infDist x (Γ : Set ℂ) = 0›]
  have hcont : ContinuousOn (torusGreen Γ) S := fun x hx =>
    (contDiffAt_torusGreen Γ (hSΓ x hx)).continuousAt.continuousWithinAt
  obtain ⟨c1, hc1⟩ := (hSc.bddBelow_image hcont)
  refine ⟨min c1 0, fun x => ?_⟩
  obtain ⟨γ, hγ, hxb⟩ := exists_sub_mem_box hn x
  have hperiod : torusGreen Γ x = torusGreen Γ (x - γ) := (torusGreen_sub_period Γ hγ x).symm
  rw [hperiod]
  set y := x - γ
  by_cases hy : δ ≤ infDist y (Γ : Set ℂ)
  · have : y ∈ S := ⟨hxb, hy⟩
    exact (min_le_left _ _).trans (hc1 ⟨y, this, rfl⟩)
  · push Not at hy
    obtain ⟨γ', hγ', hlt⟩ := exists_norm_sub_lt_of_infDist_lt Γ hy
    rw [← torusGreen_sub_period Γ hγ' y]
    by_cases h0 : y - γ' = 0
    · rw [h0]
      have : torusGreen Γ 0 = 0 := torusGreen_of_mem Γ Γ.zero_mem
      rw [this]; exact min_le_right _ _
    · exact (min_le_right _ _).trans (hδG _ h0 hlt).le

end Square

end Torus

end SandierSerfaty

end
