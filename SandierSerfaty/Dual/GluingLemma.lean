/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.IdentityAux

/-!
# The gluing lemma (paper `dual:gluing`)

`gluing_lemma`: for admissible radial data `R` (`kᵢ ≥ 6`, `B, Dᵢ ∈ C¹`, `(dual:radial-origin)`–`(dual:radial-sum)`)
and separated sites `P` (`SepSites P d₀`), the glued function `H = gluedH R P` satisfies

1. `H` is locally Lipschitz off the sites (hence continuous there and `H¹_loc`; continuity is proved
   directly from the matching of traces, `cellH_eq_of_mem_two`);
2. `H` is invariant under every translation `γ` preserving `P` (a `Γ`-periodic site set gives a `Γ`-periodic `H`);
3. `H` is `C¹` on every open sector and the gradient statement is sectorwise (no matching of derivatives);
4. `H = -log r + O(r²)` near each site, uniformly in the site (`(dual:singularity)`, value);
5. `∇H = -e_r / r + O(r)` on every sector near its site, uniformly (`(dual:singularity)`, gradient; `e_r / r = (z - p) / r²`).

The zero constant term in (4) is a consequence of the first item of `(dual:radial-origin)`; its Lipschitz form
(`H + log r` is Lipschitz across a site with value `0`) is `SandierSerfaty.Dual.exists_lipschitzOnWith_H1`.
-/

open MeasureTheory Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

variable {ι : Type*} {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ}

/-- **The gluing lemma.** -/
theorem gluing_lemma (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) :
    (∀ x : ℂ, x ∉ P → ∃ K : NNReal, ∃ δ > 0, LipschitzOnWith K (gluedH R P) (ball x δ)) ∧
    (∀ γ : ℂ, (∀ q, q + γ ∈ P ↔ q ∈ P) → ∀ z, gluedH R P (z + γ) = gluedH R P z) ∧
    (∀ p q : ℂ, IsVoronoiNeighbor P p q → ∀ z ∈ voronoiSector P p q,
      DifferentiableAt ℝ (gluedH R P) z) ∧
    (∃ C ρ : ℝ, 0 < ρ ∧ ∀ p ∈ P, ∀ z ∈ voronoiCell P p, 0 < ‖z - p‖ → ‖z - p‖ < ρ →
      |gluedH R P z + Real.log ‖z - p‖| ≤ C * ‖z - p‖ ^ 2) ∧
    (∃ C ρ : ℝ, 0 < ρ ∧ ∀ p q : ℂ, IsVoronoiNeighbor P p q → ∀ z ∈ voronoiSector P p q,
      ‖z - p‖ < ρ →
      ‖fderiv ℝ (gluedH R P) z + innerSL ℝ ((1 / ‖z - p‖ ^ 2 : ℝ) • (z - p))‖ ≤ C * ‖z - p‖) := by
  obtain ⟨R₁, T₀, M, hR₁, hT, hdT, hM⟩ := exists_bnd hR hS
  obtain ⟨C, ρ, hρ, hCρ⟩ := hR.origin
  have hd := hS.pos
  set SM : ℝ := ∑' i, M i with hSM
  have hSM0 : 0 ≤ SM := tsum_nonneg fun i => hM.nonneg hd hdT.le i
  refine ⟨fun x hx => exists_lipschitzOnWith_ball hR hS hx,
    fun γ hγ z => gluedH_add hS hγ z,
    fun p q h z hz => differentiableAt_gluedH_of_mem_sector hR hS h hz, ?_, ?_⟩
  · refine ⟨C + SM / d₀ ^ 6, min ρ 1, lt_min hρ one_pos, fun p hp z hz hr0 hrρ => ?_⟩
    rw [gluedH_eq_cellH hS hp hz]
    exact abs_cellH_add_log_le hR hS hp hR₁ hT hM (fun r hr => (hCρ r hr).1) hz hr0
      (lt_of_lt_of_le hrρ (min_le_left _ _)) (lt_of_lt_of_le hrρ (min_le_right _ _)).le
  · set K2 : ℝ := (2 + 1 / d₀) * (max 1 (Real.toNNReal (1 / d₀)) : NNReal) with hK2
    have hK20 : 0 ≤ K2 := by positivity
    refine ⟨C + K2 * (SM / d₀ ^ 5), min ρ 1, lt_min hρ one_pos, fun p q h z hz hr => ?_⟩
    have hzp := ne_of_mem_voronoiSector h hz
    have hr0 : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hzp)
    have hrρ : ‖z - p‖ < ρ := lt_of_lt_of_le hr (min_le_left _ _)
    have hr1 : ‖z - p‖ ≤ 1 := (lt_of_lt_of_le hr (min_le_right _ _)).le
    rw [(eventuallyEq_gluedH_Hsec hS h hz).fderiv_eq]
    refine (norm_fderiv_Hsec_add_le hR hS h hR₁ hT hM hz).trans ?_
    have h1 := (hCρ ‖z - p‖ ⟨hr0, hrρ⟩).2
    have h2 : (‖z - p‖ / d₀) ^ 5 * SM ≤ ‖z - p‖ * (SM / d₀ ^ 5) := by
      have h4 : ‖z - p‖ ^ 5 ≤ ‖z - p‖ := pow_le_of_le_one hr0.le hr1 (by norm_num)
      rw [div_pow]
      calc ‖z - p‖ ^ 5 / d₀ ^ 5 * SM = ‖z - p‖ ^ 5 * (SM / d₀ ^ 5) := by ring
        _ ≤ ‖z - p‖ * (SM / d₀ ^ 5) := mul_le_mul_of_nonneg_right h4 (by positivity)
    calc _ ≤ C * ‖z - p‖ + K2 * (‖z - p‖ * (SM / d₀ ^ 5)) :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h2 hK20)
      _ = _ := by ring

end Dual

end SandierSerfaty

end
