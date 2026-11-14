/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectEnergy

/-!
# The truncated energies of the reflected potential on a quadrant (Lemma 6.2(iii))

`Lower.tendsto_punctureTrunc_reflected`: for `Z : Fin n̄ → ℂ` injective with `Z i ∈ b + (0, √n̄)²`
and `h = torusPotential (squareLattice (4 n̄)) (reflectPts b Z)`, the truncated puncture energies of `h` on the
open square `b + (0, √n̄)²` with punctures `Z` converge to `torusEnergy / 4`. The proof compares the periodic
integral `∫_{D ∖ ⋃ B(a_i + γ, η)} |∇h|²` with four times the quadrant integral
(`integral_torusDomain_eq_four`); for `η` below the distance `δ` of the charges to the sides of the
quadrant, the only balls meeting the quadrant are the balls around `Z`.
-/

open MeasureTheory Filter Topology Set

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

open Torus

variable {nb : ℕ} (hnb : 1 ≤ nb) (b : ℂ) (Z : Fin nb → ℂ) (hZi : Function.Injective Z)
  (hZ : ∀ i, 0 < (Z i - b).re ∧ (Z i - b).re < √nb ∧ 0 < (Z i - b).im ∧ (Z i - b).im < √nb)

include hnb hZ in
theorem exists_delta : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ (Z i - b).re ∧ (Z i - b).re ≤ √nb - δ ∧
    δ ≤ (Z i - b).im ∧ (Z i - b).im ≤ √nb - δ := by
  have : Nonempty (Fin nb) := ⟨⟨0, by omega⟩⟩
  let f : Fin nb → ℝ := fun i =>
    min (min (Z i - b).re (√nb - (Z i - b).re)) (min (Z i - b).im (√nb - (Z i - b).im))
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
  refine ⟨f i₀, ?_, fun i => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hZ i₀
    simp only [f, lt_min_iff]
    refine ⟨⟨h1, by linarith⟩, h3, by linarith⟩
  · have := hi₀ i
    simp only [f, le_min_iff] at this
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
    refine ⟨h1, by linarith, h3, by linarith⟩

include hnb hZi hZ in
theorem tendsto_punctureTrunc_reflected :
    Tendsto (punctureTrunc (openSq b (√nb)) (Finset.univ.image Z)
        (torusPotential (squareLattice (4 * nb)) (reflectPts b Z)))
      (𝓝[>] 0) (𝓝 (torusEnergy (squareLattice (4 * nb)) (reflectPts b Z) / 4)) := by
  have : NeZero (4 * nb) := ⟨by omega⟩
  obtain ⟨δ, hδ, hZδ⟩ := exists_delta hnb b Z hZ
  have hdist := reflectPts_distinct hnb b Z hZi hZ
  have hT := tendsto_torusEnergy (squareLattice (4 * nb)) (covolume_squareLattice (4 * nb))
    (reflectPts b Z) (fun i j hij => hdist i j hij)
  refine (hT.div_const 4).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with η hη
  set Γ := squareLattice (4 * nb) with hΓ
  set a := reflectPts b Z with ha
  set h := torusPotential Γ a with hh
  obtain ⟨hP, -⟩ := torusPotential_spec Γ (covolume_squareLattice (4 * nb)) a
    (fun i j hij => hdist i j hij)
  have hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x := hP.1
  have hX := torusPotential_reflX hnb b Z hZi hZ
  have hY := torusPotential_reflY hnb b Z hZi hZ
  have hdens : ∀ x, energyDensity Γ a h η x = (ballUnion Γ a η)ᶜ.indicator
      (fun y => ‖gradient h y‖ ^ 2) x := fun x => rfl
  have e1 : ∫ x in torusDomain Γ \ ballUnion Γ a η, ‖gradient h x‖ ^ 2 =
      ∫ x in torusDomain Γ, energyDensity Γ a h η x := by
    simp only [hdens]
    rw [setIntegral_indicator (isOpen_ballUnion Γ a η).measurableSet.compl, Set.sdiff_eq]
  have e2 : ∫ x in openSq b (√nb) \ ballUnion Γ a η, ‖gradient h x‖ ^ 2 =
      ∫ x in openSq b (√nb), energyDensity Γ a h η x := by
    simp only [hdens]
    rw [setIntegral_indicator (isOpen_ballUnion Γ a η).measurableSet.compl, Set.sdiff_eq]
  have e3 : openSq b (√nb) \ ballUnion Γ a η =
      openSq b (√nb) \ ⋃ p ∈ Finset.univ.image Z, Metric.ball p η := by
    ext x
    simp only [Set.mem_sdiff, mem_iUnion, Metric.mem_ball, dist_eq_norm, Finset.mem_image,
      Finset.mem_univ, true_and, exists_prop, not_exists, not_and]
    constructor
    · rintro ⟨hx, hxn⟩
      refine ⟨hx, ?_⟩
      rintro p ⟨i, rfl⟩ hlt
      apply hxn
      rw [mem_ballUnion]
      refine ⟨finProdFinEquiv (0, i), 0, Γ.zero_mem, ?_⟩
      rw [ha, reflectPts_apply]
      simpa [reflect4_zero] using hlt
    · rintro ⟨hx, hxn⟩
      refine ⟨hx, fun hxb => ?_⟩
      obtain ⟨i, hi⟩ := exists_ball_of_mem_ballUnion hnb b Z hδ (le_of_lt hη.2) hZδ hx hxb
      exact hxn (Z i) ⟨i, rfl⟩ hi
  have e4 := integral_torusDomain_eq_four hnb b (F := energyDensity Γ a h η)
    (energyDensity_nonneg Γ a h η) (measurable_energyDensity Γ a h η)
    (fun γ hγ x => energyDensity_add_period hper η hγ x)
    (fun x => energyDensity_refl (reflXSymm b Z) hX η x)
    (fun x => energyDensity_refl (reflYSymm b Z) hY η x)
  unfold punctureTrunc
  have hcard : (Finset.univ.image Z).card = nb := by
    rw [Finset.card_image_of_injective _ hZi]; simp
  rw [hcard]
  change ((1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ballUnion Γ a η, ‖gradient h x‖ ^ 2) +
      Real.pi * ((4 * nb : ℕ) : ℝ) * Real.log η) / 4 = _
  rw [e1, e4, ← e2, e3]
  push_cast
  ring

end Lower

end Sphere

end SandierSerfaty

end
