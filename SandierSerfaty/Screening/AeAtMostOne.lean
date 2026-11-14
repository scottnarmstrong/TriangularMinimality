/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Families of sets with null pairwise intersections

For a finite family of sets `S_i` with `|S_i ∩ S_j| = 0` (`i ≠ j`), almost every point lies in at most
one `S_i` (`ae_atMostOne`). At such a point, a sum of functions `F_i` vanishing off `S_i` reduces to
one term (`sum_eq_of_atMostOne`), and `|∑ V_i|² = ∑ |V_i|²` (`norm_sq_sum_of_atMostOne`). Used for the
column, flux-cell and filler-piece families of the screening construction (screening note, §4.6).
-/

open MeasureTheory Set Filter

public section

namespace SandierSerfaty.Screening

variable {ι : Type*}

/-- Almost every point lies in at most one set of a finite family with null pairwise
intersections. -/
theorem ae_atMostOne (s : Finset ι) (S : ι → Set ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → volume (S i ∩ S j) = 0) :
    ∀ᵐ x, ∀ i ∈ s, ∀ j ∈ s, x ∈ S i → x ∈ S j → i = j := by
  have hnull : volume (⋃ i ∈ s, ⋃ j ∈ s, ⋃ (_ : i ≠ j), S i ∩ S j) = 0 := by
    refine (measure_biUnion_null_iff s.countable_toSet).2 fun i hi => ?_
    refine (measure_biUnion_null_iff s.countable_toSet).2 fun j hj => ?_
    exact measure_iUnion_null fun hij => h i hi j hj hij
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx i hi j hj hxi hxj
  by_contra hij
  exact hx (mem_biUnion hi (mem_biUnion hj (mem_iUnion.2 ⟨hij, hxi, hxj⟩)))

variable {s : Finset ι} {S : ι → Set ℂ} {x : ℂ}

/-- At a point in at most one set, a sum of terms vanishing off their sets has one term. -/
theorem sum_eq_of_atMostOne {M : Type*} [AddCommMonoid M] {F : ι → M}
    (hx : ∀ i ∈ s, ∀ j ∈ s, x ∈ S i → x ∈ S j → i = j) (hF : ∀ i ∈ s, x ∉ S i → F i = 0)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hxi₀ : x ∈ S i₀) : ∑ i ∈ s, F i = F i₀ :=
  Finset.sum_eq_single_of_mem i₀ hi₀ fun j hj hne =>
    hF j hj fun hxj => hne (hx j hj i₀ hi₀ hxj hxi₀)

/-- A sum of terms vanishing off their sets vanishes at a point outside all of them. -/
theorem sum_eq_zero_of_notMem {M : Type*} [AddCommMonoid M] {F : ι → M}
    (hF : ∀ i ∈ s, x ∉ S i → F i = 0) (hx : ∀ i ∈ s, x ∉ S i) : ∑ i ∈ s, F i = 0 :=
  Finset.sum_eq_zero fun i hi => hF i hi (hx i hi)

/-- `|∑ V_i|² = ∑ |V_i|²` at a point lying in at most one of the supports. -/
theorem norm_sq_sum_of_atMostOne {V : ι → ℂ}
    (hx : ∀ i ∈ s, ∀ j ∈ s, x ∈ S i → x ∈ S j → i = j) (hV : ∀ i ∈ s, x ∉ S i → V i = 0) :
    ‖∑ i ∈ s, V i‖ ^ 2 = ∑ i ∈ s, ‖V i‖ ^ 2 := by
  by_cases hex : ∃ i ∈ s, x ∈ S i
  · obtain ⟨i₀, hi₀, hxi₀⟩ := hex
    rw [sum_eq_of_atMostOne hx hV hi₀ hxi₀,
      sum_eq_of_atMostOne (F := fun i => ‖V i‖ ^ 2) hx
        (fun i hi hxi => by rw [hV i hi hxi, norm_zero, sq, mul_zero]) hi₀ hxi₀]
  · push Not at hex
    rw [sum_eq_zero_of_notMem hV hex,
      sum_eq_zero_of_notMem (F := fun i => ‖V i‖ ^ 2)
        (fun i hi hxi => by rw [hV i hi hxi, norm_zero, sq, mul_zero]) hex, norm_zero, sq, mul_zero]

end SandierSerfaty.Screening

end
