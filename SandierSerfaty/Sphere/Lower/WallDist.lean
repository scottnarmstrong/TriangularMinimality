/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# One-dimensional grid bands (for the sphere note's Lemma 6.12)

`cellPos R x ∈ [0,R)` is the position of `x` in its cell of the grid `R ℤ`; `wallDist R x` the distance to the nearest
wall; `wallBand R a b = {x | a ≤ wallDist R x ≤ b}`. For a fixed `x`, the set of offsets `θ ∈ [0,R]` with
`x - θ ∈ wallBand R a b` has measure `≤ 2 (b - a)` (`volume_wallBand_shift_le`).
-/

open MeasureTheory Set
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- Position of `x` inside its period cell `[kR, (k+1)R)`: `x - R ⌊x/R⌋ ∈ [0,R)`. -/
@[expose] noncomputable def cellPos (R x : ℝ) : ℝ := x - R * ⌊x / R⌋

/-- Distance from `x` to the nearest cell wall of the grid `R ℤ`. -/
@[expose] noncomputable def wallDist (R x : ℝ) : ℝ := min (cellPos R x) (R - cellPos R x)

theorem cellPos_add_period {R : ℝ} (hR : 0 < R) (x : ℝ) : cellPos R (x + R) = cellPos R x := by
  unfold cellPos
  have : ⌊(x + R) / R⌋ = ⌊x / R⌋ + 1 := by
    rw [add_div, div_self hR.ne', Int.floor_add_one]
  rw [this]; push_cast; ring

theorem cellPos_of_mem_Ico {R x : ℝ} (hR : 0 < R) (hx : x ∈ Ico 0 R) : cellPos R x = x := by
  unfold cellPos
  have : ⌊x / R⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg hx.1 hR.le, (div_lt_one hR).2 hx.2⟩
  rw [this]; simp

theorem wallDist_periodic {R : ℝ} (hR : 0 < R) : Function.Periodic (wallDist R) R := by
  intro x
  unfold wallDist
  rw [cellPos_add_period hR]

theorem measurable_cellPos (R : ℝ) : Measurable (cellPos R) := by
  unfold cellPos
  have : Measurable fun x : ℝ => ⌊x / R⌋ := Int.measurable_floor.comp (by fun_prop)
  exact measurable_id.sub (measurable_const.mul (measurable_from_top.comp this))

theorem measurable_wallDist (R : ℝ) : Measurable (wallDist R) := by
  unfold wallDist
  exact (measurable_cellPos R).min (measurable_const.sub (measurable_cellPos R))

/-- One-dimensional band measure: `|{w ∈ [0,R) : a ≤ wallDist w ≤ b}| ≤ 2 (b - a)`. -/
theorem volume_wallDist_band_le {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b) :
    volume {w ∈ Ico (0 : ℝ) R | a ≤ wallDist R w ∧ wallDist R w ≤ b} ≤ ENNReal.ofReal (2 * (b - a)) := by
  have hsub : {w ∈ Ico (0 : ℝ) R | a ≤ wallDist R w ∧ wallDist R w ≤ b} ⊆
      Icc a b ∪ Icc (R - b) (R - a) := by
    rintro w ⟨hw, ha, hb⟩
    rw [wallDist, cellPos_of_mem_Ico hR hw] at ha hb
    rcases le_total w (R - w) with h | h
    · rw [min_eq_left h] at ha hb
      exact Or.inl ⟨ha, hb⟩
    · rw [min_eq_right h] at ha hb
      exact Or.inr ⟨by linarith, by linarith⟩
  calc _ ≤ volume (Icc a b ∪ Icc (R - b) (R - a)) := measure_mono hsub
    _ ≤ volume (Icc a b) + volume (Icc (R - b) (R - a)) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * (b - a)) := by
      rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring


/-- The band set `{w | a ≤ wallDist R w ≤ b}`. -/
@[expose] def wallBand (R a b : ℝ) : Set ℝ := {w | a ≤ wallDist R w ∧ wallDist R w ≤ b}

theorem measurableSet_wallBand (R a b : ℝ) : MeasurableSet (wallBand R a b) :=
  (measurableSet_le measurable_const (measurable_wallDist R)).inter
    (measurableSet_le (measurable_wallDist R) measurable_const)

theorem volume_wallBand_shift_le {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b) (x : ℝ) :
    volume {θ ∈ Icc (0 : ℝ) R | x - θ ∈ wallBand R a b} ≤ ENNReal.ofReal (2 * (b - a)) := by
  set B := wallBand R a b with hB
  have hBm : MeasurableSet B := measurableSet_wallBand R a b
  set φ : ℝ → ℝ := B.indicator 1 with hφ
  have hper : Function.Periodic φ R := by
    intro w
    simp only [hφ, Set.indicator, hB, wallBand, Set.mem_ofPred_eq, wallDist_periodic hR w, Pi.one_apply]
  have hint : ∫ θ in (0 : ℝ)..R, φ (x - θ) = ∫ w in (0 : ℝ)..R, φ w := by
    rw [intervalIntegral.integral_comp_sub_left φ x]
    have := hper.intervalIntegral_add_eq (x - R) 0
    simp only [sub_add_cancel, zero_add] at this
    simpa using this
  have hset : MeasurableSet {θ : ℝ | x - θ ∈ B} := hBm.preimage (by fun_prop)
  have hfin : ∀ S : Set ℝ, volume (S ∩ Icc (0 : ℝ) R) ≠ ⊤ := fun S =>
    ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)
  -- left side
  have hlhs : volume {θ ∈ Icc (0 : ℝ) R | x - θ ∈ B} =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..R, φ (x - θ)) := by
    rw [intervalIntegral.integral_of_le hR.le, ← integral_Icc_eq_integral_Ioc]
    have : (fun θ => φ (x - θ)) = {θ : ℝ | x - θ ∈ B}.indicator 1 := by
      ext θ; simp [hφ, Set.indicator]
    rw [this, integral_indicator_one hset, measureReal_restrict_apply hset,
      Measure.real, ENNReal.ofReal_toReal (hfin _)]
    congr 1
    ext θ; simp [and_comm]
  -- right side
  have hrhs : ENNReal.ofReal (∫ w in (0 : ℝ)..R, φ w) ≤ ENNReal.ofReal (2 * (b - a)) := by
    rw [intervalIntegral.integral_of_le hR.le]
    have hIoc : ∫ w in Ioc (0 : ℝ) R, φ w = volume.real (B ∩ Ioc 0 R) := by
      rw [show φ = B.indicator 1 from rfl, integral_indicator_one hBm,
        measureReal_restrict_apply hBm]
    rw [hIoc, Measure.real]
    have hfin' : volume (B ∩ Ioc 0 R) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)
    rw [ENNReal.ofReal_toReal hfin']
    have hsub : B ∩ Ioc 0 R ⊆ {w ∈ Ico (0 : ℝ) R | a ≤ wallDist R w ∧ wallDist R w ≤ b} ∪ {R} := by
      rintro w ⟨hw, h0, h1⟩
      rcases h1.eq_or_lt with rfl | hlt
      · exact Or.inr rfl
      · exact Or.inl ⟨⟨h0.le, hlt⟩, hw.1, hw.2⟩
    calc volume (B ∩ Ioc 0 R)
        ≤ volume ({w ∈ Ico (0 : ℝ) R | a ≤ wallDist R w ∧ wallDist R w ≤ b} ∪ {R}) :=
          measure_mono hsub
      _ ≤ volume {w ∈ Ico (0 : ℝ) R | a ≤ wallDist R w ∧ wallDist R w ≤ b} + volume ({R} : Set ℝ) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * (b - a)) := by
          rw [Real.volume_singleton, add_zero]
          exact volume_wallDist_band_le hR hab
  rw [hlhs, hint]
  exact hrhs


end Lower

end Sphere

end SandierSerfaty

end
