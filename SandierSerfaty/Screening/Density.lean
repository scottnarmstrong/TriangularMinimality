/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.CubeCutoff

/-!
# Density of the charges from an `L²` bound on the quarter truncation (I3)

Interface I3 (comparison note, §5 `prop:density`, restated
for the book's sign `-div E = 2π(∑ δ_p - 1)`). With `Φ = E_{1/4}` and the cutoff `φ = φ_{a,w}`, the
pairing I1 (`integral_inner_truncField_lipschitz`, `α ≡ ¼`) reads
`∫ ⟪Φ, ∇φ⟫ = 2π (∑_{p∈C} ⨍_{∂B(p,¼)} φ - ∫ φ)`. The circle averages are sandwiched between the
counts in `□_{2(a-¼)}` and `□_{2(a+w+¼)}` (`φ` is `[0,1]`-valued), so no local count is needed (this
replaces the comparison note's `lem:localcount` and Step 1 of `prop:density`). With `w = √ℓ`, `ε = ℓ^{-1/2}` both
errors are `O(ℓ^{3/2})` when `∫_{□_ℓ} |Φ|² ≤ M ℓ²`:

* `ncard_cube_le`, `le_ncard_cube`: the two-sided count for one cutoff;
* `tendsto_ncard_cube_div_sq`: **I3**, `#(C ∩ □_ℓ)/ℓ² → 1`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

variable {a w : ℝ}

/-! ### The two-sided count -/

theorem integral_inner_truncField_cubeCutoff {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C)
    (hw : 0 < w) :
    ∫ x, inner ℝ (truncField C (fun _ ↦ 1 / 4) E x) (gradient (cubeCutoff a w) x) =
      2 * π * ((∑ᶠ p ∈ C, Real.circleAverage (cubeCutoff a w) p (1 / 4)) -
        ∫ x, cubeCutoff a w x) := by
  have := integral_inner_truncField_lipschitz isOpen_univ hE.1 (isChargeField_of_mem_elec hE univ)
    (α := fun _ => 1 / 4) (fun _ _ => by norm_num) ⟨1 / 4, fun _ _ => le_rfl⟩
    (lipschitzWith_cubeCutoff (a := a) hw) (hasCompactSupport_cubeCutoff (a := a) hw)
    (subset_univ _)
  rwa [one_mul] at this

/-- The flux identity and the energy bound pin the circle-average count to `∫ φ_{a,w}`. -/
theorem abs_finsum_circleAverage_sub_integral_le {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C)
    {ε L : ℝ} (ha : 0 ≤ a + w) (hw : 0 < w) (hε : 0 < ε) (hL : 0 ≤ L)
    (hΦ : ∫⁻ x in cube (2 * (a + w)),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal L) :
    |(∑ᶠ p ∈ C, Real.circleAverage (cubeCutoff a w) p (1 / 4)) - ∫ x, cubeCutoff a w x| ≤
      (ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2)) / (2 * π) := by
  have h := abs_integral_inner_gradient_cubeCutoff_le ha hw hε hL hΦ
  rw [integral_inner_truncField_cubeCutoff hE hw, abs_mul, abs_of_pos Real.two_pi_pos] at h
  rw [le_div_iff₀ Real.two_pi_pos]
  linarith

theorem ncard_cube_le {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) {ε L : ℝ} (ha : 0 ≤ a)
    (hw : 0 < w) (hε : 0 < ε) (hL : 0 ≤ L)
    (hΦ : ∫⁻ x in cube (2 * (a + w)),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal L) :
    ((C ∩ cube (2 * (a - 1 / 4))).ncard : ℝ) ≤
      (2 * (a + w)) ^ 2 + (ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2)) / (2 * π) := by
  have h1 := ncard_le_finsum_circleAverage_cubeCutoff (a := a) hE.1 hw
  have h2 := abs_finsum_circleAverage_sub_integral_le hE (by linarith) hw hε hL hΦ
  have h3 := integral_cubeCutoff_le (a := a) (by linarith) hw
  linarith [(abs_le.1 h2).2]

theorem le_ncard_cube {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) {ε L : ℝ} (ha : 0 ≤ a)
    (hw : 0 < w) (hε : 0 < ε) (hL : 0 ≤ L)
    (hΦ : ∫⁻ x in cube (2 * (a + w)),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal L) :
    (2 * a) ^ 2 - (ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2)) / (2 * π) ≤
      ((C ∩ cube (2 * (a + w + 1 / 4))).ncard : ℝ) := by
  have h1 := finsum_circleAverage_cubeCutoff_le (a := a) hE.1 hw
  have h2 := abs_finsum_circleAverage_sub_integral_le hE (by linarith) hw hε hL hΦ
  have h3 := le_integral_cubeCutoff ha hw
  linarith [(abs_le.1 h2).1]

theorem three_le_sqrt {ℓ : ℝ} (h : 9 ≤ ℓ) : 3 ≤ √ℓ := by
  rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt h

end Screening

open Screening in
/-- **I3: density from an `L²` bound on the quarter truncation** (comparison note, `prop:density`, book sign):
if `∫_{□_ℓ} |E_{1/4}|² ≤ M ℓ²` for all large `ℓ`, then `#(C ∩ □_ℓ)/ℓ² → 1`. -/
theorem tendsto_ncard_cube_div_sq {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C)
    (hS : ∃ M ℓ₀ : ℝ, ∀ ℓ ≥ ℓ₀, ∫⁻ x in cube ℓ, ENNReal.ofReal
        (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal (M * ℓ ^ 2)) :
    Tendsto (fun ℓ : ℝ ↦ ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) := by
  obtain ⟨M₀, ℓ₀, hM₀⟩ := hS
  set M := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ ℓ ≥ ℓ₀, ∫⁻ x in cube ℓ, ENNReal.ofReal
      (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal (M * ℓ ^ 2) := fun ℓ hℓ =>
    (hM₀ ℓ hℓ).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  -- the comparison functions, in the variable `t = ℓ^{-1/2}`
  set Pu : ℝ → ℝ := fun t => (1 + 2 * t + t ^ 2 / 2) ^ 2 * (1 + (M + 1) * t / (2 * π))
  set Pl : ℝ → ℝ := fun t =>
    (1 - 2 * t - t ^ 2 / 2) ^ 2 - (M + 1) * (1 - t ^ 2 / 2) ^ 2 * t / (2 * π)
  have ht : Tendsto (fun ℓ : ℝ => (√ℓ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hPu : Tendsto (fun ℓ : ℝ => Pu (√ℓ)⁻¹) atTop (𝓝 1) := by
    have h := ((show Continuous Pu by fun_prop).tendsto 0).comp ht
    rwa [show Pu 0 = 1 by simp [Pu]] at h
  have hPl : Tendsto (fun ℓ : ℝ => Pl (√ℓ)⁻¹) atTop (𝓝 1) := by
    have h := ((show Continuous Pl by fun_prop).tendsto 0).comp ht
    rwa [show Pl 0 = 1 by simp [Pl]] at h
  have hev : ∀ᶠ ℓ : ℝ in atTop, 9 ≤ ℓ ∧ ℓ₀ + 1 ≤ ℓ :=
    (eventually_ge_atTop 9).and (eventually_ge_atTop (ℓ₀ + 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hPl hPu ?_ ?_
  · filter_upwards [hev] with ℓ hℓ
    obtain ⟨h9, hℓ₀⟩ := hℓ
    set s := √ℓ with hsdef
    have hs3 : 3 ≤ s := three_le_sqrt h9
    have hℓs : ℓ = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
    have hs0 : 0 < s := by linarith
    have ha : 0 ≤ s ^ 2 / 2 - s - 1 / 4 := by nlinarith
    have key := le_ncard_cube hE (a := s ^ 2 / 2 - s - 1 / 4) (w := s) (ε := s⁻¹)
      (L := M * (2 * (s ^ 2 / 2 - s - 1 / 4 + s)) ^ 2) ha hs0 (by positivity) (by positivity)
      (hM _ (by linarith))
    rw [show 2 * (s ^ 2 / 2 - s - 1 / 4 + s + 1 / 4) = ℓ by rw [hℓs]; ring] at key
    rw [le_div_iff₀ (by positivity)]
    refine le_trans (le_of_eq ?_) key
    simp only [Pl]
    rw [hℓs]
    field_simp
    ring
  · filter_upwards [hev] with ℓ hℓ
    obtain ⟨h9, hℓ₀⟩ := hℓ
    set s := √ℓ with hsdef
    have hs3 : 3 ≤ s := three_le_sqrt h9
    have hℓs : ℓ = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
    have hs0 : 0 < s := by linarith
    have key := ncard_cube_le hE (a := s ^ 2 / 2 + 1 / 4) (w := s) (ε := s⁻¹)
      (L := M * (2 * (s ^ 2 / 2 + 1 / 4 + s)) ^ 2) (by positivity) hs0 (by positivity)
      (by positivity) (hM _ (by linarith))
    rw [show 2 * (s ^ 2 / 2 + 1 / 4 - 1 / 4) = ℓ by rw [hℓs]; ring] at key
    rw [div_le_iff₀ (by positivity)]
    refine key.trans (le_of_eq ?_)
    simp only [Pu]
    rw [hℓs]
    field_simp
    ring

end SandierSerfaty

end
