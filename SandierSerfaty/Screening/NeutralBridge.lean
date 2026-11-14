/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Density
public import SandierSerfaty.Statements.Jellium.Defs.JelliumEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy

/-!
# The bridge `W_{C0} = W^neu`

For `C0 ≥ C0* = c₀(1)/(2π) = log 2 + π/32` and
`E ∈ elec C`, the book's `W_{C0}(E, 1)` (`jelliumEnergy`) equals `W^neu(E, 1)` (`neutralEnergy`) in
`EReal`:

* **density → 1** (`jelliumEnergy_eq_limsup_of_tendsto`, any `C0`): for `R > 0`,
  `R⁻²(F + C0(n - R²)) = R⁻² F + C0(n/R² - 1)` (left distributivity of a finite nonnegative real in
  `EReal`), the real sequence `C0(n/R² - 1)` tends to `0`, and
  `limsup u + liminf v ≤ limsup (u + v) ≤ limsup u + limsup v` (`EReal.le_limsup_add`,
  `EReal.limsup_add_le`, whose side conditions hold because `limsup v = liminf v = 0`), whatever
  `limsup u ∈ [⊥, ⊤]` is;
* **density does not tend to `1`** (`W^neu = ⊤`): if `W_{C0} < ⊤`, pick a real `M > W_{C0}`;
  eventually `R⁻²(F + C0(n - R²)) < M`, which forces `F^{□_R} ≠ ⊤` (and `F ≠ ⊥` always,
  `cubeEnergy_ne_bot`); the energy bound `½∫_{□_R}|E_{1/4}|² ≤ 2πF + c₀ n` then gives
  `∫_{□_R}|E_{1/4}|² ≤ 4π(M + C0) R²`
  (`exists_lintegral_quarter_le_of_jelliumEnergy_ne_top`), and I3 gives density → 1, a contradiction. So `W_{C0} = ⊤`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

theorem cubeEnergy_ne_bot (C : Set ℂ) (E : ℂ → ℂ) (ℓ : ℝ) : cubeEnergy C E ℓ ≠ ⊥ := by
  unfold cubeEnergy
  exact EReal.add_ne_bot_iff.2 ⟨ne_bot_of_le_ne_bot EReal.zero_ne_bot
    (EReal.mul_nonneg (EReal.coe_nonneg.2 (by positivity)) (EReal.coe_ennreal_nonneg _)),
    EReal.coe_ne_bot _⟩

/-- When the density tends to `1`, the `C0` term of `W_{C0}` vanishes in the limit. -/
theorem jelliumEnergy_eq_limsup_of_tendsto (C0 : ℝ) {C : Set ℂ} (E : ℂ → ℂ)
    (hd : Tendsto (fun ℓ : ℝ ↦ ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1)) :
    jelliumEnergy C0 C E =
      limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ) atTop := by
  set u := fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ
  set v := fun ℓ : ℝ ↦ ((C0 * (((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2 - 1) : ℝ) : EReal)
  have hv : Tendsto v atTop (𝓝 0) := by
    have h : Tendsto (fun ℓ : ℝ ↦ C0 * (((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2 - 1)) atTop (𝓝 0) := by
      simpa using (hd.sub_const 1).const_mul C0
    have := EReal.tendsto_coe.2 h
    rwa [EReal.coe_zero] at this
  have heq : (fun R : ℝ ↦ (((R ^ 2)⁻¹ : ℝ) : EReal) *
      (cubeEnergy C E R + ((C0 * (((C ∩ cube R).ncard : ℝ) - R ^ 2) : ℝ) : EReal))) =ᶠ[atTop]
        u + v := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    simp only [Pi.add_apply, u, v]
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 (by positivity))
      (EReal.coe_ne_top _), ← EReal.coe_mul]
    congr 2
    field_simp
  unfold jelliumEnergy
  rw [limsup_congr heq]
  apply le_antisymm
  · calc limsup (u + v) atTop ≤ limsup u atTop + limsup v atTop :=
          EReal.limsup_add_le (Or.inr (by rw [hv.limsup_eq]; exact EReal.zero_ne_top))
            (Or.inr (by rw [hv.limsup_eq]; exact EReal.zero_ne_bot))
      _ = limsup u atTop := by rw [hv.limsup_eq, add_zero]
  · calc limsup u atTop = limsup u atTop + liminf v atTop := by rw [hv.liminf_eq, add_zero]
      _ ≤ limsup (u + v) atTop := EReal.le_limsup_add

/-- A finite `W_{C0}` with `C0 ≥ c₀/2π` bounds `∫_{□_ℓ} |E_{1/4}|²` by `O(ℓ²)`. -/
theorem exists_lintegral_quarter_le_of_jelliumEnergy_ne_top {C0 : ℝ}
    (hC0 : cQuarter 1 / (2 * π) ≤ C0) {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C)
    (hJ : jelliumEnergy C0 C E ≠ ⊤) :
    ∃ M ℓ₀ : ℝ, ∀ ℓ ≥ ℓ₀, ∫⁻ x in cube ℓ, ENNReal.ofReal
      (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal (M * ℓ ^ 2) := by
  obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 hJ)
  have hev := (eventually_lt_of_limsup_lt hM).and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hev
  have hc : cQuarter 1 ≤ 2 * π * C0 := by
    rwa [div_le_iff₀ Real.two_pi_pos, mul_comm] at hC0
  refine ⟨4 * π * (M + C0), R₀, fun R hR => ?_⟩
  obtain ⟨hlt, hR0⟩ := hR₀ R hR
  have hS1 := half_lintegral_quarter_le hE hR0
  set F := cubeEnergy C E R
  set n : ℝ := ((C ∩ cube R).ncard : ℝ)
  set I := ∫⁻ x in cube R, ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)
  have hFtop : F ≠ ⊤ := by
    intro h
    rw [h, EReal.top_add_coe, EReal.coe_mul_top_of_pos (by positivity)] at hlt
    exact not_top_lt hlt
  obtain ⟨f, hf⟩ : ∃ f : ℝ, F = f :=
    ⟨F.toReal, (EReal.coe_toReal hFtop (cubeEnergy_ne_bot C E R)).symm⟩
  have hItop : I ≠ ⊤ := by
    intro h
    rw [h, hf, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num), ← EReal.coe_mul,
      ← EReal.coe_add] at hS1
    exact EReal.coe_ne_top _ (top_le_iff.1 hS1)
  have hfR : (R ^ 2)⁻¹ * (f + C0 * (n - R ^ 2)) < M := by
    rw [hf, ← EReal.coe_add, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hlt
    exact hlt
  have hIR : 1 / 2 * I.toReal ≤ 2 * π * f + cQuarter 1 * n := by
    rw [hf, ← EReal.coe_ennreal_toReal hItop, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hS1
    exact hS1
  have hfR' : f + C0 * (n - R ^ 2) < M * R ^ 2 := by
    rw [inv_mul_lt_iff₀ (by positivity)] at hfR
    linarith
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  have hfin : I.toReal ≤ 4 * π * (M + C0) * R ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc) hn, Real.pi_pos]
  exact (ENNReal.le_ofReal_iff_toReal_le hItop (by linarith)).2 hfin

end Screening

open Screening in
/-- **The bridge** (Serfaty's Chapter 11, `exists_jelliumEnergy_eq_neutralEnergy`) with the explicit constant `C0* = c₀(1)/(2π) = log 2 + π/32`: for every `C0 ≥ C0*` and
`E ∈ elec C`, `W_{C0}(E, 1) = W^neu(E, 1)` in `EReal`. -/
theorem jelliumEnergy_eq_neutralEnergy {C0 : ℝ} (hC0 : cQuarter 1 / (2 * Real.pi) ≤ C0)
    {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) : jelliumEnergy C0 C E = neutralEnergy C E := by
  unfold neutralEnergy
  split_ifs with hd
  · exact jelliumEnergy_eq_limsup_of_tendsto C0 E hd
  · by_contra hJ
    exact hd (tendsto_ncard_cube_div_sq hE
      (exists_lintegral_quarter_le_of_jelliumEnergy_ne_top hC0 hE hJ))

end SandierSerfaty

end
