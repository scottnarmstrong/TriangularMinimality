/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TriangularReal
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential

/-!
# The puncture limit for the one-point torus

For a lattice `Γ` whose nonzero points have norm `≥ 1` and a torus potential `h` of the charge at `0`
with local part `v` (`IsLocalPart h v`), the puncture expression of `torusEnergy`

`ε ↦ ½ ∫_{T \ ⋃ B(γ, ε)} ‖∇h‖² + π log ε`

tends, as `ε ↓ 0`, to `½ A + ½ V + π log η - π² η²` with `η = ¼`, `A = ∫_F 1_{far η} ‖∇h‖²` and
`V = ∫_{B(0,η)} ‖∇v‖²` (`SandierSerfaty.Torus.tendsto_puncture`). In terms of the cell integral
`J = ∫_F ‖E_η‖² = V + A` this is `½ J + π log η - π² η²`.
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Torus

section Puncture

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem iUnion_ball_compl (Γ : Submodule ℤ ℂ) (ε : ℝ) :
    (⋃ i : Fin 1, ⋃ γ ∈ Γ, ball (zeroCharge i + γ) ε)ᶜ = farSet Γ ε := by
  ext x
  simp [farSet, zeroCharge, dist_eq_norm]

/-- The puncture integral over `T \ ⋃ B(γ, ε)` is the cell integral of `1_{far ε} ‖∇h‖²`. -/
theorem integral_torusDomain_far {h : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) {F : Set ℂ}
    (hF : IsAddFundamentalDomain Γ F volume) (ε : ℝ) :
    ∫ x in torusDomain Γ \ ⋃ i : Fin 1, ⋃ γ ∈ Γ, ball (zeroCharge i + γ) ε,
        ‖gradient h x‖ ^ 2 =
      (∫⁻ x in F, (farSet Γ ε).indicator (cellGradSq h) x).toReal := by
  have hmeasU : MeasurableSet (farSet Γ ε) := measurableSet_farSet Γ ε
  rw [Set.sdiff_eq, iUnion_ball_compl, ← setIntegral_indicator hmeasU]
  set f : ℂ → ℝ := (farSet Γ ε).indicator fun x => ‖gradient h x‖ ^ 2 with hf
  have hfper : ∀ γ ∈ Γ, ∀ x, f (x + γ) = f x := by
    intro γ hγ x
    simp only [hf]
    by_cases hx : x ∈ farSet Γ ε
    · rw [indicator_of_mem hx, indicator_of_mem ((farSet_add_periodic hγ).2 hx),
        gradient_add_periodic hper hγ]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h' => hx ((farSet_add_periodic hγ).1 h'))]
  rw [(torusDomain_spec Γ).2 F hF f hfper]
  have hnn : 0 ≤ᵐ[volume.restrict F] f := ae_of_all _ fun x => by
    simp only [hf]; exact indicator_nonneg (fun y _ => by positivity) x
  have hmeas : AEStronglyMeasurable f (volume.restrict F) :=
    (((measurable_gradient h).norm.pow_const 2).indicator hmeasU).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
  congr 1
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ farSet Γ ε
  · simp [hf, indicator_of_mem hx, cellGradSq]
  · simp [hf, indicator_of_notMem hx]

/-- **The puncture limit.** -/
theorem tendsto_puncture (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h v : ℂ → ℝ}
    (hP : IsTorusPotential Γ zeroCharge h) (hv : IsLocalPart h v) {F : Set ℂ}
    (hF : IsAddFundamentalDomain Γ F volume) (hFb : Bornology.IsBounded F)
    (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F) :
    Tendsto (fun ε : ℝ => (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i : Fin 1, ⋃ γ ∈ Γ,
        ball (zeroCharge i + γ) ε, ‖gradient h x‖ ^ 2) + Real.pi * ((1 : ℕ) : ℝ) * Real.log ε)
      (𝓝[>] 0)
      (𝓝 (1 / 2 * (∫⁻ x in F, (farSet Γ (1 / 4)).indicator (cellGradSq h) x).toReal +
        1 / 2 * Vint v (1 / 4) + Real.pi * Real.log (1 / 4) - Real.pi ^ 2 * (1 / 4) ^ 2)) := by
  set Aη : ℝ≥0∞ := ∫⁻ x in F, (farSet Γ (1 / 4)).indicator (cellGradSq h) x with hAη
  have hAη_fin : Aη ≠ ⊤ := lintegral_far_ne_top hP hFb hcov (by norm_num)
  obtain ⟨C, hC⟩ := exists_Vint_le hv.1
  set W : ℝ := 1 / 2 * Aη.toReal + 1 / 2 * Vint v (1 / 4) + Real.pi * Real.log (1 / 4) -
    Real.pi ^ 2 * (1 / 4) ^ 2 with hW
  have hrem : Tendsto (fun ε : ℝ => Real.pi ^ 2 * ε ^ 2 - 1 / 2 * Vint v ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => Real.pi ^ 2 * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => Real.pi ^ 2 * ε ^ 2) (𝓝 0) (𝓝 (Real.pi ^ 2 * 0 ^ 2)) :=
        (continuous_const.mul (continuous_id.pow 2)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ => Vint v ε) (𝓝[>] 0) (𝓝 0) := by
      have hCt : Tendsto (fun ε : ℝ => C * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => C * ε ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
          (continuous_const.mul (continuous_id.pow 2)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero' ?_ ?_ hCt
      · filter_upwards with ε using Vint_nonneg v ε
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with ε hε
        exact hC ε hε.1 hε.2.le
    simpa only [mul_zero, sub_zero] using h1.sub (h2.const_mul (1 / 2))
  have hlim := hrem.const_add W
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with ε hε
  have hε0 : 0 < ε := hε.1
  have hεη : ε < 1 / 4 := hε.2
  have hsplit := lintegral_far_split hmin hP.1 hF hε0 hεη.le
  rw [lintegral_gradSq_ann hv hε0 hεη] at hsplit
  set a : ℝ := Vint v (1 / 4) - Vint v ε - 2 * (Real.pi ^ 2 * ((1 / 4) ^ 2 - ε ^ 2)) +
    2 * Real.pi * Real.log ((1 / 4) / ε) with ha
  have ha0 : 0 ≤ a := by
    obtain ⟨hint, hval⟩ := integral_gradient_ann hv hε0 hεη
    rw [ha, ← hval]
    exact setIntegral_nonneg (measurableSet_ann ε) fun y _ => by positivity
  rw [integral_torusDomain_far hP.1 hF ε, hsplit, ENNReal.toReal_add hAη_fin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal ha0, ha, hW, Real.log_div (by norm_num) hε0.ne']
  simp only [Nat.cast_one, mul_one]
  ring

end Puncture

end Torus

end SandierSerfaty

end
