/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.ChartIntegrable
public import SandierSerfaty.Sphere.CutoffFamily

/-!
# The exact Green identity for the chart potential on the plane (sphere note, Proposition 3.4, step 1)

For pairwise distinct `x₁, …, xₙ` and `0 < η ≤ ρ` (with `ρ` a separation radius),
```
∫_{Ω_η} (|∇h_X|² + h_X · 2π n µ) = - ∑ᵢ circleTerm h_X xᵢ η,    Ω_η = {x | ∀ i, η ≤ |x - xᵢ|}.
```
This is `Sphere.green_cutoff` for the cutoffs `χ_R = cutoffR R`, `R → ∞`: the integral of
`h_X ⟨∇χ_R, ∇h_X⟩` is `O(R⁻²)` by the decay estimates of `Sphere.ChartDecay`.
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem exists_separation (P : Finset ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 4 * ρ ≤ ‖p - q‖ := by
  classical
  by_cases h : (P.offDiag).Nonempty
  · obtain ⟨⟨p, q⟩, hpq, hmin⟩ := Finset.exists_min_image P.offDiag (fun z => ‖z.1 - z.2‖) h
    have hne : p ≠ q := (Finset.mem_offDiag.1 hpq).2.2
    have hpos : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    refine ⟨‖p - q‖ / 4, by positivity, fun a ha b hb hab => ?_⟩
    have := hmin (a, b) (Finset.mem_offDiag.2 ⟨ha, hb, hab⟩)
    simp only at this
    linarith
  · refine ⟨1, one_pos, fun a ha b hb hab => ?_⟩
    exact absurd ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩⟩ h

theorem abs_gradDot_le (φ u : ℂ → ℝ) (x : ℂ) :
    |gradDot φ u x| ≤ 2 * (‖fderiv ℝ φ x‖ * ‖fderiv ℝ u x‖) := by
  have hb : ∀ (f : ℂ → ℝ) (v : ℂ), ‖v‖ = 1 → |fderiv ℝ f x v| ≤ ‖fderiv ℝ f x‖ := by
    intro f v hv
    have := (fderiv ℝ f x).le_opNorm v
    simpa [hv] using this
  have h1 : |pd₁ φ x * pd₁ u x| ≤ ‖fderiv ℝ φ x‖ * ‖fderiv ℝ u x‖ := by
    rw [abs_mul]
    exact mul_le_mul (hb φ 1 (by simp)) (hb u 1 (by simp)) (abs_nonneg _) (norm_nonneg _)
  have h2 : |pd₂ φ x * pd₂ u x| ≤ ‖fderiv ℝ φ x‖ * ‖fderiv ℝ u x‖ := by
    rw [abs_mul]
    exact mul_le_mul (hb φ Complex.I (by simp)) (hb u Complex.I (by simp)) (abs_nonneg _)
      (norm_nonneg _)
  unfold gradDot
  calc |pd₁ φ x * pd₁ u x + pd₂ φ x * pd₂ u x| ≤ |pd₁ φ x * pd₁ u x| + |pd₂ φ x * pd₂ u x| :=
        abs_add_le _ _
    _ ≤ 2 * (‖fderiv ℝ φ x‖ * ‖fderiv ℝ u x‖) := by linarith

theorem measurable_chartPot {n : ℕ} (X : Fin n → ℂ) : Measurable (chartPot X) := by
  unfold chartPot gKer
  have h1 : ∀ i : Fin n, Measurable fun x : ℂ => -Real.log ‖x - X i‖ := fun i =>
    (Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub measurable_const))).neg
  exact (Finset.measurable_sum _ fun i _ => h1 i).add
    (measurable_const.mul contDiff_potV.continuous.measurable)

theorem continuous_dens : Continuous dens := by
  have h : dens = fun x : ℂ => densR ‖x‖ := funext dens_eq_densR
  rw [h]
  exact continuous_densR.comp continuous_norm

theorem volume_closedBall_toReal (R : ℝ) (hR : 0 ≤ R) :
    (volume (Metric.closedBall (0 : ℂ) R)).toReal = R ^ 2 * Real.pi := by
  rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR]
  simp

/-- The cutoff-gradient term tends to `0` as the cutoff radius tends to infinity. -/
theorem tendsto_cutoff_term {n : ℕ} (X : Fin n → ℂ) :
    Tendsto (fun R : ℝ => ∫ x, chartPot X x * gradDot (cutoffR R) (chartPot X) x) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_fderiv_bump_le
  set M : ℝ := ∑ i, ‖X i‖ with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hX : ∀ i, ‖X i‖ ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖X i‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  set R₀ : ℝ := 8 * (1 + M) ^ 2 with hR₀
  have hR₀1 : 1 ≤ R₀ := by nlinarith
  set c₁ : ℝ := n * (4 * (1 + M) ^ 2) with hc₁
  set c₂ : ℝ := n * (16 * (1 + M) ^ 2) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set B : ℝ := 8 * Real.pi * (c₁ * c₂ * K) with hB
  have hbound : ∀ R : ℝ, R₀ ≤ R →
      ‖∫ x, chartPot X x * gradDot (cutoffR R) (chartPot X) x‖ ≤ B / R ^ 2 := by
    intro R hR
    have hRpos : 0 < R := by linarith
    set S : Set ℂ := {x : ℂ | R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R} with hS
    have hSm : MeasurableSet S :=
      (measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const)
    have hzero : ∀ x ∉ S, chartPot X x * gradDot (cutoffR R) (chartPot X) x = 0 := by
      intro x hx
      by_cases h1 : ‖x‖ < R
      · simp [gradDot_eq_zero_of_eventuallyEq (cutoffR_eventuallyEq_one hRpos h1)]
      · have h2 : 2 * R < ‖x‖ := by
          by_contra h2
          exact hx ⟨not_lt.1 h1, not_lt.1 h2⟩
        simp [gradDot_eq_zero_of_eventuallyEq (c := 0) (cutoffR_eventuallyEq_zero hRpos h2)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hSsub : S ⊆ Metric.closedBall (0 : ℂ) (2 * R) := fun x hx => by simpa using hx.2
    have hvolS : volume S < ⊤ :=
      lt_of_le_of_lt (measure_mono hSsub) measure_closedBall_lt_top
    have hpt : ∀ x ∈ S, ‖chartPot X x * gradDot (cutoffR R) (chartPot X) x‖ ≤
        2 * c₁ * K * c₂ / R ^ 4 := by
      intro x hx
      have hxR : R ≤ ‖x‖ := hx.1
      have hx0 : R₀ ≤ ‖x‖ := hR.trans hxR
      have hxpos : 0 < ‖x‖ := by linarith
      have h1 := abs_chartPot_le X hM hX hx0
      have h2 := norm_fderiv_chartPot_le X hM hX hx0
      have h3 := abs_gradDot_le (cutoffR R) (chartPot X) x
      have h4 := norm_fderiv_cutoffR_le hRpos hK x
      rw [Real.norm_eq_abs, abs_mul]
      have hu : |chartPot X x| ≤ c₁ / R := by
        calc |chartPot X x| ≤ n * (4 * (1 + M) ^ 2 / ‖x‖) := h1
          _ = c₁ / ‖x‖ := by rw [hc₁]; ring
          _ ≤ c₁ / R := div_le_div_of_nonneg_left hc₁0 hRpos hxR
      have hd : ‖fderiv ℝ (chartPot X) x‖ ≤ c₂ / R ^ 2 := by
        calc ‖fderiv ℝ (chartPot X) x‖ ≤ n * (16 * (1 + M) ^ 2 / ‖x‖ ^ 2) := h2
          _ = c₂ / ‖x‖ ^ 2 := by rw [hc₂]; ring
          _ ≤ c₂ / R ^ 2 :=
            div_le_div_of_nonneg_left hc₂0 (by positivity) (pow_le_pow_left₀ hRpos.le hxR 2)
      have hg : |gradDot (cutoffR R) (chartPot X) x| ≤ 2 * (K / R * (c₂ / R ^ 2)) :=
        h3.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul h4 hd (norm_nonneg _) (by positivity)) (by norm_num))
      calc |chartPot X x| * |gradDot (cutoffR R) (chartPot X) x|
          ≤ (c₁ / R) * (2 * (K / R * (c₂ / R ^ 2))) :=
            mul_le_mul hu hg (abs_nonneg _) (by positivity)
        _ = 2 * c₁ * K * c₂ / R ^ 4 := by field_simp
    have hnorm := norm_setIntegral_le_of_norm_le_const hvolS hpt
    refine hnorm.trans ?_
    have hvolle : volume.real S ≤ (2 * R) ^ 2 * Real.pi := by
      rw [← volume_closedBall_toReal (2 * R) (by positivity)]
      exact ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono hSsub)
    calc 2 * c₁ * K * c₂ / R ^ 4 * volume.real S
        ≤ 2 * c₁ * K * c₂ / R ^ 4 * ((2 * R) ^ 2 * Real.pi) :=
          mul_le_mul_of_nonneg_left hvolle (by positivity)
      _ = B / R ^ 2 := by rw [hB]; field_simp; ring
  refine squeeze_zero_norm' (a := fun R => B / R ^ 2) ?_ ?_
  · filter_upwards [eventually_ge_atTop R₀] with R hR using hbound R hR
  · have h1 : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    exact (tendsto_const_nhds (x := B)).div_atTop h1

/-- The right-hand side `L = 2π n µ` of `Δ h_X = L`. -/
@[expose] noncomputable def chartLap (n : ℕ) (x : ℂ) : ℝ := 2 * Real.pi * n * dens x

theorem greenData_chartPot {n : ℕ} (X : Fin n → ℂ) :
    GreenData (Finset.univ.image X) (chartPot X) (chartLap n) where
  c2 x hx := (contDiffAt_chartPot X fun i h => hx (by simp [h])).of_le (by norm_cast)
  lap x hx := laplacian_chartPot X fun i h => hx (by simp [h])
  cont x _ := (continuous_const.mul continuous_dens).continuousAt

theorem integrableOn_chartPot_lap {n : ℕ} (X : Fin n → ℂ) (s : Set ℂ) :
    IntegrableOn (fun x => chartPot X x * chartLap n x) s := by
  have h := (integrable_chartPot_dens X).const_mul (2 * Real.pi * n)
  refine (h.congr (Filter.Eventually.of_forall fun x => ?_)).integrableOn
  simp only [chartLap]; ring

theorem tendsto_cutoff_main {n : ℕ} (X : Fin n → ℂ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun R : ℝ => ∫ x in Omega (Finset.univ.image X) η,
        cutoffR R x * (gradSq (chartPot X) x + chartPot X x * chartLap n x)) atTop
      (𝓝 (∫ x in Omega (Finset.univ.image X) η,
        (gradSq (chartPot X) x + chartPot X x * chartLap n x))) := by
  have hint : IntegrableOn (fun x => gradSq (chartPot X) x + chartPot X x * chartLap n x)
      (Omega (Finset.univ.image X) η) :=
    (integrableOn_gradSq_chartPot X hη).add (integrableOn_chartPot_lap X _)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖gradSq (chartPot X) x + chartPot X x * chartLap n x‖) ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall fun R => ?_
    have hm : Measurable fun x => cutoffR R x * (gradSq (chartPot X) x + chartPot X x * chartLap n x) := by
      have hL : Measurable (chartLap n) :=
        (measurable_const.mul continuous_dens.measurable)
      exact (contDiff_cutoffR R).continuous.measurable.mul
        ((measurable_gradSq _).add ((measurable_chartPot X).mul hL))
    exact hm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_of_nonneg (cutoffR_nonneg R x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoffR_le_one R x)
  · refine Filter.Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (max ‖x‖ 1)] with R hR
    have hRpos : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
    rw [cutoffR_eq_one hRpos ((le_max_left _ _).trans hR), one_mul]

/-- **The exact Green identity** for the chart potential on the plane. -/
theorem green_plane_exterior {n : ℕ} (X : Fin n → ℂ) {ρ η : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ p ∈ Finset.univ.image X, ∀ q ∈ Finset.univ.image X, p ≠ q → 4 * ρ ≤ ‖p - q‖)
    (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∫ x in Omega (Finset.univ.image X) η, (gradSq (chartPot X) x + chartPot X x * chartLap n x) =
      -∑ p ∈ Finset.univ.image X, circleTerm (chartPot X) p η := by
  set M : ℝ := ∑ i, ‖X i‖ with hMdef
  have hX : ∀ i, ‖X i‖ ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖X i‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hR : ∀ R : ℝ, M + 3 * ρ ≤ R →
      (∫ x in Omega (Finset.univ.image X) η,
          cutoffR R x * (gradSq (chartPot X) x + chartPot X x * chartLap n x)) +
        ∫ x, chartPot X x * gradDot (cutoffR R) (chartPot X) x =
      -∑ p ∈ Finset.univ.image X, circleTerm (chartPot X) p η := by
    intro R hRM
    have hRpos : 0 < R := by linarith
    have D : CutoffData (Finset.univ.image X) ρ (cutoffR R) :=
      { pos := hρ
        sep := hsep
        smooth := contDiff_cutoffR R
        compact := cutoffR_hasCompactSupport hRpos
        one := by
          rintro x ⟨p, hp, hxp⟩
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
          refine cutoffR_eq_one hRpos ?_
          have h1 : ‖x‖ ≤ ‖x - X i‖ + ‖X i‖ := by
            calc ‖x‖ = ‖(x - X i) + X i‖ := by ring_nf
              _ ≤ ‖x - X i‖ + ‖X i‖ := norm_add_le _ _
          linarith [hX i] }
    exact green_cutoff D (greenData_chartPot X) hη hηρ
  have h1 := tendsto_cutoff_main X hη
  have h2 := tendsto_cutoff_term X
  have h3 := h1.add h2
  have h4 : Tendsto (fun R : ℝ => (∫ x in Omega (Finset.univ.image X) η,
          cutoffR R x * (gradSq (chartPot X) x + chartPot X x * chartLap n x)) +
        ∫ x, chartPot X x * gradDot (cutoffR R) (chartPot X) x) atTop
      (𝓝 (-∑ p ∈ Finset.univ.image X, circleTerm (chartPot X) p η)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (M + 3 * ρ)] with R hRM using (hR R hRM).symm
  have := tendsto_nhds_unique h3 h4
  simpa using this

end Sphere

end SandierSerfaty

end
