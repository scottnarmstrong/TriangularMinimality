/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.ChartDecay
public import SandierSerfaty.Sphere.GreenCutoff

/-!
# Integrals of the chart potential against `µ` and of `|∇h_X|²` (sphere note, Proposition 3.4, inputs)

* `Sphere.integrable_chartPot_dens`, `Sphere.integral_chartPot_dens`:
  `∫ h_X µ = -½ ∑ V(xᵢ) + n/2` (from Lemma 3.2);
* `Sphere.integrableOn_gradSq_chartPot`: `|∇h_X|²` is integrable on `{x | ∀ i, η ≤ |x - xᵢ|}`.
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem integrable_gKer_dens (p : ℂ) : Integrable fun x : ℂ => gKer (x - p) * dens x := by
  have h := (integrable_log_dens p).neg
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply, gKer, norm_sub_rev p x]
  ring

theorem integral_gKer_dens (p : ℂ) : ∫ x : ℂ, gKer (x - p) * dens x = potU p := by
  unfold potU
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [gKer, norm_sub_rev p x]

theorem chartPot_mul_dens {n : ℕ} (X : Fin n → ℂ) (x : ℂ) :
    chartPot X x * dens x =
      ∑ i, gKer (x - X i) * dens x + (n : ℝ) / 2 * (potV x * dens x) := by
  unfold chartPot
  rw [add_mul, Finset.sum_mul]
  ring

theorem integrable_chartPot_dens {n : ℕ} (X : Fin n → ℂ) :
    Integrable fun x : ℂ => chartPot X x * dens x := by
  have h : (fun x : ℂ => chartPot X x * dens x) =
      fun x => ∑ i, gKer (x - X i) * dens x + (n : ℝ) / 2 * (potV x * dens x) :=
    funext (chartPot_mul_dens X)
  rw [h]
  exact (integrable_finsetSum _ fun i _ => integrable_gKer_dens (X i)).add
    (integrable_potV_dens.const_mul _)

/-- `∫ h_X µ = -½ ∑ V(xᵢ) + n/2`. -/
theorem integral_chartPot_dens {n : ℕ} (X : Fin n → ℂ) :
    ∫ x : ℂ, chartPot X x * dens x = -(1 / 2) * ∑ i, potV (X i) + (n : ℝ) / 2 := by
  have h : (fun x : ℂ => chartPot X x * dens x) =
      fun x => ∑ i, gKer (x - X i) * dens x + (n : ℝ) / 2 * (potV x * dens x) :=
    funext (chartPot_mul_dens X)
  rw [h, integral_add (integrable_finsetSum _ fun i _ => integrable_gKer_dens (X i))
    (integrable_potV_dens.const_mul _), integral_finsetSum _ fun i _ => integrable_gKer_dens (X i),
    integral_const_mul, integral_potV_dens]
  simp only [integral_gKer_dens, potU_eq]
  rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  ring

theorem measurable_gradSq (u : ℂ → ℝ) : Measurable (gradSq u) := by
  have h1 : Measurable fun x => fderiv ℝ u x 1 := measurable_fderiv_apply_const ℝ u 1
  have h2 : Measurable fun x => fderiv ℝ u x Complex.I := measurable_fderiv_apply_const ℝ u Complex.I
  exact (h1.pow_const 2).add (h2.pow_const 2)

theorem gradSq_le (u : ℂ → ℝ) (x : ℂ) : gradSq u x ≤ 2 * ‖fderiv ℝ u x‖ ^ 2 := by
  have h1 : |fderiv ℝ u x 1| ≤ ‖fderiv ℝ u x‖ := by
    have := (fderiv ℝ u x).le_opNorm 1
    simpa using this
  have h2 : |fderiv ℝ u x Complex.I| ≤ ‖fderiv ℝ u x‖ := by
    have := (fderiv ℝ u x).le_opNorm Complex.I
    simpa using this
  unfold gradSq pd₁ pd₂
  have e1 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
  have e2 := sq_le_sq' (neg_le_of_abs_le h2) (le_of_abs_le h2)
  linarith

/-- `|∇h_X|²` is integrable off the `η`-discs about the points. -/
theorem integrableOn_gradSq_chartPot {n : ℕ} (X : Fin n → ℂ) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (gradSq (chartPot X)) (Omega (Finset.univ.image X) η) := by
  set M : ℝ := ∑ i, ‖X i‖ with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hX : ∀ i, ‖X i‖ ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖X i‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  set R₀ : ℝ := 8 * (1 + M) ^ 2 with hR₀
  have hR₀1 : 1 ≤ R₀ := by nlinarith
  have hxP : ∀ x ∈ Omega (Finset.univ.image X) η, ∀ i, x ≠ X i := by
    intro x hx i h
    have := hx (X i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [h, sub_self, norm_zero] at this
    exact absurd this (not_le.2 hη)
  have hsplit : Omega (Finset.univ.image X) η ⊆
      (Omega (Finset.univ.image X) η ∩ Metric.closedBall 0 R₀) ∪ {x : ℂ | R₀ ≤ ‖x‖} := by
    intro x hx
    by_cases h : ‖x‖ ≤ R₀
    · exact Or.inl ⟨hx, by simpa using h⟩
    · exact Or.inr (not_le.1 h).le
  refine IntegrableOn.mono_set (t := (Omega (Finset.univ.image X) η ∩ Metric.closedBall 0 R₀) ∪
    {x : ℂ | R₀ ≤ ‖x‖}) ?_ hsplit
  refine IntegrableOn.union ?_ ?_
  · refine ContinuousOn.integrableOn_compact
      ((isCompact_closedBall 0 R₀).inter_left (isClosed_Omega _ η)) ?_
    intro x hx
    have hxi := hxP x hx.1
    have hd := contDiffAt_chartPot X hxi
    have h1 : ∀ v : ℂ, ContinuousAt (fun y => fderiv ℝ (chartPot X) y v) x := fun v =>
      (contDiffAt_pd (n := 1) (hd.of_le (by norm_cast)) v).continuousAt
    have : ContinuousAt (gradSq (chartPot X)) x := by
      unfold gradSq pd₁ pd₂
      exact ((h1 1).pow 2).add ((h1 Complex.I).pow 2)
    exact this.continuousWithinAt
  · set c : ℝ := n * (16 * (1 + M) ^ 2) with hc
    have hg : Integrable (fun x : ℂ => (2 * c ^ 2 * 16) * (1 + ‖x‖) ^ (-4 : ℝ)) := by
      refine Integrable.const_mul ?_ _
      exact integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    refine hg.integrableOn.mono' (measurable_gradSq _).aestronglyMeasurable ?_
    rw [ae_restrict_iff' (measurableSet_le measurable_const measurable_norm)]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx' : R₀ ≤ ‖x‖ := hx
    have hxpos : 0 < ‖x‖ := by linarith
    have hnorm := norm_fderiv_chartPot_le X hM hX (x := x) hx'
    have hA := gradSq_le (chartPot X) x
    rw [Real.norm_of_nonneg (by unfold gradSq pd₁ pd₂; positivity)]
    have h4 : ‖fderiv ℝ (chartPot X) x‖ ≤ c / ‖x‖ ^ 2 := by
      calc _ ≤ _ := hnorm
        _ = c / ‖x‖ ^ 2 := by rw [hc]; ring
    have h5 : ‖fderiv ℝ (chartPot X) x‖ ^ 2 ≤ (c / ‖x‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4 2
    have h6 : (1 + ‖x‖) ^ (-4 : ℝ) = ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h7 : (1 + ‖x‖) ^ 4 ≤ 16 * ‖x‖ ^ 4 := by
      have : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
      calc (1 + ‖x‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 16 * ‖x‖ ^ 4 := by ring
    rw [h6]
    calc gradSq (chartPot X) x ≤ 2 * (c / ‖x‖ ^ 2) ^ 2 := by linarith
      _ = 2 * c ^ 2 / ‖x‖ ^ 4 := by field_simp
      _ ≤ (2 * c ^ 2 * 16) * ((1 + ‖x‖) ^ 4)⁻¹ := by
        rw [div_eq_mul_inv]
        have h8 : (‖x‖ ^ 4)⁻¹ ≤ 16 * ((1 + ‖x‖) ^ 4)⁻¹ := by
          rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
        have h9 : 0 ≤ 2 * c ^ 2 := by positivity
        calc 2 * c ^ 2 * (‖x‖ ^ 4)⁻¹ ≤ 2 * c ^ 2 * (16 * ((1 + ‖x‖) ^ 4)⁻¹) :=
              mul_le_mul_of_nonneg_left h8 h9
          _ = 2 * c ^ 2 * 16 * ((1 + ‖x‖) ^ 4)⁻¹ := by ring

end Sphere

end SandierSerfaty

end
