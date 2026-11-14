/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorSeries

/-!
# The first-order consequences of `f₀ ∈ C²`, `e ∈ C¹`

The paper (§5.4 and Lemma `cal:stationarity`) uses `C¹` of `f₀` and `e` and
differentiation under the integral sign in `cal:stationarity` without proof.

* `contDiffOn_f₀`, `contDiffOn_e` (`SectorSeries.lean`) give continuous `f₀'`, `e'` on `(0, ∞)`
  (`continuousOn_deriv_f₀`, `continuousOn_deriv_e`), which is what differentiation under the integral sign in
  `cal:stationarity` needs (the integrands are `C¹` in `(d, s)` away from `t = 0`);
* `tendsto_f₀_quotient`: `(f₀(√(p²+s²)) - f₀(p))/s² → f₀'(p)/(2p)` as `s → 0` (paper §5.5), i.e. the first
  integrand of `lam` extends continuously to `s = 0`.
-/

open Set Filter Topology

public section

namespace SandierSerfaty

namespace Calibration

theorem continuousOn_deriv_f₀ : ContinuousOn (deriv f₀) (Ioi 0) :=
  (contDiffOn_f₀.deriv_of_isOpen isOpen_Ioi (m := 0) (by norm_num)).continuousOn

theorem continuousOn_deriv_e : ContinuousOn (deriv e) (Ioi 0) :=
  (contDiffOn_e.deriv_of_isOpen isOpen_Ioi (m := 0) (by norm_num)).continuousOn

theorem continuousOn_f₀ : ContinuousOn f₀ (Ioi 0) := contDiffOn_f₀.continuousOn

theorem continuousOn_e : ContinuousOn e (Ioi 0) := contDiffOn_e.continuousOn

theorem differentiableAt_f₀ {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ f₀ t :=
  (contDiffOn_f₀.differentiableOn (by norm_num) t ht).differentiableAt (Ioi_mem_nhds ht)

theorem differentiableAt_e {t : ℝ} (ht : 0 < t) : DifferentiableAt ℝ e t :=
  (contDiffOn_e.differentiableOn one_ne_zero t ht).differentiableAt (Ioi_mem_nhds ht)

/-- The first integrand of `lam` extends continuously to `s = 0` with value `f₀'(p)/(2p)`
(paper §5.5). -/
theorem tendsto_f₀_quotient :
    Tendsto (fun s : ℝ => (f₀ (√(p ^ 2 + s ^ 2)) - f₀ p) / s ^ 2) (𝓝[≠] 0)
      (𝓝 (deriv f₀ p / (2 * p))) := by
  have hp := p_pos
  have hsq : HasDerivAt (fun u : ℝ => √(p ^ 2 + u)) (1 / (2 * p)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_add (p ^ 2)).sqrt (by simp; exact hp.ne')
    refine h.congr_deriv ?_
    simp [Real.sqrt_sq hp.le]
  have hf : HasDerivAt f₀ (deriv f₀ (√(p ^ 2 + 0))) (√(p ^ 2 + 0)) := by
    have : √(p ^ 2 + 0) = p := by simp [Real.sqrt_sq hp.le]
    rw [this]
    exact (differentiableAt_f₀ hp).hasDerivAt
  have hφ : HasDerivAt (fun u : ℝ => f₀ (√(p ^ 2 + u))) (deriv f₀ p * (1 / (2 * p))) 0 := by
    have h := hf.comp 0 hsq
    have e : √(p ^ 2 + 0) = p := by simp [Real.sqrt_sq hp.le]
    rw [e] at h
    exact h
  have hs := hφ.tendsto_slope_zero
  -- compose with `s ↦ s²`
  have hcomp : Tendsto (fun s : ℝ => s ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => s ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_pow 2).tendsto (0 : ℝ)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact pow_ne_zero 2 hs
  have h2 := hs.comp hcomp
  refine (h2.congr fun s => ?_).trans ?_
  · simp only [Function.comp, smul_eq_mul]
    have : √(p ^ 2) = p := Real.sqrt_sq hp.le
    simp only [zero_add, add_zero, this]
    field_simp
  · rw [show deriv f₀ p / (2 * p) = deriv f₀ p * (1 / (2 * p)) by ring]

end Calibration

end SandierSerfaty

end
