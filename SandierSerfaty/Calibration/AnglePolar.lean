/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorGrad
public import SandierSerfaty.Calibration.SectorRest

/-!
# The trial potential and its energy density along the rays of the model sector

Paper `cal:trial-potential`. For `φ ∈ (-α, β)` write `T φ = d sec φ = Tφ d φ`. On the ray of angle `φ`,

* `modelH_polar`: `H(r e^{iφ}) = B(r) + ser (Dᵢ(T)) T r`;
* `gradSq_polar`: `|∇H|² = (B'(r) + (1/r) ser (kᵢ Dᵢ(T)) T r)² + ((tan φ / r) ser (Qᵢ(T)) T r)²`;
* `restSq d w = |∇H|²(w) - B'(‖w‖)²` is the non-singular part of the energy density; `rest_polar`:
  `r · restSq = 2 B' ΣA + ΣA²/r + tan²φ ΣQ²/r` (the integrand of `integral_rest_inner`).

Also `exists_polar_rep` (every point of the sector is `polarCoord.symm (r, φ)` with `r cos φ < d`) and
`Tφ_mem` (`T φ ∈ [d, secRadius]`).
-/

open Set Filter Topology MeasureTheory Real

public section

namespace SandierSerfaty

namespace Calibration

open SandierSerfaty.Dual

/-- `T(φ) = d sec φ`, the length of the ray of angle `φ` in the sector. -/
@[expose] noncomputable def Tφ (d φ : ℝ) : ℝ := d / Real.cos φ

theorem cos_pos_of_mem {α β φ : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) (hφ : φ ∈ Ioo (-α) β) :
    0 < Real.cos φ :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(abs_lt.1 hα).2, hφ.1, pi_pos, (abs_lt.1 hα).1], by linarith [(abs_lt.1 hβ).2, hφ.2]⟩

theorem Tφ_mem {d α β φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hφ : φ ∈ Ioo (-α) β) : Tφ d φ ∈ Icc d (secRadius d α β) := by
  have hc := cos_pos_of_mem hα hβ hφ
  have hc0 := cos_max_pos hα hβ
  refine ⟨?_, ?_⟩
  · unfold Tφ
    rw [le_div_iff₀ hc]
    nlinarith [Real.cos_le_one φ]
  · unfold Tφ secRadius
    have hφ' : |φ| ≤ max |α| |β| := by
      rw [abs_le]
      constructor
      · have := le_abs_self α; have := le_max_left |α| |β|; linarith [hφ.1]
      · have := le_abs_self β; have := le_max_right |α| |β|; linarith [hφ.2]
    have hcos : Real.cos (max |α| |β|) ≤ Real.cos φ := by
      rw [← Real.cos_abs φ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [pi_pos, max_lt hα hβ]) hφ'
    exact div_le_div_of_nonneg_left hd.le hc0 hcos

theorem Tφ_pos {d α β φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hφ : φ ∈ Ioo (-α) β) : 0 < Tφ d φ := div_pos hd (cos_pos_of_mem hα hβ hφ)

theorem lt_Tφ_iff {d α β r φ : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) (hφ : φ ∈ Ioo (-α) β) :
    r * Real.cos φ < d ↔ r < Tφ d φ := by
  unfold Tφ; rw [lt_div_iff₀ (cos_pos_of_mem hα hβ hφ)]

theorem exists_polar_rep {d α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) {w : ℂ}
    (hw : w ∈ modelSector d α β) :
    ∃ r φ : ℝ, 0 < r ∧ φ ∈ Ioo (-α) β ∧ r * Real.cos φ < d ∧ w = Complex.polarCoord.symm (r, φ) := by
  have hw0 := ne_zero_of_mem_modelSector hw
  obtain ⟨h1, h2⟩ := arg_mem_of_mem_modelSector hα hβ hw
  have hsymm : w = Complex.polarCoord.symm (‖w‖, Complex.arg w) := by
    rw [Complex.polarCoord_symm_apply]
    simp only
    have := Complex.norm_mul_cos_add_sin_mul_I w
    push_cast
    exact this.symm
  refine ⟨‖w‖, Complex.arg w, norm_pos_iff.2 hw0, ⟨h1, h2⟩, ?_, hsymm⟩
  have := polarCoord_symm_re ‖w‖ (Complex.arg w)
  rw [← hsymm] at this
  rw [← this]; exact hw.2.1

theorem tφ_ratio {d r φ : ℝ} (hd : 0 < d) (hc : 0 < Real.cos φ) :
    r * Real.cos φ / d = r / Tφ d φ := by
  unfold Tφ; field_simp

theorem modelH_polar {d α β r φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hr : 0 < r)
    (hφ : φ ∈ Ioo (-α) β) (_hrt : r * Real.cos φ < d) :
    modelH radialData d (Complex.polarCoord.symm (r, φ)) =
      B r + ser (fun i => D i (Tφ d φ)) (Tφ d φ) r := by
  have hc := cos_pos_of_mem hα hβ hφ
  have hn : ‖(Complex.polarCoord.symm (r, φ) : ℂ)‖ = r := polarCoord_symm_norm (x := (r, φ)) hr
  have hre := polarCoord_symm_re r φ
  rw [modelH_eq, hn]
  congr 1
  unfold serF ser
  refine tsum_congr fun i => ?_
  have hgpos : 0 < r / Tφ d φ := div_pos hr (Tφ_pos hd hα hβ hφ)
  simp only [termFn, PsiM, hn, radialData]
  have : r / (r / Tφ d φ) = Tφ d φ := by field_simp
  rw [hre, tφ_ratio hd hc, this]
  ring

theorem gradSq_polar {d α β r φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hr : 0 < r)
    (hφ : φ ∈ Ioo (-α) β) (hrt : r * Real.cos φ < d) :
    Analysis.gradSq (modelH radialData d) (Complex.polarCoord.symm (r, φ)) =
      (deriv B r + 1 / r * ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r) ^ 2 +
        (Real.tan φ / r * ser (fun i => Q i (Tφ d φ)) (Tφ d φ) r) ^ 2 := by
  have hc := cos_pos_of_mem hα hβ hφ
  rw [gradSq_modelH_polar hd hα hβ hr hφ hrt]
  have e1 : ∑' i, (k i : ℝ) * (r * Real.cos φ / d) ^ k i * D i (d / Real.cos φ) =
      ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r := by
    unfold ser
    refine tsum_congr fun i => ?_
    rw [tφ_ratio hd hc]; unfold Tφ; ring
  have e2 : ∑' i, (r * Real.cos φ / d) ^ k i * Q i (d / Real.cos φ) =
      ser (fun i => Q i (Tφ d φ)) (Tφ d φ) r := by
    unfold ser
    refine tsum_congr fun i => ?_
    rw [tφ_ratio hd hc]; unfold Tφ; ring
  rw [e1, e2]

/-- The non-singular part `|∇H|² - B'(‖w‖)²` of the energy density of the trial potential. -/
@[expose] noncomputable def restSq (d : ℝ) (w : ℂ) : ℝ :=
  Analysis.gradSq (modelH radialData d) w - (deriv B ‖w‖) ^ 2

theorem rest_polar {d α β r φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hr : 0 < r)
    (hφ : φ ∈ Ioo (-α) β) (hrt : r * Real.cos φ < d) :
    r * restSq d (Complex.polarCoord.symm (r, φ)) =
      2 * deriv B r * ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r +
        ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r ^ 2 / r +
        Real.tan φ ^ 2 * (ser (fun i => Q i (Tφ d φ)) (Tφ d φ) r ^ 2 / r) := by
  unfold restSq
  rw [gradSq_polar hd hα hβ hr hφ hrt, polarCoord_symm_norm (x := (r, φ)) hr]
  simp only
  field_simp
  ring

theorem restSq_eq_polar {d α β r φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) (hr : 0 < r)
    (hφ : φ ∈ Ioo (-α) β) (hrt : r * Real.cos φ < d) :
    restSq d (Complex.polarCoord.symm (r, φ)) =
      2 * deriv B r * (ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r / r) +
        (ser (fun i => (k i : ℝ) * D i (Tφ d φ)) (Tφ d φ) r / r) ^ 2 +
        Real.tan φ ^ 2 * (ser (fun i => Q i (Tφ d φ)) (Tφ d φ) r / r) ^ 2 := by
  unfold restSq
  rw [gradSq_polar hd hα hβ hr hφ hrt, polarCoord_symm_norm (x := (r, φ)) hr]
  simp only
  field_simp
  ring

end Calibration

end SandierSerfaty

end
