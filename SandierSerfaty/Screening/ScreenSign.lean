/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenFluxEnergy

/-!
# Kept singularities against the new fields (screening note, Lemma 4.26)

The screening note, Lemma 4.26 (`lem:sign`). For `A : Asm` with
`A.Good D` under `D.Hyp`, let `Y_F = ∑_k V_k - ∑_{q ∈ D*} W_q` (`Asm.YF`) and, for a kept charge
`p`, let `F_p = f_{α_p,1/4}(· - p)` be the continuous representative (`truncDiff`).

* `Good.integral_inner_Vflux`: `∫ (∑_k V_k) · ∇χ = -∫ (∑_k 1_{H_k} f_k) χ` for Lipschitz `χ` with
  compact support;
* `Good.ae_sum_fluxSrc_eq`: on `O₂ = {δ > d + ½}`, `∑_k 1_{H_k} f_k = 2π ∑_{D*} u_q` a.e.;
* `Good.integral_inner_YF`: for such `χ` vanishing on `{δ ≤ d + ½}`,
  `∫ Y_F · ∇χ = -2π ∑_{q ∈ D*} ⨍_{∂B(q,1/4)} χ`;
* `Good.integral_inner_YF_Fp_nonneg`: hence `∫ Y_F · ∇F_p ≥ 0` for `p ∈ K` (`F_p ≤ 0`).
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

/-- The pairing of an integrable field with the gradient of a Lipschitz function is integrable. -/
theorem integrable_inner_gradient_of_lipschitz {V : ℂ → ℂ} (hV : Integrable V) {χ : ℂ → ℝ}
    {K : ℝ≥0} (hχ : LipschitzWith K χ) : Integrable fun x => inner ℝ (V x) (gradient χ x) :=
  Integrable.mono' (hV.norm.mul_const K) (hV.aestronglyMeasurable.inner (aestronglyMeasurable_gradient χ))
    (Eventually.of_forall fun x => (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_gradient_le_of_lipschitz hχ x) (norm_nonneg _)))

/-- An integrable function times a continuous compactly supported one is integrable. -/
theorem integrable_mul_of_hasCompactSupport {f : ℂ → ℝ} (hf : Integrable f) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) : Integrable fun x => f x * χ x := by
  obtain ⟨M, hM⟩ := hχc.exists_bound_of_continuous hχ
  refine Integrable.mono' (hf.norm.mul_const M) (hf.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)

namespace Scr

open Pinwheel

namespace Asm

/-- `Y_F = ∑_k V_k - ∑_{q ∈ D*} W_q`. -/
@[expose] noncomputable def YF (D : Data) (A : Asm) (x : ℂ) : ℂ :=
  A.Vflux D x - ∑ q ∈ D.Ds, radialW (1 / 4) (x - q)

/-- The continuous representative `F_p = f_{α_p,1/4}(· - p)` of a kept charge. -/
@[expose] noncomputable def Fp (D : Data) (p : ℂ) (x : ℂ) : ℝ := truncDiff (D.α p) (1 / 4) (x - p)

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

theorem integrable_fluxV {jk : Fin 4 × ℕ} (hjk : jk ∈ A.cols) :
    Integrable (A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2) :=
  (h.cutHyp.isFieldPiece_fluxV hA.isCut (mem_cols.1 hjk)).1

theorem integrable_fluxSrc {jk : Fin 4 × ℕ} (hjk : jk ∈ A.cols) : Integrable (fluxSrc D A jk) :=
  (h.cutHyp.isFieldPiece_fluxV hA.isCut (mem_cols.1 hjk)).2.1

theorem integrable_Vflux : Integrable (A.Vflux D) := (hA.isFieldPiece_Vflux h).1

theorem integrable_YF : Integrable (A.YF D) := by
  have hW : Integrable fun x => ∑ q ∈ D.Ds, radialW (1 / 4) (x - q) :=
    integrable_finsetSum _ fun q _ => (integrable_radialW (by norm_num)).comp_sub_right q
  exact (hA.integrable_Vflux h).sub hW

/-- The pairing of the flux-cell field with Lipschitz test functions. -/
theorem integral_inner_Vflux {χ : ℂ → ℝ} {K : ℝ≥0} (hχ : LipschitzWith K χ)
    (hχc : HasCompactSupport χ) :
    ∫ x, inner ℝ (A.Vflux D x) (gradient χ x) = -∫ x, (∑ jk ∈ A.cols, fluxSrc D A jk x) * χ x := by
  have hint : ∀ jk ∈ A.cols, Integrable fun x =>
      inner ℝ (A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x) (gradient χ x) := fun jk hjk =>
    integrable_inner_gradient_of_lipschitz (hA.integrable_fluxV h hjk) hχ
  have hint' : ∀ jk ∈ A.cols, Integrable fun x => fluxSrc D A jk x * χ x := fun jk hjk =>
    integrable_mul_of_hasCompactSupport (hA.integrable_fluxSrc h hjk) hχ.continuous hχc
  have hV : (fun x => inner ℝ (A.Vflux D x) (gradient χ x)) = fun x =>
      ∑ jk ∈ A.cols, inner ℝ (A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x) (gradient χ x) := by
    ext x; rw [Vflux, sum_inner]
  have hS : (fun x => (∑ jk ∈ A.cols, fluxSrc D A jk x) * χ x) =
      fun x => ∑ jk ∈ A.cols, fluxSrc D A jk x * χ x := by
    ext x; rw [Finset.sum_mul]
  rw [hV, hS, integral_finsetSum _ hint, integral_finsetSum _ hint', ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun jk hjk => ?_
  rw [h.cutHyp.integral_inner_fluxV hA.isCut (mem_cols.1 hjk) hχ]
  congr 1
  rw [← integral_indicator (A.cut.fluxRect D.c D.t D.d D.ℓ jk.1 jk.2).measurableSet_carrier]
  congr 1; ext x
  simp only [fluxSrc, fluxRect, indicator_mul_left]

/-- On `O₂ = {δ > d + ½}` the flux-cell sources add up to `2π ∑_{D*} u_q` (a.e.). -/
theorem ae_sum_fluxSrc_eq :
    ∀ᵐ x, D.d + 1 / 2 < D.dep x → ∑ jk ∈ A.cols, fluxSrc D A jk x = 2 * π * D.uSum x := by
  filter_upwards [hA.src_ae_eq h] with x hx hdep
  have hc : ∀ j : Fin 4, carrySrc D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x = 0 := by
    intro j
    refine carrySrc_eq_zero_of_notMem fun hxc => ?_
    have := (h.cutHyp.sqDepth_mem_of_mem_carryRect hA.isCut j hxc).2
    change D.dep x ≤ D.d - 1 at this
    linarith
  have hp : ∀ i ∈ A.pcs, pieceSrc D A i x = 0 := by
    intro i hi
    refine indicator_of_notMem (fun hxp => ?_) _
    have := hA.dep_le_of_mem_pc h hi hxp
    linarith
  have hQ : x ∈ D.Q := Data.mem_Q_iff.2 (by linarith [h.d_pos])
  rw [Finset.sum_eq_zero fun j _ => hc j, Finset.sum_eq_zero hp, indicator_of_mem hQ, add_zero,
    add_zero] at hx
  rw [hx, Data.g, Data.psi_eq_one (by linarith), Data.gradient_psi_of_lt (by linarith),
    inner_zero_right]
  ring

/-- **Lemma 4.26** (pairing): for Lipschitz `χ` with compact support vanishing on `{δ ≤ d + ½}`,
`∫ Y_F · ∇χ = -2π ∑_{q ∈ D*} ⨍_{∂B(q,1/4)} χ`. -/
theorem integral_inner_YF {χ : ℂ → ℝ} {K : ℝ≥0} (hχ : LipschitzWith K χ)
    (hχc : HasCompactSupport χ) (hχ0 : ∀ x, D.dep x ≤ D.d + 1 / 2 → χ x = 0) :
    ∫ x, inner ℝ (A.YF D x) (gradient χ x) =
      -(2 * π * ∑ q ∈ D.Ds, Real.circleAverage χ q (1 / 4)) := by
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  have hintW : ∀ q ∈ D.Ds, Integrable fun x => inner ℝ (radialW (1 / 4) (x - q)) (gradient χ x) :=
    fun q _ => integrable_inner_gradient_of_lipschitz ((integrable_radialW hq).comp_sub_right q) hχ
  have hYF : (fun x => inner ℝ (A.YF D x) (gradient χ x)) = fun x =>
      inner ℝ (A.Vflux D x) (gradient χ x) -
        ∑ q ∈ D.Ds, inner ℝ (radialW (1 / 4) (x - q)) (gradient χ x) := by
    ext x; rw [YF, inner_sub_left, sum_inner]
  rw [hYF, integral_sub (integrable_inner_gradient_of_lipschitz (hA.integrable_Vflux h) hχ)
    (integrable_finsetSum _ hintW), integral_finsetSum _ hintW, hA.integral_inner_Vflux h hχ hχc,
    Finset.sum_congr rfl fun q _ => integral_inner_radialW hq q hχ]
  -- the flux sources against `χ`
  have hflux : ∫ x, (∑ jk ∈ A.cols, fluxSrc D A jk x) * χ x =
      ∑ q ∈ D.Ds, 2 * π * ∫ x, radialU (1 / 4) (x - q) * χ x := by
    have hint : ∀ q ∈ D.Ds, Integrable fun x => radialU (1 / 4) (x - q) * χ x := fun q _ =>
      integrable_mul_of_hasCompactSupport ((integrable_radialU _).comp_sub_right q) hχ.continuous hχc
    have hae : (fun x => (∑ jk ∈ A.cols, fluxSrc D A jk x) * χ x) =ᵐ[volume]
        fun x => ∑ q ∈ D.Ds, 2 * π * (radialU (1 / 4) (x - q) * χ x) := by
      filter_upwards [hA.ae_sum_fluxSrc_eq h] with x hx
      by_cases hdep : D.d + 1 / 2 < D.dep x
      · rw [hx hdep, Data.uSum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      · rw [hχ0 x (not_lt.1 hdep)]; simp
    rw [integral_congr_ae hae, integral_finsetSum _ fun q hq' => (hint q hq').const_mul _]
    exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  rw [hflux, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **Lemma 4.26** (sign): for a kept charge `p`, `∫ Y_F · ∇F_p ≥ 0`. -/
theorem integral_inner_YF_Fp_nonneg {p : ℂ} (hp : p ∈ D.K) :
    0 ≤ ∫ x, inner ℝ (A.YF D x) (gradient (Fp D p) x) := by
  have hpC := h.K_subset_C hp
  have hα := h.hα p hpC
  have hL : LipschitzWith (Real.toNNReal (D.α p)⁻¹) (Fp D p) :=
    lipschitzWith_truncDiff_sub hα.1 hα.2 p
  have hc : HasCompactSupport (Fp D p) := hasCompactSupport_truncDiff _ _ p
  have h0 : ∀ x, D.dep x ≤ D.d + 1 / 2 → Fp D p x = 0 := by
    intro x hx
    refine truncDiff_eq_zero ?_
    have h1 := Data.dep_le_add (D := D) p x
    have h2 := (h.mem_K.1 hp).2
    rw [norm_sub_rev] at h1
    linarith
  rw [hA.integral_inner_YF h hL hc h0, neg_nonneg]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun q _ => ?_)
  refine Real.circleAverage_mono_on_of_le_circle ?_ fun x _ => truncDiff_nonpos hα.1 _
  exact hL.continuous.continuousOn.circleIntegrable'

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
