/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.Cube
public import SandierSerfaty.Torus.ChargeSet
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Counting lattice points in large squares

For a lattice `Γ ⊆ ℂ` of covolume `1` and the squares `□_ℓ = [-ℓ/2, ℓ/2]²`
(`SandierSerfaty.cube`), `#(Γ ∩ □_ℓ) / ℓ² → 1` as `ℓ → ∞` over the reals
(`SandierSerfaty.Torus.tendsto_ncard_inter_cube_div`), and the same holds for `#(Γ ∩ □_{ℓ + c}) / ℓ²`.
The real-parameter statement is Mathlib's `ZLattice.covolume.tendsto_card_le_div'` applied to the
degree-two homogeneous function `(max |re z| |im z|)²`.
-/

open MeasureTheory Filter Topology Metric Set

public section

namespace SandierSerfaty

namespace Torus

theorem mem_cube_iff {ℓ : ℝ} {z : ℂ} : z ∈ cube ℓ ↔ |z.re| ≤ ℓ / 2 ∧ |z.im| ≤ ℓ / 2 := by
  simp only [cube, Complex.mem_reProdIm, mem_Icc, abs_le]

theorem cube_mono {a b : ℝ} (h : a ≤ b) : cube a ⊆ cube b := by
  intro z hz
  rw [mem_cube_iff] at hz ⊢
  exact ⟨hz.1.trans (by linarith), hz.2.trans (by linarith)⟩

theorem measurableSet_cube (ℓ : ℝ) : MeasurableSet (cube ℓ) :=
  (isClosed_Icc.reProdIm isClosed_Icc).measurableSet

theorem isBounded_cube (ℓ : ℝ) : Bornology.IsBounded (cube ℓ) :=
  (Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _)

theorem convex_cube (ℓ : ℝ) : Convex ℝ (cube ℓ) := by
  have h : cube ℓ = (Complex.reCLM ⁻¹' Icc (-(ℓ / 2)) (ℓ / 2)) ∩
      (Complex.imCLM ⁻¹' Icc (-(ℓ / 2)) (ℓ / 2)) := by
    ext z; simp [cube, Complex.mem_reProdIm]
  rw [h]
  exact ((convex_Icc _ _).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc _ _).linear_preimage Complex.imCLM.toLinearMap)

theorem volume_cube (ℓ : ℝ) : volume (cube ℓ) = ENNReal.ofReal ℓ ^ 2 := by
  have h : cube ℓ =
      Complex.measurableEquivRealProd ⁻¹' (Icc (-(ℓ / 2)) (ℓ / 2) ×ˢ Icc (-(ℓ / 2)) (ℓ / 2)) := by
    ext z; simp only [cube, Complex.mem_reProdIm, mem_preimage, mem_prod]; rfl
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, sq, show ℓ / 2 - -(ℓ / 2) = ℓ by ring]

/-- The intersection of a closed discrete set with a bounded set is finite. -/
theorem finite_lattice_inter {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] {s : Set ℂ}
    (hs : Bornology.IsBounded s) : ((Γ : Set ℂ) ∩ s).Finite := by
  have hdisc : IsDiscrete (Γ : Set ℂ) := isDiscrete_iff_discreteTopology.2 inferInstance
  have := Metric.finite_isBounded_inter_isClosed hdisc hs (isClosed_lattice Γ)
  simpa [inter_comm] using this

/-- The homogeneous function of degree two whose sublevel sets are the squares. -/
noncomputable def sqNormSq (z : ℂ) : ℝ := (max |z.re| |z.im|) ^ 2

theorem sqNormSq_smul (z : ℂ) {r : ℝ} (hr : 0 ≤ r) : sqNormSq (r • z) = r ^ 2 * sqNormSq z := by
  simp only [sqNormSq, Complex.smul_re, Complex.smul_im, smul_eq_mul, abs_mul, abs_of_nonneg hr]
  rw [← mul_max_of_nonneg _ _ hr]; ring

theorem sqNormSq_le_iff {z : ℂ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : sqNormSq z ≤ (ℓ / 2) ^ 2 ↔ z ∈ cube ℓ := by
  rw [mem_cube_iff, sqNormSq, pow_le_pow_iff_left₀ (le_max_of_le_left (abs_nonneg _))
    (by linarith) (by norm_num), max_le_iff]

/-- **Lattice points in large squares.** -/
theorem tendsto_ncard_inter_cube_div (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hΓ : ZLattice.covolume Γ = 1) :
    Tendsto (fun ℓ : ℝ ↦ (((Γ : Set ℂ) ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) := by
  have h1 : {z : ℂ | z ∈ (univ : Set ℂ) ∧ sqNormSq z ≤ 1} = cube 2 := by
    ext z
    have := sqNormSq_le_iff (z := z) (ℓ := 2) (by norm_num)
    simp only [mem_ofPred_eq, mem_univ, true_and]
    rw [← this]; norm_num
  have hmain := ZLattice.covolume.tendsto_card_le_div' (E := ℂ) Γ (X := univ) (F := sqNormSq)
    (fun x r _ hr => mem_univ _)
    (fun x r hr => by rw [Complex.finrank_real_complex]; exact sqNormSq_smul x hr)
    (by rw [h1]; exact isBounded_cube 2) (by rw [h1]; exact measurableSet_cube 2)
    (by
      rw [h1]
      exact (convex_cube 2).addHaar_frontier volume)
  rw [h1, hΓ] at hmain
  have hvol : volume.real (cube 2) = 4 := by
    rw [measureReal_def, volume_cube, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hvol, div_one] at hmain
  have hlim : Tendsto (fun ℓ : ℝ => ℓ ^ 2 / 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
  have hc := hmain.comp hlim
  have hq := hc.const_mul (1 / 4)
  rw [show (1 / 4 : ℝ) * 4 = 1 by norm_num] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
  have hset : {x : ℂ | x ∈ (univ : Set ℂ) ∧ sqNormSq x ≤ ℓ ^ 2 / 4} = cube ℓ := by
    ext z
    have := sqNormSq_le_iff (z := z) hℓ.le
    simp only [mem_ofPred_eq, mem_univ, true_and]
    rw [← this]; ring_nf
  simp only [Function.comp_apply, hset, Nat.card_coe_set_eq, inter_comm]
  field_simp

/-- The shifted version: `#(Γ ∩ □_{ℓ + c}) / ℓ² → 1`. -/
theorem tendsto_ncard_inter_cube_add_div (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hΓ : ZLattice.covolume Γ = 1) (c : ℝ) :
    Tendsto (fun ℓ : ℝ ↦ (((Γ : Set ℂ) ∩ cube (ℓ + c)).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) := by
  have h1 := (tendsto_ncard_inter_cube_div Γ hΓ).comp (tendsto_atTop_add_const_right atTop c
    tendsto_id)
  have h2 : Tendsto (fun ℓ : ℝ => ((ℓ + c) / ℓ) ^ 2) atTop (𝓝 1) := by
    have : Tendsto (fun ℓ : ℝ => 1 + c / ℓ) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have h3 := this.pow 2
    simp only [add_zero, one_pow] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    field_simp
  have := h1.mul h2
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (-c)] with ℓ hℓ hℓ'
  have : ℓ + c ≠ 0 := by linarith
  simp only [Function.comp_apply, id]
  field_simp

end Torus

end SandierSerfaty

end
