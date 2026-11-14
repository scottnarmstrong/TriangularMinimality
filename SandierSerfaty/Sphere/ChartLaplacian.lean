/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.ChartPotential
public import SandierSerfaty.Sphere.Density
public import SandierSerfaty.Torus.PotentialLocal
public import SandierSerfaty.Analysis.WeylCalculus

/-!
# The Laplacian of the chart potential (sphere note, Definition 3.3)

`Δ h_X = 2π n µ` off the points `xᵢ` (that is, `-Δ h_X = 2π(∑ δ_{xᵢ} - n µ)` on `ℂ`, the delta masses
being encoded by the local form `h_X = s - log |· - xᵢ|`), and `h_X` is smooth off `{xᵢ}`.

* `Sphere.laplacian_potV`: `Δ V = 4 / (1 + |x|²)² = 4π µ`;
* `Sphere.contDiffAt_chartPot`, `Sphere.laplacian_chartPot`.
-/

open Laplacian Filter Topology InnerProductSpace
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem contDiff_potV : ContDiff ℝ ∞ potV := by
  unfold potV
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).log (fun x => by positivity)

theorem pd_potV (v y : ℂ) :
    Weyl.pd v potV y = 2 * inner ℝ v y / (1 + ‖y‖ ^ 2) := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ y) y := by
    simpa using ((hasFDerivAt_id y).norm_sq).const_add 1
  have h2 := h1.log (by positivity)
  unfold Weyl.pd potV
  rw [h2.fderiv]
  simp [two_smul, div_eq_inv_mul, real_inner_comm]
  ring

theorem pd_pd_potV (v x : ℂ) :
    Weyl.pd v (Weyl.pd v potV) x =
      2 * inner ℝ v v / (1 + ‖x‖ ^ 2) - 4 * inner ℝ v x ^ 2 / (1 + ‖x‖ ^ 2) ^ 2 := by
  have hw : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  have e : Weyl.pd v potV = fun y => 2 * inner ℝ v y * (1 + ‖y‖ ^ 2)⁻¹ := by
    funext y; rw [pd_potV, div_eq_mul_inv]
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using ((hasFDerivAt_id x).norm_sq).const_add 1
  have h2 : HasFDerivAt (fun z : ℂ => 2 * inner ℝ v z) (2 • innerSL ℝ v) x := by
    have := ((innerSL ℝ v).hasFDerivAt (x := x)).const_mul (2 : ℝ)
    simpa [two_smul] using this
  have h3 : HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹)
      ((-((1 + ‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)) x := by
    have := (hasDerivAt_inv hw).comp_hasFDerivAt x h1
    simpa [Function.comp_def, smul_smul] using this
  have h4 : HasFDerivAt (fun z : ℂ => 2 * inner ℝ v z * (1 + ‖z‖ ^ 2)⁻¹) _ x := h2.mul h3
  unfold Weyl.pd at e ⊢
  rw [e, h4.fderiv]
  simp [two_smul, real_inner_comm]
  field_simp
  ring

theorem laplacian_potV (x : ℂ) : Δ potV x = 4 * Real.pi * dens x := by
  have hpi := Real.pi_pos
  have hc : ContDiffAt ℝ 2 potV x := (contDiff_potV.of_le (by norm_cast)).contDiffAt
  rw [Weyl.lap_eq_pd hc, pd_pd_potV, pd_pd_potV, dens_eq]
  have h1 : inner ℝ (1 : ℂ) 1 = 1 := by simp
  have h2 : inner ℝ Complex.I Complex.I = 1 := by simp
  have h3 : inner ℝ (1 : ℂ) x = x.re := by simp [Complex.inner]
  have h4 : inner ℝ Complex.I x = x.im := by simp [Complex.inner]
  have h5 : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hw : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  rw [h1, h2, h3, h4]
  rw [h5] at hw ⊢
  field_simp
  ring

theorem contDiffAt_gKer_sub {p x : ℂ} (hx : x ≠ p) :
    ContDiffAt ℝ ∞ (fun y => gKer (y - p)) x := by
  unfold gKer
  have h : x - p ≠ 0 := sub_ne_zero.2 hx
  have h1 : ContDiffAt ℝ ∞ (fun y : ℂ => ‖y - p‖) x :=
    (contDiffAt_norm ℝ h).comp x (contDiffAt_id.sub contDiffAt_const)
  exact (h1.log (norm_ne_zero_iff.2 h)).neg

theorem laplacian_gKer_sub {p x : ℂ} (hx : x ≠ p) : Δ (fun y => gKer (y - p)) x = 0 := by
  have e : (fun y : ℂ => gKer (y - p)) = (-1 : ℝ) • fun y : ℂ => Real.log ‖y - p‖ := by
    funext y; simp [gKer]
  have hc : ContDiffAt ℝ 2 (fun y : ℂ => Real.log ‖y - p‖) x := by
    have h : x - p ≠ 0 := sub_ne_zero.2 hx
    have h1 : ContDiffAt ℝ 2 (fun y : ℂ => ‖y - p‖) x :=
      ((contDiffAt_norm ℝ h).comp x (contDiffAt_id.sub contDiffAt_const)).of_le (by norm_cast)
    exact h1.log (norm_ne_zero_iff.2 h)
  rw [e, laplacian_smul (-1 : ℝ) hc, Torus.laplacian_log_norm_sub hx]
  simp

theorem laplacian_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℝ} {x : ℂ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    Δ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact congrFun (laplacian_const (E := ℂ) (c := (0 : ℝ))) x
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (f a) x := hf a (Finset.mem_insert_self a s)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ i ∈ s, f i y) x :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have e : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y := by
      funext y; rw [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    have := h1.laplacian_add h2
    rw [show (fun y => f a y + ∑ i ∈ s, f i y) = f a + fun y => ∑ i ∈ s, f i y from rfl, this,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `h_X` is smooth away from the points `xᵢ`. -/
theorem contDiffAt_chartPot {n : ℕ} (X : Fin n → ℂ) {x : ℂ} (hx : ∀ i, x ≠ X i) :
    ContDiffAt ℝ ∞ (chartPot X) x := by
  unfold chartPot
  exact (ContDiffAt.sum fun i _ => contDiffAt_gKer_sub (hx i)).add
    (contDiffAt_const.mul contDiff_potV.contDiffAt)

/-- `Δ h_X = 2π n µ` away from the points `xᵢ`. -/
theorem laplacian_chartPot {n : ℕ} (X : Fin n → ℂ) {x : ℂ} (hx : ∀ i, x ≠ X i) :
    Δ (chartPot X) x = 2 * Real.pi * n * dens x := by
  have h2 : ∀ i ∈ Finset.univ, ContDiffAt ℝ 2 (fun y => gKer (y - X i)) x := fun i _ =>
    (contDiffAt_gKer_sub (hx i)).of_le (by norm_cast)
  have hV : ContDiffAt ℝ 2 potV x := (contDiff_potV.of_le (by norm_cast)).contDiffAt
  have e : chartPot X = (fun y => ∑ i, gKer (y - X i)) + fun y => ((n : ℝ) / 2) • potV y := by
    funext y; simp [chartPot]
  have hs : ContDiffAt ℝ 2 (fun y => ∑ i, gKer (y - X i)) x := ContDiffAt.sum h2
  have hV' : ContDiffAt ℝ 2 (fun y => ((n : ℝ) / 2) • potV y) x := hV.const_smul _
  have hsm : Δ (fun y => ((n : ℝ) / 2) • potV y) x = ((n : ℝ) / 2) • Δ potV x :=
    laplacian_smul ((n : ℝ) / 2) hV
  rw [e, hs.laplacian_add hV', hsm, laplacian_potV]
  have : Δ (fun y => ∑ i, gKer (y - X i)) x = 0 := by
    rw [laplacian_finset_sum Finset.univ h2]
    exact Finset.sum_eq_zero fun i _ => laplacian_gKer_sub (hx i)
  rw [this]
  simp only [smul_eq_mul]
  ring

end Sphere

end SandierSerfaty

end
