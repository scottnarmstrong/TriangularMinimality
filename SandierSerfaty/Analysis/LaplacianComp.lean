/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The Laplacian on the plane: translations, linear forms, finite sums

Elementary computations with `Δ` on `ℂ` (with its Euclidean structure):

* `SandierSerfaty.Analysis.laplacian_comp_sub`: `Δ (f ∘ (· - a)) x = Δ f (x - a)`;
* `SandierSerfaty.Analysis.laplacian_comp_clm`: for a real linear form `L : ℂ →L[ℝ] ℝ` and `P : ℝ → ℝ` of class
  `C²`, `Δ (P ∘ L) x = P''(L x) (L 1² + L i²)`;
* `SandierSerfaty.Analysis.laplacian_finset_sum`: the Laplacian of a finite sum of `C²` functions.
-/

open Filter Topology Laplacian

public section

namespace SandierSerfaty

namespace Analysis

/-- Translation invariance of the Laplacian on `ℂ`. -/
theorem laplacian_comp_sub (f : ℂ → ℝ) (a x : ℂ) :
    Δ (fun z => f (z - a)) x = Δ f (x - a) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_comp_sub]

/-- The second derivative of a real function in a diagonal direction. -/
theorem iteratedFDeriv_two_diag (P : ℝ → ℝ) (t u : ℝ) :
    iteratedFDeriv ℝ 2 P t ![u, u] = u * u * iteratedDeriv 2 P t := by
  have h : (![u, u] : Fin 2 → ℝ) = fun i => u • (fun _ : Fin 2 => (1 : ℝ)) i := by
    ext i; fin_cases i <;> simp
  rw [h, ContinuousMultilinearMap.map_smul_univ]
  simp only [iteratedDeriv_eq_iteratedFDeriv, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- The Laplacian of `P ∘ L` for a real linear form `L` on `ℂ`. -/
theorem laplacian_comp_clm (L : ℂ →L[ℝ] ℝ) (P : ℝ → ℝ) (hP : ContDiff ℝ 2 P) (x : ℂ) :
    Δ (P ∘ L) x = iteratedDeriv 2 P (L x) * (L 1 ^ 2 + L Complex.I ^ 2) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [L.iteratedFDeriv_comp_right hP x le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h1 : (fun i : Fin 2 => L (![1, 1] i)) = ![L 1, L 1] := by
    ext i; fin_cases i <;> simp
  have h2 : (fun i : Fin 2 => L (![Complex.I, Complex.I] i)) = ![L Complex.I, L Complex.I] := by
    ext i; fin_cases i <;> simp
  rw [h1, h2, iteratedFDeriv_two_diag, iteratedFDeriv_two_diag]
  ring

/-- The Laplacian of a finite sum of `C²` functions is the sum of the Laplacians. -/
theorem laplacian_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℝ) (x : ℂ)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    Δ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have h1 : ContDiffAt ℝ 2 (f j) x := hf j (Finset.mem_insert_self j s)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ i ∈ s, f i y) x :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have e : (fun y => ∑ i ∈ insert j s, f i y) = f j + fun y => ∑ i ∈ s, f i y := by
      funext y; simp [Finset.sum_insert hj]
    rw [e, ContDiffAt.laplacian_add h1 h2, ih fun i hi => hf i (Finset.mem_insert_of_mem hi),
      Finset.sum_insert hj]

end Analysis

end SandierSerfaty

end
