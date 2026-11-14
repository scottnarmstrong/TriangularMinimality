/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Constants
public import SandierSerfaty.Sphere.ChartLaplacian
public import SandierSerfaty.Sphere.Scaling

/-!
# The Laplacian of the blown-up potential (sphere note, Lemma 6.10, hypothesis `Δ H = 2π m`)

* `Lower.laplacian_comp_smul`: `Δ (f (c · )) x = c² (Δ f)(c x)`;
* `Lower.laplacian_blowupPot`: away from the blown-up points `s_n xᵢ`, `Δ H = 2π m` with
  `H = blowupPot X` and `m = blowupDens n`;
* `Lower.contDiff_blowupDens`: `m` is smooth.
-/

open Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- `Δ (f ∘ (c •)) x = c² (Δ f)(c x)`. -/
theorem laplacian_comp_smul (f : ℂ → ℝ) {c : ℝ} (hc : c ≠ 0) (x : ℂ) :
    Δ (fun y => f (c • y)) x = c ^ 2 * Δ f (c • x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun y => f (c • y)) Complex.orthonormalBasisOneI,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]
  let L : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ c hc).toContinuousLinearEquiv
  have h : iteratedFDeriv ℝ 2 (fun y => f (c • y)) x =
      (iteratedFDeriv ℝ 2 f (c • x)).compContinuousLinearMap fun _ => (L : ℂ →L[ℝ] ℂ) := by
    have := L.iteratedFDerivWithin_comp_right f
      uniqueDiffOn_univ (x := x) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at this
    exact this
  simp only [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set b := Complex.orthonormalBasisOneI i
  have : (fun j : Fin 2 => (L : ℂ →L[ℝ] ℂ) (![b, b] j)) = fun j => c • ![b, b] j := by
    funext j; rfl
  rw [this]
  have hm := (iteratedFDeriv ℝ 2 f (c • x)).map_smul_univ (fun _ : Fin 2 => c) ![b, b]
  rw [hm]
  simp [pow_two]

theorem blowupScale_sq {n : ℕ} : blowupScale n ^ 2 = blowupKappa ^ 2 * n := by
  unfold blowupScale
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- `Δ H = 2π m` for `H = blowupPot X` off the blown-up points. -/
theorem laplacian_blowupPot {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {z : ℂ}
    (hz : ∀ i, z ≠ blowupScale n • X i) :
    Δ (blowupPot X) z = 2 * Real.pi * blowupDens n z := by
  have hs := blowupScale_pos hn
  have hsi : ((blowupScale n)⁻¹ : ℝ) ≠ 0 := (inv_pos.2 hs).ne'
  have hz' : ∀ i, ((blowupScale n)⁻¹ : ℝ) • z ≠ X i := by
    intro i h
    apply hz i
    exact (inv_smul_eq_iff₀ hs.ne').1 h
  unfold blowupPot
  rw [laplacian_comp_smul (chartPot X) hsi z, laplacian_chartPot X hz']
  unfold blowupDens dens
  have hk := blowupKappa_pos
  have hp := Real.pi_pos
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [inv_pow, blowupScale_sq]
  field_simp

theorem contDiff_blowupDens (n : ℕ) : ContDiff ℝ ∞ (blowupDens n) := by
  unfold blowupDens lam
  have h1 : ContDiff ℝ ∞ fun z : ℂ => ‖((blowupScale n)⁻¹ : ℝ) • z‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_const_smul _)
  have h2 : ∀ z : ℂ, 1 + ‖((blowupScale n)⁻¹ : ℝ) • z‖ ^ 2 ≠ 0 := fun z => by positivity
  have h3 : ContDiff ℝ ∞ fun z : ℂ => 2 / (1 + ‖((blowupScale n)⁻¹ : ℝ) • z‖ ^ 2) :=
    contDiff_const.div (contDiff_const.add h1) h2
  exact (h3.pow 2).div_const _

end Lower

end Sphere

end SandierSerfaty

end
