/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectLimit
public import SandierSerfaty.Sphere.Lower.Statements

/-!
# Reflection and the square-torus bound (sphere note, Lemma 6.2)

For `Q = a₀ + [0, t]²`, a density `m > 0` with `n̄ = m t² ∈ ℕ`, `n̄ ≥ 1`, and `n̄` pairwise distinct points
`Y ⊂ Q°` (`σ = √m`):

* (i) `Lower.torusPotential_reflX`, `Lower.torusPotential_reflY`: the torus potential of the reflected
  configuration is invariant under the reflections across the lines through the corner `σ a₀`
  (the reflections across the other sides differ from these by lattice translations);
* (iii) `Lower.neumannEnergy_eq`:
  `W^Neu_Q(Y; m) = 𝒲_Γ(Ỹ) / 4 - (π/2) n̄ log m`, where `𝒲_Γ(Ỹ) = torusEnergy` of the `4 n̄` reflected
  scaled points on `squareLattice (4 n̄)`; in particular the truncated energies converge;
* (iv) `Lower.neumannEnergy_ge` (under `Assembly.TorusBoundStatement`): `W^Neu_Q(Y; m) ≥ n̄ (W_tri - (π/2) log m)`.

Part (ii) of the sphere note lemma (smoothness, the equation `-Δ u_Y = 2π(∑ δ_y - m)` and the Neumann boundary
condition) is not used by the lower bound and is not formalized here.
-/

open MeasureTheory Filter Topology Set
open scoped Pointwise

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

open Torus

section Setup

variable {nb : ℕ} (a₀ : ℂ) (t m : ℝ) (Y : Fin nb → ℂ)

theorem sqrt_mul_sq_eq {m t : ℝ} (hm : 0 ≤ m) (ht : 0 ≤ t) : √(m * t ^ 2) = √m * t := by
  rw [Real.sqrt_mul hm, Real.sqrt_sq ht]

theorem smul_sub_re (σ : ℝ) (y a : ℂ) : (σ • y - σ • a).re = σ * (y - a).re := by
  simp [mul_sub]

theorem smul_sub_im (σ : ℝ) (y a : ℂ) : (σ • y - σ • a).im = σ * (y - a).im := by
  simp [mul_sub]

variable {a₀ t m Y}

theorem scaled_mem_openSq (hm : 0 < m) (_ht : 0 < t) (hY : ∀ i, Y i ∈ interior (sqAt a₀ t))
    (i : Fin nb) :
    0 < ((√m • Y i : ℂ) - √m • a₀).re ∧ ((√m • Y i : ℂ) - √m • a₀).re < √m * t ∧
      0 < ((√m • Y i : ℂ) - √m • a₀).im ∧ ((√m • Y i : ℂ) - √m • a₀).im < √m * t := by
  have hσ : 0 < √m := Real.sqrt_pos.2 hm
  have := hY i
  rw [interior_sqAt] at this
  simp only [openSq, mem_ofPred_eq] at this
  rw [smul_sub_re, smul_sub_im, Complex.sub_re, Complex.sub_im]
  refine ⟨by nlinarith [this.1], by nlinarith [this.2.1], by nlinarith [this.2.2.1],
    by nlinarith [this.2.2.2]⟩

end Setup

section Energy

variable {nb : ℕ} {a₀ : ℂ} {t m : ℝ} {Y : Fin nb → ℂ}

/-- The data of Definition 6.1 in the form needed for the energy identity. -/
theorem neumannEnergy_eq (hnb : 1 ≤ nb) (hm : 0 < m) (ht : 0 < t) (hnbt : (nb : ℝ) = m * t ^ 2)
    (hYi : Function.Injective Y) (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) :
    neumannEnergy a₀ t m Y =
      torusEnergy (squareLattice (4 * nb)) (reflectPts (√m • a₀) (fun i => √m • Y i)) / 4 -
        Real.pi / 2 * nb * Real.log m := by
  have hσ : 0 < √m := Real.sqrt_pos.2 hm
  have hs : √(nb : ℝ) = √m * t := by rw [hnbt]; exact sqrt_mul_sq_eq hm.le ht.le
  have hZ : ∀ i, 0 < ((fun i => √m • Y i) i - √m • a₀).re ∧
      ((fun i => √m • Y i) i - √m • a₀).re < √nb ∧
      0 < ((fun i => √m • Y i) i - √m • a₀).im ∧ ((fun i => √m • Y i) i - √m • a₀).im < √nb := by
    intro i
    rw [hs]
    exact scaled_mem_openSq hm ht hY i
  have hZi : Function.Injective (fun i => √m • Y i) := fun i j h =>
    hYi (smul_right_injective ℂ hσ.ne' h)
  have hT := tendsto_punctureTrunc_reflected hnb (√m • a₀) (fun i => √m • Y i) hZi hZ
  rw [hs] at hT
  have hσ' : 0 < (√m)⁻¹ := inv_pos.2 hσ
  have hT' := tendsto_punctureTrunc_smul hσ' hT
  have hG : (√m)⁻¹ • openSq (√m • a₀) (√m * t) = interior (sqAt a₀ t) := by
    ext x
    rw [interior_sqAt, Set.mem_smul_set_iff_inv_smul_mem₀ hσ'.ne', inv_inv]
    simp only [openSq, mem_ofPred_eq, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have hP : (Finset.univ.image (fun i => √m • Y i)).image (fun p => (√m)⁻¹ • p) =
      Finset.univ.image Y := by
    rw [Finset.image_image]
    refine Finset.image_congr fun i _ => ?_
    exact inv_smul_smul₀ hσ.ne' (Y i)
  rw [hG, hP] at hT'
  have hcard : (Finset.univ.image (fun i => √m • Y i)).card = nb := by
    rw [Finset.card_image_of_injective _ hZi]; simp
  rw [hcard, inv_inv] at hT'
  unfold neumannEnergy punctureEnergy neumannPot
  rw [hT'.limUnder_eq, Real.log_inv, Real.log_sqrt hm.le]
  ring

/-- **Lemma 6.2(iv)** (conditional on the square-torus bound). -/
theorem neumannEnergy_ge (hR1 : Assembly.TorusBoundStatement) (hnb : 1 ≤ nb) (hm : 0 < m) (ht : 0 < t)
    (hnbt : (nb : ℝ) = m * t ^ 2) (hYi : Function.Injective Y)
    (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) :
    nb * (triangularEnergy - Real.pi / 2 * Real.log m) ≤ neumannEnergy a₀ t m Y := by
  have hσ : 0 < √m := Real.sqrt_pos.2 hm
  have hs : √(nb : ℝ) = √m * t := by rw [hnbt]; exact sqrt_mul_sq_eq hm.le ht.le
  have hZ : ∀ i, 0 < ((fun i => √m • Y i) i - √m • a₀).re ∧
      ((fun i => √m • Y i) i - √m • a₀).re < √nb ∧
      0 < ((fun i => √m • Y i) i - √m • a₀).im ∧ ((fun i => √m • Y i) i - √m • a₀).im < √nb := by
    intro i
    rw [hs]
    exact scaled_mem_openSq hm ht hY i
  have hZi : Function.Injective (fun i => √m • Y i) := fun i j h =>
    hYi (smul_right_injective ℂ hσ.ne' h)
  have h1 := hR1 (4 * nb) (by omega) (reflectPts (√m • a₀) (fun i => √m • Y i))
    (fun i j hij => reflectPts_distinct hnb _ _ hZi hZ i j hij)
  rw [neumannEnergy_eq hnb hm ht hnbt hYi hY]
  push_cast at h1
  nlinarith [h1]

end Energy

end Lower

end Sphere

end SandierSerfaty

end
