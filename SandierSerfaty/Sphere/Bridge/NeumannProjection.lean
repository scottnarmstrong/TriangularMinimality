/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.ReflectGlue
public import SandierSerfaty.Screening.TorusProjection

/-!
# Neumann projection with reflection (screening note, Lemma 7.1)

**Lemma 7.1** (`Bridge.neumannEnergy_le_locEnergy`). Let `Q = a₀ + [0, t]²`, `m > 0` with `n̄ = m t² ∈ ℕ`,
`n̄ ≥ 1`, `Y` pairwise distinct points of `Q°` with radii `ρ` such that `B̄(y, ρ_y) ⊂ Q°` and
`ρ_y + ρ_{y'} ≤ |y - y'|`, and `E'` a Neumann charge field on `Q` with density `m` and charges `Y`. Then
`W^Neu_Q(Y; m) ≤ G_Q(ρ)[E']` (`locEnergy m Y ρ E' Q`).

**Proof.** With `σ = √m`, the glued reflected field `Ê` (`Bridge.gluedField`) is a Neumann charge field
of density `1` on `Q̂ = sq (σ a₀) √(4 n̄)` with the `4 n̄` reflected charges, and
`G_{Q̂}(ρ̂)[Ê] = 4 G_Q(ρ)[E'] + 4 n̄ π log σ` (`τ₁(σ r) = τ_m(r) + π log σ`). The projection I5
(`torusEnergy_le_locEnergy`) and Lemma 6.2(iii) (`Lower.neumannEnergy_eq`) give
`4 W^Neu_Q(Y; m) + 2π n̄ log m = torusEnergy ≤ 4 G_Q(ρ)[E'] + 2π n̄ log m`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Real

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open Lower Screening Torus

theorem finsum_range_inter_eq {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) {D : Set ℂ}
    (haD : ∀ i, a i ∈ D) (g : ℂ → ℝ) : ∑ᶠ p ∈ range a ∩ D, g p = ∑ i, g (a i) := by
  rw [inter_eq_left.2 (range_subset_iff.2 haD), finsum_range_eq, sum_image_eq ha]

theorem tauM_mul_sqrt {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    tauM 1 (√m * r) = tauM m r + π / 2 * Real.log m := by
  unfold tauM
  rw [Real.log_mul (Real.sqrt_pos.2 hm).ne' hr.ne', Real.log_sqrt hm.le, mul_pow,
    Real.sq_sqrt hm.le]
  ring

variable {nb : ℕ} {a₀ : ℂ} {t m : ℝ} {Y : Fin nb → ℂ} {ρ : ℂ → ℝ}

/-- **The screening note's Lemma 7.1** (Neumann projection with reflection): `W^Neu_Q(Y; m) ≤ G_Q(ρ)[E']`. -/
theorem neumannEnergy_le_locEnergy (hnb : 1 ≤ nb) (hm : 0 < m) (ht : 0 < t)
    (hnbt : (nb : ℝ) = m * t ^ 2) (hYi : Function.Injective Y)
    (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) (hρ : ∀ i, 0 < ρ (Y i))
    (hball : ∀ i, closedBall (Y i) (ρ (Y i)) ⊆ interior (sqAt a₀ t))
    (hdisj : ∀ i j, i ≠ j → ρ (Y i) + ρ (Y j) ≤ ‖Y i - Y j‖) {E : ℂ → ℂ}
    (hE : IsNeumannChargeField (sqAt a₀ t) m (Finset.univ.image Y) E) :
    ((neumannEnergy a₀ t m Y : ℝ) : EReal) ≤ locEnergy m (range Y) ρ E (sqAt a₀ t) := by
  set σ := √m with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hm
  have hσ2 : σ ^ 2 = m := Real.sq_sqrt hm.le
  have hs : √(nb : ℝ) = σ * t := by rw [hnbt]; exact sqrt_mul_sq_eq hm.le ht.le
  have hN : √((4 * nb : ℕ) : ℝ) = 2 * (σ * t) := by rw [sqrt_four_mul, hs]
  set a := reflectPts (σ • a₀) (fun i => σ • Y i) with ha_def
  set Qh := sq (σ • a₀) √((4 * nb : ℕ) : ℝ) with hQh
  have hQh' : Qh = sq (σ • a₀) (2 * (σ * t)) := by rw [hQh, hN]
  -- the reflected charges
  have hZ : ∀ i, 0 < ((fun i => σ • Y i) i - σ • a₀).re ∧ ((fun i => σ • Y i) i - σ • a₀).re < √nb ∧
      0 < ((fun i => σ • Y i) i - σ • a₀).im ∧ ((fun i => σ • Y i) i - σ • a₀).im < √nb := by
    intro i; rw [hs]; exact scaled_mem_openSq hm ht hY i
  have hZi : Function.Injective (fun i => σ • Y i) := fun i j h =>
    hYi (smul_right_injective ℂ hσ.ne' h)
  have ha : Function.Injective a := fun k l h =>
    reflectPts_distinct hnb _ _ hZi hZ k l (by
      rw [show reflectPts (σ • a₀) (fun i => σ • Y i) k = reflectPts (σ • a₀) (fun i => σ • Y i) l
        from h, sub_self]
      exact Submodule.zero_mem _)
  have hk : ∀ k : Fin (4 * nb), ∃ e i, a k = quadMap σ a₀ e (Y i) := fun k =>
    ⟨(finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2, by
      rw [ha_def, ← reflectPts_eq_quadMap Y, Prod.mk.eta, Equiv.apply_symm_apply]⟩
  have hρa : ∀ e i, gluedRadius σ a₀ ρ (quadMap σ a₀ e (Y i)) = σ * ρ (Y i) := fun e i =>
    gluedRadius_quadMap hσ ρ e (interior_subset (hY i))
  have hballq : ∀ e i, closedBall (quadMap σ a₀ e (Y i)) (σ * ρ (Y i)) ⊆
      quadOpen (σ • a₀) (σ * t) e := by
    intro e i x hx
    obtain ⟨z, rfl⟩ := quadMap_surjective (a₀ := a₀) hσ e x
    rw [mem_closedBall, dist_eq_norm, norm_quadMap_sub hσ, mul_le_mul_iff_right₀ hσ] at hx
    exact (quadMap_mem_quadOpen_iff hσ e z).2 (hball i (mem_closedBall.2 (by rwa [dist_eq_norm])))
  -- the projection I5
  have hI5 := torusEnergy_le_locEnergy (N := 4 * nb) (by omega) (σ • a₀) a ha
    (fun k => by
      obtain ⟨e, i, hki⟩ := hk k
      rw [hki, ← hQh, hQh']
      exact quadOpen_subset_interior_sq _ _ e ((quadMap_mem_quadOpen_iff hσ e _).2 (hY i)))
    (gluedRadius σ a₀ ρ)
    (fun k => by
      obtain ⟨e, i, hki⟩ := hk k
      rw [hki, hρa]; exact mul_pos hσ (hρ i))
    (fun k => by
      obtain ⟨e, i, hki⟩ := hk k
      rw [hki, hρa, ← hQh, hQh']
      exact (hballq e i).trans (quadOpen_subset_interior_sq _ _ e))
    (fun k l hkl => by
      obtain ⟨e, i, hki⟩ := hk k
      obtain ⟨e', j, hlj⟩ := hk l
      rw [hki, hlj, hρa, hρa]
      by_cases hee : e = e'
      · subst hee
        have hij : i ≠ j := fun h => hkl (ha (by rw [hki, hlj, h]))
        rw [norm_quadMap_sub hσ, ← mul_add]
        exact mul_le_mul_of_nonneg_left (hdisj i j hij) hσ.le
      · have hd : Disjoint (closedBall (quadMap σ a₀ e (Y i)) (σ * ρ (Y i)))
            (closedBall (quadMap σ a₀ e' (Y j)) (σ * ρ (Y j))) :=
          (pairwise_disjoint_quadOpen _ _ hee).mono (hballq e i) (hballq e' j)
        rw [disjoint_closedBall_closedBall_iff (mul_pos hσ (hρ i)).le
          (mul_pos hσ (hρ j)).le, dist_eq_norm] at hd
        exact hd.le)
    (E' := gluedField σ a₀ t E) (by
      rw [← hQh, hQh']
      exact isNeumannChargeField_gluedField hσ hY (by rwa [hσ2]))
  -- the energy identity
  have hint := lintegral_truncField_gluedField (σ := σ) (a₀ := a₀) (t := t) hσ hYi hY hρ hball E
  rw [← hQh'] at hint
  have hτ : ∑ᶠ p ∈ range a ∩ Qh, tauM 1 (gluedRadius σ a₀ ρ p) =
      4 * ∑ i, tauM m (ρ (Y i)) + 4 * nb * (π / 2 * Real.log m) := by
    rw [finsum_range_inter_eq ha (fun k => ?_)]
    · have hτi : ∀ i, tauM 1 (σ * ρ (Y i)) = tauM m (ρ (Y i)) + π / 2 * Real.log m :=
        fun i => tauM_mul_sqrt hm (hρ i)
      rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
      simp only [ha_def, reflectPts_eq_quadMap Y, hρa, hτi,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    · obtain ⟨e, i, hki⟩ := hk k
      rw [hki, hQh']
      exact quadClosed_subset_sq _ _ e
        (quadOpen_subset_quadClosed _ _ _ ((quadMap_mem_quadOpen_iff hσ e _).2 (hY i)))
  have hτY : ∑ᶠ p ∈ range Y ∩ sqAt a₀ t, tauM m (ρ p) = ∑ i, tauM m (ρ (Y i)) :=
    finsum_range_inter_eq hYi (fun i => interior_subset (hY i)) _
  -- Lemma 6.2(iii)
  have hW := neumannEnergy_eq hnb hm ht hnbt hYi hY
  rw [← hσdef, ← ha_def] at hW
  by_cases hX : ∫⁻ y in sqAt a₀ t, ENNReal.ofReal (‖truncField (range Y) ρ E y‖ ^ 2) = ⊤
  · rw [locEnergy_eq_top hX]; exact le_top
  rw [locEnergy_eq_coe hX, hτY, EReal.coe_le_coe_iff, hW]
  have hX4 : ∫⁻ x in Qh, ENNReal.ofReal (‖truncField (range a) (gluedRadius σ a₀ ρ)
      (gluedField σ a₀ t E) x‖ ^ 2) ≠ ⊤ := by
    rw [hint]; exact ENNReal.mul_ne_top (by norm_num) hX
  rw [locEnergy_eq_coe hX4, hτ, hint, ENNReal.toReal_mul, EReal.coe_le_coe_iff] at hI5
  rw [ENNReal.toReal_ofNat] at hI5
  linarith

end Bridge

end Sphere

end SandierSerfaty

end
