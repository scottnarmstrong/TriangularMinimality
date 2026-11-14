/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.LogKernel
public import SandierSerfaty.Sphere.Lower.BlowupLaplacian
public import SandierSerfaty.Sphere.Lower.DensityFreeze

/-!
# The blown-up potential solves `-ΔH = 2π (∑ δ_{s xᵢ} - m)` in the sense of distributions

`Lower.integral_blowupPot_mul_lap`: for every smooth compactly supported `φ`,
`-∫ H Δφ = 2π (∑ᵢ φ(s xᵢ) - ∫ m φ)`, `H = blowupPot X`, `m = blowupDens n`.  With `ΔH = 2π m` off the points
(`Lower.laplacian_blowupPot`) this is the equation `-ΔH = 2π (∑ δ - m)` used for the field `w` of Input 6.3
(sphere note, Proposition 6.13).
-/

open MeasureTheory Set Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem integrable_log_norm_sub_mul_lap {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (p : ℂ) : Integrable (fun x : ℂ => Real.log ‖x - p‖ * Δ φ x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hI : IntegrableOn (fun x : ℂ => Real.log ‖x - p‖ * Δ φ x) (Metric.closedBall 0 R) :=
    (integrableOn_log_norm_sub p).mul_continuousOn (contDiff_lap hφ).continuous.continuousOn
      (isCompact_closedBall _ _)
  refine hI.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  have hx' : x ∉ tsupport φ := fun h => hx (hR h)
  rw [Weyl.lap_eq_zero_of_notMem_tsupport hx', mul_zero]

theorem hasCompactSupport_lap {φ : ℂ → ℝ} (hc : HasCompactSupport φ) :
    HasCompactSupport (fun x => Δ φ x) := by
  refine hc.mono' ?_
  intro x hx
  by_contra hx'
  exact hx (Weyl.lap_eq_zero_of_notMem_tsupport hx')

/-- The Laplacian of `x ↦ V(x / s)` is `4 s⁻² π µ(x/s)`. -/
theorem laplacian_potV_smul {s : ℝ} (hs : s ≠ 0) (x : ℂ) :
    Δ (fun y => potV (s⁻¹ • y)) x = s⁻¹ ^ 2 * (4 * Real.pi * dens (s⁻¹ • x)) := by
  rw [laplacian_comp_smul potV (inv_ne_zero hs) x, laplacian_potV]

theorem blowupPot_eq_of_ne {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {x : ℂ}
    (hx : ∀ i, x ≠ blowupScale n • X i) : blowupPot X x =
      ∑ i, (-Real.log ‖x - blowupScale n • X i‖ + Real.log (blowupScale n)) +
        (n : ℝ) / 2 * potV ((blowupScale n)⁻¹ • x) := by
  have hs := blowupScale_pos hn
  unfold blowupPot chartPot gKer
  have hi : ∀ i, -Real.log ‖(blowupScale n)⁻¹ • x - X i‖ =
      -Real.log ‖x - blowupScale n • X i‖ + Real.log (blowupScale n) := by
    intro i
    have e : (blowupScale n)⁻¹ • x - X i = (blowupScale n)⁻¹ • (x - blowupScale n • X i) := by
      rw [smul_sub, inv_smul_smul₀ hs.ne']
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    have h0 : ‖x - blowupScale n • X i‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (hx i))
    rw [Real.log_mul (inv_pos.2 hs).ne' h0, Real.log_inv]; ring
  rw [Finset.sum_congr rfl fun i _ => hi i]

theorem integrable_blowupPot_mul_lap {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable fun x => blowupPot X x * Δ φ x := by
  have hs := blowupScale_pos hn
  have hlap := contDiff_lap hφ
  have hlc := hasCompactSupport_lap hc
  have hA : ∀ i : Fin n, Integrable fun x : ℂ =>
      -(Real.log ‖x - blowupScale n • X i‖ * Δ φ x) + Real.log (blowupScale n) * Δ φ x :=
    fun i => (integrable_log_norm_sub_mul_lap hφ hc _).neg.add
      ((hlap.continuous.const_mul _).integrable_of_hasCompactSupport hlc.mul_left)
  have hV : Integrable fun x : ℂ => potV ((blowupScale n)⁻¹ • x) * Δ φ x :=
    ((contDiff_potV.comp (contDiff_const_smul _)).continuous.mul hlap.continuous
      ).integrable_of_hasCompactSupport hlc.mul_left
  have hR : Integrable fun x : ℂ => ∑ i, (-(Real.log ‖x - blowupScale n • X i‖ * Δ φ x) +
      Real.log (blowupScale n) * Δ φ x) + (n : ℝ) / 2 * (potV ((blowupScale n)⁻¹ • x) * Δ φ x) :=
    (integrable_finsetSum _ fun i _ => hA i).add (hV.const_mul _)
  refine hR.congr ?_
  filter_upwards [(Set.countable_range fun i => blowupScale n • X i).ae_notMem (volume : Measure ℂ)]
    with x hx
  have hx' : ∀ i, x ≠ blowupScale n • X i := fun i h => hx ⟨i, h.symm⟩
  rw [blowupPot_eq_of_ne hn X hx', add_mul, Finset.sum_mul, mul_assoc]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integral_blowupPot_mul_lap {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    -(∫ x, blowupPot X x * Δ φ x) =
      2 * Real.pi * ((∑ i, φ (blowupScale n • X i)) - ∫ x, blowupDens n x * φ x) := by
  obtain ⟨s, hsdef⟩ : ∃ s, s = blowupScale n := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ blowupScale_pos hn
  have hlap := contDiff_lap hφ
  have hlc := hasCompactSupport_lap hc
  -- decomposition of `H`
  have hpot : ∀ x : ℂ, (∀ i, x ≠ s • X i) → blowupPot X x =
      ∑ i, (-Real.log ‖x - s • X i‖ + Real.log s) + (n : ℝ) / 2 * potV (s⁻¹ • x) := by
    intro x hx
    unfold blowupPot chartPot gKer
    rw [← hsdef]
    have hi : ∀ i, -Real.log ‖s⁻¹ • x - X i‖ = -Real.log ‖x - s • X i‖ + Real.log s := by
      intro i
      have e : s⁻¹ • x - X i = s⁻¹ • (x - s • X i) := by
        rw [smul_sub, inv_smul_smul₀ hs.ne']
      rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      have h0 : ‖x - s • X i‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (hx i))
      rw [Real.log_mul (inv_pos.2 hs).ne' h0, Real.log_inv]; ring
    rw [Finset.sum_congr rfl fun i _ => hi i]
  have hH : ∀ᵐ x : ℂ, blowupPot X x * Δ φ x =
      ∑ i, (-(Real.log ‖x - s • X i‖ * Δ φ x) + Real.log s * Δ φ x) +
        (n : ℝ) / 2 * (potV (s⁻¹ • x) * Δ φ x) := by
    filter_upwards [(Set.countable_range fun i => s • X i).ae_notMem (volume : Measure ℂ)] with x hx
    have hx' : ∀ i, x ≠ s • X i := fun i h => hx ⟨i, h.symm⟩
    rw [hpot x hx', add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae hH]
  have hA : ∀ i : Fin n, Integrable fun x : ℂ => -(Real.log ‖x - s • X i‖ * Δ φ x) :=
    fun i => (integrable_log_norm_sub_mul_lap hφ hc _).neg
  have hB : Integrable fun x : ℂ => Real.log s * Δ φ x :=
    (hlap.continuous.const_mul _).integrable_of_hasCompactSupport hlc.mul_left
  have hi1 : ∀ i : Fin n, Integrable fun x : ℂ => -(Real.log ‖x - s • X i‖ * Δ φ x) + Real.log s * Δ φ x :=
    fun i => (hA i).add hB
  have hV : Integrable fun x : ℂ => potV (s⁻¹ • x) * Δ φ x :=
    ((contDiff_potV.comp (contDiff_const_smul _)).continuous.mul hlap.continuous
      ).integrable_of_hasCompactSupport hlc.mul_left
  rw [integral_add (integrable_finsetSum _ fun i _ => hi1 i) (hV.const_mul _),
    integral_finsetSum _ fun i _ => hi1 i]
  have hterm : ∀ i : Fin n, ∫ x, (-(Real.log ‖x - s • X i‖ * Δ φ x) + Real.log s * Δ φ x) =
      -(2 * Real.pi * φ (s • X i)) := by
    intro i
    rw [integral_add (hA i) hB, integral_neg, integral_log_norm_sub_mul_lap hφ hc,
      integral_const_mul, integral_lap_eq_zero hφ hc]
    ring
  simp only [hterm, integral_const_mul]
  -- the smooth part
  have hVu : ∫ x, potV (s⁻¹ • x) * Δ φ x = ∫ x, Δ (fun y => potV (s⁻¹ • y)) x * φ x := by
    refine Weyl.integral_mul_lap_eq (W := Set.univ) hc.isCompact (Set.subset_univ _) isOpen_univ
      ?_ (hφ.of_le (by norm_cast)) (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    exact ((contDiff_potV.comp (contDiff_const_smul _)).of_le (by norm_cast)).contDiffOn
  rw [hVu]
  have hm : ∀ x : ℂ, (n : ℝ) / 2 * Δ (fun y => potV (s⁻¹ • y)) x = 2 * Real.pi * blowupDens n x := by
    intro x
    rw [laplacian_potV_smul hs.ne']
    unfold blowupDens dens
    have hk := blowupKappa_pos
    have hp := Real.pi_pos
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    subst hsdef
    rw [inv_pow, blowupScale_sq]
    field_simp
    norm_num
  have hrhs : (n : ℝ) / 2 * ∫ x, Δ (fun y => potV (s⁻¹ • y)) x * φ x =
      2 * Real.pi * ∫ x, blowupDens n x * φ x := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, hm x]
    ring
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, hrhs, ← hsdef]
  ring

end Lower

end Sphere

end SandierSerfaty

end
