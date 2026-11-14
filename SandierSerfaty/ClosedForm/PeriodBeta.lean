/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.WeierstrassReal
public import SandierSerfaty.ClosedForm.GammaThird
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The period integral: `B(1/6, 1/2) = 3 √e`

The closed-form note's Proposition C6. With `σ(t) = (e / φ(t))³` on `(0, 1/2)`, `σ` is a strictly increasing
`C¹` bijection onto `(0, 1)` with
`σ'(t) σ(t)^(-5/6) (1 - σ(t))^(-1/2) = 6 √e`. The change of variables
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` gives `B(1/6, 1/2) = 3 √e`
(`betaReal_one_sixth_one_half_eq`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped PeriodPair

public section

namespace SandierSerfaty

namespace ClosedForm

theorem rpow_sq_aux (x : ℝ) (hx : 0 < x) (r : ℝ) : (x ^ 2) ^ r = x ^ (2 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

theorem rpow_cube_aux (x : ℝ) (hx : 0 < x) (r : ℝ) : (x ^ 3) ^ r = x ^ (3 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

theorem key_identity_aux {c w v : ℝ} (hc : 0 < c) (hw : 0 < w) (hv : 0 < v)
    (hvw : v ^ 2 + c ^ 6 = w ^ 6) :
    6 * (c ^ 2) ^ 3 * v / (w ^ 2) ^ 4 *
      ((((c ^ 2) / (w ^ 2)) ^ 3) ^ (1 / 6 - 1 : ℝ) * (1 - ((c ^ 2) / (w ^ 2)) ^ 3) ^ (1 / 2 - 1 : ℝ))
      = 6 * c := by
  have hq : 0 < (c / w) ^ 3 := by positivity
  have e1 : ((c ^ 2) / (w ^ 2)) ^ 3 = ((c / w) ^ 3) ^ 2 := by ring
  have hr : 0 < v / w ^ 3 := by positivity
  have e2 : 1 - ((c / w) ^ 3) ^ 2 = (v / w ^ 3) ^ 2 := by
    field_simp; linarith [hvw]
  rw [e1, e2, rpow_sq_aux _ hq, rpow_sq_aux _ hr, rpow_cube_aux _ (by positivity)]
  have e3 : (3 : ℝ) * (2 * (1 / 6 - 1)) = -5 := by norm_num
  have e4 : (2 : ℝ) * (1 / 2 - 1) = -1 := by norm_num
  rw [e3, e4, Real.rpow_neg (by positivity), Real.rpow_neg hr.le, Real.rpow_one]
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- The pointwise identity of the change of variables, for `0 < e < φ`. -/
theorem key_identity {e φ : ℝ} (he : 0 < e) (hφ : e < φ) :
    6 * e ^ 3 * √(φ ^ 3 - e ^ 3) / φ ^ 4 *
      (((e * φ⁻¹) ^ 3) ^ (1 / 6 - 1 : ℝ) * (1 - (e * φ⁻¹) ^ 3) ^ (1 / 2 - 1 : ℝ)) = 6 * √e := by
  have hφ0 : 0 < φ := he.trans hφ
  have hpos : 0 < φ ^ 3 - e ^ 3 := by
    have : e ^ 3 < φ ^ 3 := pow_lt_pow_left₀ hφ he.le (by norm_num)
    linarith
  obtain ⟨c, hc, rfl⟩ : ∃ c, 0 < c ∧ e = c ^ 2 :=
    ⟨√e, Real.sqrt_pos.2 he, (Real.sq_sqrt he.le).symm⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w, 0 < w ∧ φ = w ^ 2 :=
    ⟨√φ, Real.sqrt_pos.2 hφ0, (Real.sq_sqrt hφ0.le).symm⟩
  have hv : 0 < √((w ^ 2) ^ 3 - (c ^ 2) ^ 3) := Real.sqrt_pos.2 hpos
  have hvw : √((w ^ 2) ^ 3 - (c ^ 2) ^ 3) ^ 2 + c ^ 6 = w ^ 6 := by
    rw [Real.sq_sqrt hpos.le]; ring
  have := key_identity_aux hc hw hv hvw
  rw [Real.sqrt_sq hc.le]
  rw [show (c ^ 2 * (w ^ 2)⁻¹) = c ^ 2 / w ^ 2 by ring]
  exact this

/-- `σ(t) = (e / φ(t))³`. -/
@[expose] noncomputable def sigma (t : ℝ) : ℝ := (hexE * (phi t)⁻¹) ^ 3

/-- The derivative `σ'(t) = 6 e³ √(φ³ - e³) / φ⁴`. -/
@[expose] noncomputable def sigma' (t : ℝ) : ℝ :=
  6 * hexE ^ 3 * √(phi t ^ 3 - hexE ^ 3) / phi t ^ 4

theorem mem_Ioo_one {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) : t ∈ Ioo (0 : ℝ) 1 :=
  ⟨ht.1, by linarith [ht.2]⟩

theorem hasDerivAt_sigma {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    HasDerivAt sigma (sigma' t) t := by
  have h1 : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_one (Ioo_subset_Ioc_self ht)
  have hp := phi_pos h1
  have h := (((hasDerivAt_phi h1).inv hp.ne').const_mul hexE).pow 3
  rw [psi_eq (Ioo_subset_Ioc_self ht)] at h
  refine h.congr_deriv ?_
  unfold sigma'
  have hp' := hp.ne'
  push_cast
  simp only [Pi.inv_apply]
  field_simp
  ring

theorem sigma'_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) : 0 < sigma' t := by
  have h1 : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_one (Ioo_subset_Ioc_self ht)
  have hp := phi_pos h1
  have he := hexE_pos
  have hlt := e_lt_phi ht
  have : hexE ^ 3 < phi t ^ 3 := pow_lt_pow_left₀ hlt he.le (by norm_num)
  unfold sigma'
  have : 0 < √(phi t ^ 3 - hexE ^ 3) := Real.sqrt_pos.2 (by linarith)
  positivity

theorem sigma_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) : sigma t ∈ Ioo (0 : ℝ) 1 := by
  have h1 : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_one (Ioo_subset_Ioc_self ht)
  have hp := phi_pos h1
  have he := hexE_pos
  have hlt := e_lt_phi ht
  have hq : hexE * (phi t)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hp]; exact hlt
  have hq0 : 0 < hexE * (phi t)⁻¹ := by positivity
  exact ⟨by unfold sigma; positivity, by unfold sigma; exact pow_lt_one₀ hq0.le hq (by norm_num)⟩

theorem sigma_half : sigma (1 / 2) = 1 := by
  unfold sigma
  rw [phi_half, mul_inv_cancel₀ hexE_pos.ne']; norm_num

theorem continuousOn_sigma : ContinuousOn sigma (Ioc (0 : ℝ) (1 / 2)) := by
  have hc : ContinuousOn phi (Ioc (0 : ℝ) (1 / 2)) := continuousOn_phi.mono fun t ht => mem_Ioo_one ht
  unfold sigma
  refine ContinuousOn.pow (continuousOn_const.mul (hc.inv₀ fun t ht => (phi_pos (mem_Ioo_one ht)).ne')) 3

theorem strictMonoOn_sigma : StrictMonoOn sigma (Ioc (0 : ℝ) (1 / 2)) := by
  intro a ha b hb hab
  have h := strictAntiOn_phi ha hb hab
  have pa := phi_pos (mem_Ioo_one ha)
  have pb := phi_pos (mem_Ioo_one hb)
  have he := hexE_pos
  unfold sigma
  have : hexE * (phi a)⁻¹ < hexE * (phi b)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    exact div_lt_div_of_pos_left he pb h
  exact pow_lt_pow_left₀ this (by positivity) (by norm_num)

theorem tendsto_sigma : Tendsto sigma (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t => (phi t)⁻¹) (𝓝[>] 0) (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_phi
  have h2 := (h1.const_mul hexE).pow 3
  show Tendsto (fun t => (hexE * (phi t)⁻¹) ^ 3) _ _
  simpa using h2

/-- The image of `(0, 1/2)` under `σ` is `(0, 1)`. -/
theorem image_sigma : sigma '' Ioo (0 : ℝ) (1 / 2) = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact sigma_mem ht
  · intro y hy
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), sigma t < y := (tendsto_order.1 tendsto_sigma).2 y hy.1
    obtain ⟨δ, hδ, hδ2⟩ := (hev.and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
    have hδ' : δ ∈ Ioo (0 : ℝ) (1 / 2) := hδ2
    have hcont : ContinuousOn sigma (Icc δ (1 / 2)) :=
      continuousOn_sigma.mono fun t ht => ⟨hδ'.1.trans_le ht.1, ht.2⟩
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hδ'.2.le hcont ⟨hδ.le, by rw [sigma_half]; exact hy.2.le⟩
    refine ⟨t, ⟨hδ'.1.trans_le ht.1, lt_of_le_of_ne ht.2 ?_⟩, hty⟩
    rintro rfl
    rw [sigma_half] at hty
    exact hy.2.ne hty.symm

/-- The integrand of the change of variables is constant. -/
theorem integrand_const {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    |sigma' t| • (sigma t ^ (1 / 6 - 1 : ℝ) * (1 - sigma t) ^ (1 / 2 - 1 : ℝ)) = 6 * √hexE := by
  rw [abs_of_pos (sigma'_pos ht), smul_eq_mul]
  have := key_identity hexE_pos (e_lt_phi ht)
  unfold sigma sigma'
  exact this

/-- C6: `B(1/6, 1/2) = 3 √e`. -/
theorem betaReal_one_sixth_one_half_eq : betaReal (1 / 6) (1 / 2) = 3 * √hexE := by
  unfold betaReal
  rw [← image_sigma]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (hasDerivAt_sigma ht).hasDerivWithinAt)
    (strictMonoOn_sigma.injOn.mono Ioo_subset_Ioc_self)]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun t ht => integrand_const ht)]
  rw [setIntegral_const, Real.volume_real_Ioo]
  simp
  ring

end ClosedForm

end SandierSerfaty
