/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.WeierstrassDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# `℘` on the real interval `(0, 1)`

The closed-form note's Lemma C5. Let `φ(t) = Re ℘(t)`, `ψ(t) = Re ℘'(t)`. For `t ∈ (0, 1)`:

* `hasDerivAt_phi`, `hasDerivAt_psi`: `φ' = ψ` and `ψ' = 6 φ²`;
* `psi_sq`: `ψ² = 4 (φ³ - e³)`, hence `e ≤ φ` (`e_le_phi`);
* `psi_neg`: `ψ < 0` on `(0, 1/2)`; `strictAntiOn_phi`: `φ` is strictly decreasing on `(0, 1/2]`;
* `psi_eq`: `ψ = -2 √(φ³ - e³)` on `(0, 1/2]`;
* `tendsto_phi`: `φ(t) → +∞` as `t ↓ 0`.
-/

open Complex Filter Topology Set
open scoped PeriodPair

public section

namespace SandierSerfaty

namespace ClosedForm

/-- `φ(t) = Re ℘(t)`. -/
@[expose] noncomputable def phi (t : ℝ) : ℝ := (℘[hexPair] (t : ℂ)).re

/-- `ψ(t) = Re ℘'(t)`. -/
@[expose] noncomputable def psi (t : ℝ) : ℝ := (℘'[hexPair] (t : ℂ)).re

theorem wp_ofReal (t : ℝ) : ℘[hexPair] (t : ℂ) = (phi t : ℂ) := by
  obtain ⟨r, hr⟩ := weierstrassP_real t
  simp [phi, hr]

theorem dwp_ofReal (t : ℝ) : ℘'[hexPair] (t : ℂ) = (psi t : ℂ) := by
  obtain ⟨r, hr⟩ := derivWeierstrassP_real t
  simp [psi, hr]

theorem ofReal_mem_hexU {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : (t : ℂ) ∈ hexU := by
  intro h
  obtain ⟨m, n, hmn⟩ := mem_hexPair_lattice.1 h
  have him := congrArg Complex.im hmn
  have hre := congrArg Complex.re hmn
  simp [rho_im, rho_re] at him hre
  subst him
  have hn : (n : ℝ) = t := by simpa using hre
  have h1 : (0 : ℝ) < n := by rw [hn]; exact ht.1
  have h2 : (n : ℝ) < 1 := by rw [hn]; exact ht.2
  have h1' : (0 : ℤ) < n := by exact_mod_cast h1
  have h2' : n < 1 := by exact_mod_cast h2
  omega

theorem hasDerivAt_phi {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt phi (psi t) t := by
  have h := (hasDerivAt_wp (ofReal_mem_hexU ht)).real_of_complex
  rw [dwp_ofReal, Complex.ofReal_re] at h
  exact h

theorem hasDerivAt_psi {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt psi (6 * phi t ^ 2) t := by
  have h := (hasDerivAt_dwp (ofReal_mem_hexU ht)).real_of_complex
  rw [deriv_dwp_eq (ofReal_mem_hexU ht), wp_ofReal] at h
  have e : (6 * (phi t : ℂ) ^ 2).re = 6 * phi t ^ 2 := by
    rw [show (6 * (phi t : ℂ) ^ 2) = ((6 * phi t ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [e] at h
  exact h

theorem psi_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : psi t ^ 2 = 4 * (phi t ^ 3 - hexE ^ 3) := by
  have h := dwp_sq (ofReal_mem_hexU ht)
  rw [dwp_ofReal, wp_ofReal, hexPair_g₃_eq] at h
  have h' : psi t ^ 2 = 4 * phi t ^ 3 - hexG3 := by exact_mod_cast h
  rw [h', ← four_mul_hexE_cube_real]; ring

theorem e_le_phi {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : hexE ≤ phi t := by
  have h := psi_sq ht
  have h0 : hexE ^ 3 ≤ phi t ^ 3 := by nlinarith [sq_nonneg (psi t)]
  have he := hexE_pos
  have hp : 0 ≤ phi t := by
    by_contra hneg
    have : phi t ^ 3 < 0 := Odd.pow_neg (by decide) (not_le.1 hneg)
    have : 0 < hexE ^ 3 := by positivity
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hp h0

theorem phi_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < phi t :=
  lt_of_lt_of_le hexE_pos (e_le_phi ht)

theorem half_mem : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num

theorem psi_half : psi (1 / 2) = 0 := by
  have := derivWeierstrassP_half
  have h : ℘'[hexPair] (((1 / 2 : ℝ)) : ℂ) = 0 := by push_cast; exact this
  rw [dwp_ofReal] at h
  exact_mod_cast h

theorem phi_half : phi (1 / 2) = hexE := by
  have h : ℘[hexPair] (((1 / 2 : ℝ)) : ℂ) = (hexE : ℂ) := by push_cast; exact weierstrassP_half
  rw [wp_ofReal] at h
  exact_mod_cast h

theorem continuousOn_psi : ContinuousOn psi (Ioo (0 : ℝ) 1) :=
  fun _ ht => (hasDerivAt_psi ht).continuousAt.continuousWithinAt

theorem continuousOn_phi : ContinuousOn phi (Ioo (0 : ℝ) 1) :=
  fun _ ht => (hasDerivAt_phi ht).continuousAt.continuousWithinAt

theorem strictMonoOn_psi : StrictMonoOn psi (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) continuousOn_psi
  intro t ht
  rw [interior_Ioo] at ht
  rw [(hasDerivAt_psi ht).deriv]
  have := phi_pos ht
  positivity

theorem psi_neg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) : psi t < 0 := by
  have h1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have := strictMonoOn_psi h1 half_mem ht.2
  rwa [psi_half] at this

theorem strictAntiOn_phi : StrictAntiOn phi (Ioc (0 : ℝ) (1 / 2)) := by
  have hsub : Ioc (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2))
    (continuousOn_phi.mono hsub)
  intro t ht
  rw [interior_Ioc] at ht
  rw [(hasDerivAt_phi (hsub (Ioo_subset_Ioc_self ht))).deriv]
  exact psi_neg ht

theorem e_lt_phi {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) : hexE < phi t := by
  have := strictAntiOn_phi (Ioo_subset_Ioc_self ht) ⟨by norm_num, le_refl _⟩ ht.2
  rwa [phi_half] at this

theorem psi_eq {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) :
    psi t = -2 * √(phi t ^ 3 - hexE ^ 3) := by
  have h1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hsq := psi_sq h1
  have hnonneg : 0 ≤ phi t ^ 3 - hexE ^ 3 := by nlinarith [sq_nonneg (psi t)]
  have hle : psi t ≤ 0 := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, psi_half]
    · exact (psi_neg ⟨ht.1, h⟩).le
  have : √(phi t ^ 3 - hexE ^ 3) = -psi t / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq hnonneg (by linarith)]
    nlinarith
  rw [this]; ring

/-- C5(e): `φ(t) → +∞` as `t ↓ 0`. -/
theorem tendsto_phi : Tendsto phi (𝓝[>] 0) atTop := by
  set z0 : hexPair.lattice := ⟨0, zero_mem _⟩
  have hcont : ContinuousAt ℘[hexPair - (0 : ℂ)] 0 :=
    (hexPair.analyticAt_weierstrassPExcept 0).continuousAt
  have hdef : ∀ z : ℂ, ℘[hexPair - (0 : ℂ)] z = ℘[hexPair] z + (1 / 0 ^ 2 - 1 / (z - 0) ^ 2) := by
    intro z
    exact hexPair.weierstrassPExcept_def z0 z
  have hre : Tendsto (fun t : ℝ => (℘[hexPair - (0 : ℂ)] (t : ℂ)).re) (𝓝[>] 0)
      (𝓝 ((℘[hexPair - (0 : ℂ)] 0).re)) := by
    have h1 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
      simpa using Complex.continuous_ofReal.tendsto 0
    exact ((Complex.continuous_re.tendsto _).comp (hcont.tendsto.comp h1)).mono_left
      nhdsWithin_le_nhds
  have hinv : Tendsto (fun t : ℝ => 1 / t ^ 2) (𝓝[>] 0) atTop := by
    simpa [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).atTop_mul_atTop₀ tendsto_inv_nhdsGT_zero
      |>.congr (fun t => by ring)
  have : ∀ t : ℝ, phi t = (℘[hexPair - (0 : ℂ)] (t : ℂ)).re + 1 / t ^ 2 := by
    intro t
    have h := hdef t
    have h2 : ℘[hexPair] (t : ℂ) = ℘[hexPair - (0 : ℂ)] (t : ℂ) + 1 / (t : ℂ) ^ 2 := by
      rw [h]; simp
    simp only [phi, h2, Complex.add_re]
    congr 1
    rw [show (1 / (t : ℂ) ^ 2) = ((1 / t ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  exact (hinv.atTop_add hre).congr (fun t => by rw [this t]; ring)

end ClosedForm

end SandierSerfaty
