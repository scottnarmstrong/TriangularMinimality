/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Splitting
public import SandierSerfaty.Torus.PotentialLocal

/-!
# Scaling of the puncture energy (sphere note, Lemma 3.5, scaling case) and the blown-up identity

* `Sphere.punctureTrunc_smul`: for `σ > 0`, the truncated energy of `H(· / σ)` on `σ G` with punctures
  `σ P` at scale `η` is the truncated energy of `H` on `G` at scale `η / σ`, plus `π |P| log σ`;
* `Sphere.punctureEnergy_smul`: `W_{σG}(H(· / σ)) = W_G(H) + π |P| log σ` whenever `W_G(H)` is a limit
  (the "in particular" of Lemma 3.5);
* `Sphere.blowupScale` (Definition 3.6): `sₙ = κ √n`.
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis
open scoped ContDiff Pointwise

public section

namespace SandierSerfaty

namespace Sphere

theorem norm_gradient_comp_smul (H : ℂ → ℝ) {σ : ℝ} (hσ : 0 < σ) (x : ℂ) :
    ‖gradient (fun z => H ((σ⁻¹ : ℝ) • z)) x‖ = σ⁻¹ * ‖gradient H ((σ⁻¹ : ℝ) • x)‖ := by
  rw [Torus.norm_gradient_eq, Torus.norm_gradient_eq, fderiv_comp_smul (f := H) (σ⁻¹ : ℝ),
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ)]

theorem smul_diff_iUnion_ball {σ : ℝ} (hσ : 0 < σ) (G : Set ℂ) (P : Finset ℂ) (η : ℝ) :
    σ • (G \ ⋃ p ∈ P, Metric.ball p (η / σ)) =
      σ • G \ ⋃ q ∈ P.image (fun p => σ • p), Metric.ball q η := by
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hσ.ne', Set.mem_sdiff, Set.mem_sdiff,
    mem_smul_set_iff_inv_smul_mem₀ hσ.ne']
  simp only [mem_iUnion, Metric.mem_ball, dist_eq_norm, Finset.mem_image, exists_prop,
    not_exists, not_and]
  constructor
  · rintro ⟨hG, hn⟩
    refine ⟨hG, ?_⟩
    rintro q ⟨p, hp, rfl⟩
    have h := hn p hp
    have e : σ⁻¹ • x - p = σ⁻¹ • (x - σ • p) := by
      rw [smul_sub, inv_smul_smul₀ hσ.ne']
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ)] at h
    rw [not_lt]
    by_contra hlt
    rw [not_le] at hlt
    exact h (by rw [div_eq_inv_mul]; exact mul_lt_mul_of_pos_left hlt (inv_pos.2 hσ))
  · rintro ⟨hG, hn⟩
    refine ⟨hG, fun p hp h => ?_⟩
    have e : σ⁻¹ • x - p = σ⁻¹ • (x - σ • p) := by
      rw [smul_sub, inv_smul_smul₀ hσ.ne']
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hσ), div_eq_inv_mul] at h
    exact hn (σ • p) ⟨p, hp, rfl⟩ (by
      have := lt_of_mul_lt_mul_left h (inv_pos.2 hσ).le
      exact this)

/-- Scaling of the truncated energy (Lemma 3.5, scaling case). -/
theorem punctureTrunc_smul {σ : ℝ} (hσ : 0 < σ) (G : Set ℂ) (P : Finset ℂ) (H : ℂ → ℝ) {η : ℝ}
    (hη : η ≠ 0) :
    punctureTrunc (σ • G) (P.image (fun p => σ • p)) (fun z => H ((σ⁻¹ : ℝ) • z)) η =
      punctureTrunc G P H (η / σ) + Real.pi * P.card * Real.log σ := by
  have hcard : (P.image (fun p => σ • p)).card = P.card :=
    Finset.card_image_of_injective _ (smul_right_injective ℂ hσ.ne')
  unfold punctureTrunc
  rw [hcard, ← smul_diff_iUnion_ball hσ G P η]
  have hint : ∫ x in σ • (G \ ⋃ p ∈ P, Metric.ball p (η / σ)),
        ‖gradient (fun z => H ((σ⁻¹ : ℝ) • z)) x‖ ^ 2 =
      ∫ x in G \ ⋃ p ∈ P, Metric.ball p (η / σ), ‖gradient H x‖ ^ 2 := by
    have h := Measure.setIntegral_comp_smul_of_pos (μ := volume)
      (fun x => ‖gradient (fun z => H ((σ⁻¹ : ℝ) • z)) x‖ ^ 2) (G \ ⋃ p ∈ P, Metric.ball p (η / σ))
      hσ
    have hf : ∀ y : ℂ, ‖gradient (fun z => H ((σ⁻¹ : ℝ) • z)) (σ • y)‖ ^ 2 =
        (σ ^ 2)⁻¹ * ‖gradient H y‖ ^ 2 := by
      intro y
      rw [norm_gradient_comp_smul H hσ, inv_smul_smul₀ hσ.ne', mul_pow, inv_pow]
    simp only [hf, Complex.finrank_real_complex, smul_eq_mul] at h
    rw [integral_const_mul] at h
    have hs : (σ ^ 2) ≠ 0 := by positivity
    have : (∫ x in σ • (G \ ⋃ p ∈ P, Metric.ball p (η / σ)),
        ‖gradient (fun z => H ((σ⁻¹ : ℝ) • z)) x‖ ^ 2) =
        σ ^ 2 * ((σ ^ 2)⁻¹ * ∫ y in G \ ⋃ p ∈ P, Metric.ball p (η / σ), ‖gradient H y‖ ^ 2) := by
      rw [h]; field_simp
    rw [this]; field_simp
  rw [hint, Real.log_div hη hσ.ne']
  ring

theorem tendsto_div_nhdsGT {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun η : ℝ => η / σ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun η : ℝ => η / σ) (𝓝 0) (𝓝 (0 / σ)) :=
      (continuous_id.div_const σ).tendsto 0
    rw [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with η hη using div_pos hη hσ

/-- **Lemma 3.5, scaling case.** If the truncated energies of `H` on `(G, P)` converge to `W`,
those of `H(· / σ)` on `(σ G, σ P)` converge to `W + π |P| log σ`. -/
theorem tendsto_punctureTrunc_smul {σ : ℝ} (hσ : 0 < σ) {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    {W : ℝ} (h : Tendsto (punctureTrunc G P H) (𝓝[>] 0) (𝓝 W)) :
    Tendsto (punctureTrunc (σ • G) (P.image (fun p => σ • p)) (fun z => H ((σ⁻¹ : ℝ) • z)))
      (𝓝[>] 0) (𝓝 (W + Real.pi * P.card * Real.log σ)) := by
  have h1 := (h.comp (tendsto_div_nhdsGT hσ)).add_const (Real.pi * P.card * Real.log σ)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact (punctureTrunc_smul hσ G P H hη.ne').symm

/-- **Lemma 3.5, scaling case** ("in particular"): `W_{σG}(H(· / σ)) = W_G(H) + π |P| log σ`
whenever `W_G(H)` is a limit. -/
theorem punctureEnergy_smul {σ : ℝ} (hσ : 0 < σ) {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ} {W : ℝ}
    (h : Tendsto (punctureTrunc G P H) (𝓝[>] 0) (𝓝 W)) :
    punctureEnergy (σ • G) (P.image (fun p => σ • p)) (fun z => H ((σ⁻¹ : ℝ) • z)) =
      punctureEnergy G P H + Real.pi * P.card * Real.log σ := by
  rw [punctureEnergy, punctureEnergy, h.limUnder_eq, (tendsto_punctureTrunc_smul hσ h).limUnder_eq]

/-- The separation constant `c_sep = √(log 2 / 10)` (Definition 3.6). -/
@[expose] noncomputable def cSep : ℝ := Real.sqrt (Real.log 2 / 10)

/-- The blow-up constant `κ = 2 / c_sep`. -/
@[expose] noncomputable def blowupKappa : ℝ := 2 / cSep

/-- The blow-up scale `s_n = κ √n`. -/
@[expose] noncomputable def blowupScale (n : ℕ) : ℝ := blowupKappa * Real.sqrt n

theorem cSep_pos : 0 < cSep := Real.sqrt_pos.2 (by have := Real.log_pos (one_lt_two (α := ℝ)); positivity)

theorem blowupKappa_pos : 0 < blowupKappa := div_pos two_pos cSep_pos

theorem blowupScale_pos {n : ℕ} (hn : 0 < n) : 0 < blowupScale n :=
  mul_pos blowupKappa_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))

theorem log_blowupScale {n : ℕ} (hn : 0 < n) :
    Real.log (blowupScale n) = Real.log blowupKappa + Real.log n / 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold blowupScale
  rw [Real.log_mul blowupKappa_pos.ne' (Real.sqrt_pos.2 hn').ne', Real.log_sqrt hn'.le]

/-- The blown-up potential `H(z) = h_X(z / s_n)`. -/
@[expose] noncomputable def blowupPot {n : ℕ} (X : Fin n → ℂ) (z : ℂ) : ℝ :=
  chartPot X (((blowupScale n)⁻¹ : ℝ) • z)

end Sphere

end SandierSerfaty

end
