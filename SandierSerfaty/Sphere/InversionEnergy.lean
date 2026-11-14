/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.InversionDisc
public import SandierSerfaty.Sphere.PunctureSplit

/-!
# Puncture energy under the inversion (sphere note, Lemma 3.5, inversion case)

For `R > 0`, `E = {‖z‖ > R}`, `D' = B(0, 1/R)` and `ι(x) = 1 / x̄` (a bijection `D' ∖ {0} → E`), let `H`
be admissible on `(E, P)` and `H'` admissible on `(D', ι P)` with `H ∘ ι = H' + c` on `D' ∖ {0}`. Then
`W_E(H) = W_{D'}(H') + π ∑_{p ∈ P} log ‖p‖²`
(`Sphere.punctureEnergy_inv`), i.e. `W_{Ĝ}(H ∘ ι) = W_G(H) - π ∑ log k(p̃)` with `k(p̃) = ‖p̃‖⁻² = ‖p‖²`...
as in Lemma 3.5, here `k(ι p) = ‖ι p‖⁻²`.

*Proof.* The Dirichlet integral over `E ∖ ⋃ B(p, η)` equals that of `H'` over `ι(E ∖ ⋃ B(p, η))`
(`Sphere.integral_gradSq_inv`); the latter set lies between `D' ∖ ⋃ B(ι p, ρ⁺)` and
`D' ∖ ⋃ B(ι p, ρ⁻)`, `ρ^± = η / (‖p‖ (‖p‖ ∓ η))` (`Sphere.ball_sandwich`), and
`ρ^± / η → ‖p‖⁻²`; the multi-radius form of Lemma 2.4 gives the limit.
-/

open MeasureTheory Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Sphere

/-- The pull-back under `ι` of `E ∖ ⋃ B(p, η)`. -/
@[expose] noncomputable def invDomain (R : ℝ) (P : Finset ℂ) (η : ℝ) : Set ℂ :=
  (ball (0 : ℂ) R⁻¹ \ {0}) \ ⋃ p ∈ P, ball (invCenter p η) (invRad p η)

theorem measurableSet_invDomain (R : ℝ) (P : Finset ℂ) (η : ℝ) : MeasurableSet (invDomain R P η) :=
  (measurableSet_ball.diff (measurableSet_singleton _)).diff
    (Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball)

theorem zero_notMem_invDomain (R : ℝ) (P : Finset ℂ) (η : ℝ) : (0 : ℂ) ∉ invDomain R P η :=
  fun h => h.1.2 rfl

theorem image_invDomain {R : ℝ} (hR : 0 < R) {P : Finset ℂ} {η : ℝ} (hη : 0 < η)
    (hηP : ∀ p ∈ P, η < ‖p‖) :
    invC '' invDomain R P η = {z : ℂ | R < ‖z‖} \ ⋃ p ∈ P, ball p η := by
  ext y
  simp only [mem_image, invDomain, Set.mem_sdiff, mem_ball, dist_zero_right, mem_singleton_iff,
    mem_iUnion, exists_prop, not_exists, not_and, mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨⟨hzR, hz0⟩, hz⟩, rfl⟩
    refine ⟨?_, fun p hp hmem => ?_⟩
    · rw [norm_invC]
      exact (lt_inv_comm₀ hR (norm_pos_iff.2 hz0)).2 hzR
    · have hy0 : invC z ≠ 0 := invC_ne_zero hz0
      have := (invC_mem_ball_iff hη (hηP p hp) hy0).2 (mem_ball.2 hmem)
      rw [invC_invC] at this
      exact hz p hp (mem_ball.1 this)
  · rintro ⟨hy, hyP⟩
    have hy0 : y ≠ 0 := by
      intro h; rw [h, norm_zero] at hy; linarith
    refine ⟨invC y, ⟨⟨?_, invC_ne_zero hy0⟩, fun p hp hmem => ?_⟩, invC_invC y⟩
    · rw [norm_invC]
      exact (inv_lt_inv₀ (by linarith) hR).2 hy
    · have := (invC_mem_ball_iff hη (hηP p hp) hy0).1 (mem_ball.2 hmem)
      exact hyP p hp (mem_ball.1 this)

/-- The Dirichlet integral of `H` over `E ∖ ⋃ B(p, η)` equals that of `H'` over its pull-back. -/
theorem integral_gradSq_inv {R : ℝ} (hR : 0 < R) {P : Finset ℂ} {H H' : ℂ → ℝ} {c : ℝ}
    (hH : PunctureAdmissible {z : ℂ | R < ‖z‖} P H)
    (hcomp : ∀ z ∈ ball (0 : ℂ) R⁻¹, z ≠ 0 → z ∉ P.image invC → H (invC z) = H' z + c)
    {η : ℝ} (hη : 0 < η) (hηP : ∀ p ∈ P, η < ‖p‖) :
    ∫ x in {z : ℂ | R < ‖z‖} \ ⋃ p ∈ P, ball p η, ‖gradient H x‖ ^ 2 =
      ∫ z in invDomain R P η, ‖gradient H' z‖ ^ 2 := by
  rw [← image_invDomain hR hη hηP]
  have hdiff : ∀ z ∈ invDomain R P η, DifferentiableAt ℝ H (invC z) := by
    intro z hz
    have hmem : invC z ∈ invC '' invDomain R P η := mem_image_of_mem _ hz
    rw [image_invDomain hR hη hηP] at hmem
    refine (hH.c2 (invC z) hmem.1 fun hP => hmem.2 ?_).differentiableAt (by norm_num)
    exact mem_biUnion hP (mem_ball_self hη)
  rw [integral_gradSq_image_invC (measurableSet_invDomain R P η) (zero_notMem_invDomain R P η) H hdiff]
  refine setIntegral_congr_fun (measurableSet_invDomain R P η) fun z hz => ?_
  have hzP : z ∉ P.image invC := by
    intro hmem
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hmem
    have hp0 : p ≠ 0 := norm_pos_iff.1 (hη.trans (hηP p hp))
    have := (invC_mem_ball_iff hη (hηP p hp) hp0).2 (mem_ball_self hη)
    exact hz.2 (mem_biUnion hp this)
  have hev : (H ∘ invC) =ᶠ[𝓝 z] fun w => H' w + c := by
    have hopen : IsOpen ((ball (0 : ℂ) R⁻¹ \ {0}) \ ((P.image invC : Finset ℂ) : Set ℂ)) :=
      (isOpen_ball.sdiff isClosed_singleton).sdiff (Finset.finite_toSet _).isClosed
    filter_upwards [hopen.mem_nhds ⟨hz.1, hzP⟩] with w hw
    exact hcomp w hw.1.1 hw.1.2 hw.2
  show ‖gradient (H ∘ invC) z‖ ^ 2 = ‖gradient H' z‖ ^ 2
  rw [Torus.norm_gradient_eq, Torus.norm_gradient_eq, hev.fderiv_eq, fderiv_add_const]

theorem PunctureAdmissible.tendsto_truncMulti {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) {ρ : ℝ → ℂ → ℝ} (hρ : RadiiToZero P ρ) :
    Tendsto (fun η => truncMulti G P H (ρ η)) (𝓝[>] 0) (𝓝 (punctureEnergy G P H)) := by
  obtain ⟨W, hW⟩ := hH.exists_tendsto_truncMulti
  have h1 := hW ρ hρ
  have h2 := hH.tendsto_punctureEnergy
  have h3 := hW (fun η _ => η) (fun p _ => tendsto_id)
  have e : punctureTrunc G P H = fun η => truncMulti G P H (fun _ => η) :=
    funext (punctureTrunc_eq_truncMulti G P H)
  rw [e] at h2
  rwa [tendsto_nhds_unique h2 h3]

/-- The outer radii `ρ⁺(q) = η / (‖ι q‖ (‖ι q‖ - η))`. -/
@[expose] noncomputable def invRadPlus (η : ℝ) (q : ℂ) : ℝ := η / (‖invC q‖ * (‖invC q‖ - η))

/-- The inner radii `ρ⁻(q) = η / (‖ι q‖ (‖ι q‖ + η))`. -/
@[expose] noncomputable def invRadMinus (η : ℝ) (q : ℂ) : ℝ := η / (‖invC q‖ * (‖invC q‖ + η))

theorem invRadPlus_invC (η : ℝ) (p : ℂ) : invRadPlus η (invC p) = η / (‖p‖ * (‖p‖ - η)) := by
  simp [invRadPlus, invC_invC]

theorem invRadMinus_invC (η : ℝ) (p : ℂ) : invRadMinus η (invC p) = η / (‖p‖ * (‖p‖ + η)) := by
  simp [invRadMinus, invC_invC]

theorem tendsto_div_gen {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : ContinuousAt g 0) (hg0 : g 0 = a) :
    Tendsto (fun η : ℝ => η / (a * g η)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : ContinuousAt (fun η : ℝ => η / (a * g η)) 0 :=
      continuousAt_id.div (continuousAt_const.mul hg) (by rw [hg0]; positivity)
    have := hc.tendsto
    simp only [zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < g η := hg.eventually (lt_mem_nhds (by rw [hg0]; exact ha))
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h1] with η hη h2
    exact div_pos hη (mul_pos ha h2)

theorem tendsto_log_mul_gen {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    (hg0 : g 0 = a) :
    Tendsto (fun η : ℝ => Real.log (a * g η)) (𝓝[>] 0) (𝓝 (Real.log (a ^ 2))) := by
  have hc : ContinuousAt (fun η : ℝ => Real.log (a * g η)) 0 :=
    ContinuousAt.log (continuousAt_const.mul hg) (by rw [hg0]; positivity)
  have := hc.tendsto
  simp only [hg0] at this
  rw [sq]
  exact this.mono_left nhdsWithin_le_nhds

/-- **Lemma 3.5, inversion case.** `W_E(H) = W_{D'}(H') + π ∑_{p ∈ P} log ‖p‖²` when
`H ∘ ι = H' + c` on `D' ∖ {0}`. -/
theorem punctureEnergy_inv {R : ℝ} (hR : 0 < R) {P : Finset ℂ} (hP : ∀ p ∈ P, R < ‖p‖)
    {H H' : ℂ → ℝ} {c : ℝ} (hH : PunctureAdmissible {z : ℂ | R < ‖z‖} P H)
    (hH' : PunctureAdmissible (ball (0 : ℂ) R⁻¹) (P.image invC) H')
    (hcomp : ∀ z ∈ ball (0 : ℂ) R⁻¹, z ≠ 0 → z ∉ P.image invC → H (invC z) = H' z + c) :
    punctureEnergy {z : ℂ | R < ‖z‖} P H =
      punctureEnergy (ball (0 : ℂ) R⁻¹) (P.image invC) H' +
        Real.pi * ∑ p ∈ P, Real.log (‖p‖ ^ 2) := by
  classical
  set Pt := P.image invC with hPt
  have hp_pos : ∀ p ∈ P, 0 < ‖p‖ := fun p hp => by linarith [hP p hp]
  have hRP : RadiiToZero Pt invRadPlus := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    have := tendsto_div_gen (hp_pos p hp) (g := fun η => ‖p‖ - η) (by fun_prop) (by simp)
    simpa [invRadPlus_invC] using this
  have hRM : RadiiToZero Pt invRadMinus := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    have := tendsto_div_gen (hp_pos p hp) (g := fun η => ‖p‖ + η) (by fun_prop) (by simp)
    simpa [invRadMinus_invC] using this
  have hconvP := hH'.tendsto_truncMulti hRP
  have hconvM := hH'.tendsto_truncMulti hRM
  have hlogP : Tendsto (fun η : ℝ => ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ - η))) (𝓝[>] 0)
      (𝓝 (∑ p ∈ P, Real.log (‖p‖ ^ 2))) :=
    tendsto_finsetSum _ fun p hp =>
      tendsto_log_mul_gen (hp_pos p hp) (g := fun η => ‖p‖ - η) (by fun_prop) (by simp)
  have hlogM : Tendsto (fun η : ℝ => ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ + η))) (𝓝[>] 0)
      (𝓝 (∑ p ∈ P, Real.log (‖p‖ ^ 2))) :=
    tendsto_finsetSum _ fun p hp =>
      tendsto_log_mul_gen (hp_pos p hp) (g := fun η => ‖p‖ + η) (by fun_prop) (by simp)
  have hLo := hconvP.add (hlogP.const_mul Real.pi)
  have hUp := hconvM.add (hlogM.const_mul Real.pi)
  have hbd : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      truncMulti (ball (0 : ℂ) R⁻¹) Pt H' (invRadPlus η) +
          Real.pi * ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ - η)) ≤
        punctureTrunc {z : ℂ | R < ‖z‖} P H η ∧
      punctureTrunc {z : ℂ | R < ‖z‖} P H η ≤
        truncMulti (ball (0 : ℂ) R⁻¹) Pt H' (invRadMinus η) +
          Real.pi * ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ + η)) := by
    have h0 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := eventually_mem_nhdsWithin
    filter_upwards [h0, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with η hη hηR
    have hηR : η < R := hηR
    have hηP : ∀ p ∈ P, η < ‖p‖ := fun p hp => hηR.trans (hP p hp)
    have hposP : ∀ q ∈ Pt, 0 < invRadPlus η q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      rw [invRadPlus_invC]
      have := hηP p hp
      have := hp_pos p hp
      exact div_pos hη (mul_pos this (by linarith))
    have hposM : ∀ q ∈ Pt, 0 < invRadMinus η q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      rw [invRadMinus_invC]
      have := hp_pos p hp
      exact div_pos hη (mul_pos this (by linarith))
    have hinjG : Function.Injective invC := fun a b h => by
      have := congrArg invC h
      rwa [invC_invC, invC_invC] at this
    set E : Set ℂ := {z : ℂ | R < ‖z‖} with hE
    set D' : Set ℂ := ball (0 : ℂ) R⁻¹ with hD'
    have hJ := integral_gradSq_inv hR hH hcomp hη hηP
    set J := ∫ z in invDomain R P η, ‖gradient H' z‖ ^ 2 with hJdef
    set Dp : Set ℂ := D' \ ⋃ q ∈ Pt, ball q (invRadPlus η q) with hDp
    set Dm : Set ℂ := D' \ ⋃ q ∈ Pt, ball q (invRadMinus η q) with hDm
    have hintM : IntegrableOn (fun x => ‖gradient H' x‖ ^ 2) Dm :=
      hH'.integrableOn_gradSq_multi hposM
    have hnn : ∀ x, 0 ≤ ‖gradient H' x‖ ^ 2 := fun x => by positivity
    have hsubM : invDomain R P η ⊆ Dm := by
      intro z hz
      refine ⟨hz.1.1, fun hmem => ?_⟩
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hmem
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      rw [invRadMinus_invC] at hzq
      have hs := (ball_sandwich (norm_pos_iff.1 (hp_pos p hp)) hη (hηP p hp)).1 hzq
      exact hz.2 (mem_biUnion hp hs)
    have hsubP : Dp \ {0} ⊆ invDomain R P η := by
      intro z ⟨hzDp, hz0⟩
      refine ⟨⟨hzDp.1, hz0⟩, fun hmem => hzDp.2 ?_⟩
      obtain ⟨p, hp, hzc⟩ := mem_iUnion₂.1 hmem
      have hs := (ball_sandwich (norm_pos_iff.1 (hp_pos p hp)) hη (hηP p hp)).2 hzc
      refine mem_biUnion (Finset.mem_image_of_mem invC hp) ?_
      rw [invRadPlus_invC]
      exact hs
    have hJm : J ≤ ∫ x in Dm, ‖gradient H' x‖ ^ 2 :=
      setIntegral_mono_set hintM (ae_of_all _ hnn) hsubM.eventuallyLE
    have hintInv : IntegrableOn (fun x => ‖gradient H' x‖ ^ 2) (invDomain R P η) :=
      hintM.mono_set hsubM
    have hJp : ∫ x in Dp, ‖gradient H' x‖ ^ 2 ≤ J := by
      refine setIntegral_mono_set hintInv (ae_of_all _ hnn) ?_
      filter_upwards [(Set.countable_singleton (0 : ℂ)).ae_notMem volume] with x hx hxDp
      exact hsubP ⟨hxDp, hx⟩
    have hcardPt : (Pt.card : ℝ) = P.card := by rw [hPt, Finset.card_image_of_injective _ hinjG]
    have hsumP : ∑ q ∈ Pt, Real.log (invRadPlus η q) =
        ∑ p ∈ P, Real.log (η / (‖p‖ * (‖p‖ - η))) := by
      rw [hPt, Finset.sum_image (fun a _ b _ h => hinjG h)]
      exact Finset.sum_congr rfl fun p _ => by rw [invRadPlus_invC]
    have hsumM : ∑ q ∈ Pt, Real.log (invRadMinus η q) =
        ∑ p ∈ P, Real.log (η / (‖p‖ * (‖p‖ + η))) := by
      rw [hPt, Finset.sum_image (fun a _ b _ h => hinjG h)]
      exact Finset.sum_congr rfl fun p _ => by rw [invRadMinus_invC]
    have htermP : ∀ p ∈ P, Real.log (η / (‖p‖ * (‖p‖ - η))) + Real.log (‖p‖ * (‖p‖ - η)) =
        Real.log η := fun p hp => by
      have hx : 0 < ‖p‖ * (‖p‖ - η) := mul_pos (hp_pos p hp) (by linarith [hηP p hp])
      rw [Real.log_div hη.ne' hx.ne']; ring
    have htermM : ∀ p ∈ P, Real.log (η / (‖p‖ * (‖p‖ + η))) + Real.log (‖p‖ * (‖p‖ + η)) =
        Real.log η := fun p hp => by
      have hx : 0 < ‖p‖ * (‖p‖ + η) := mul_pos (hp_pos p hp) (by linarith [hp_pos p hp])
      rw [Real.log_div hη.ne' hx.ne']; ring
    have hcard : ∑ _p ∈ P, Real.log η = P.card * Real.log η := by simp [Finset.sum_const]
    have hLoEq : truncMulti D' Pt H' (invRadPlus η) +
        Real.pi * ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ - η)) =
        (1 / 2 : ℝ) * (∫ x in Dp, ‖gradient H' x‖ ^ 2) + Real.pi * P.card * Real.log η := by
      unfold truncMulti
      rw [hsumP]
      have : Real.pi * ∑ p ∈ P, Real.log (η / (‖p‖ * (‖p‖ - η))) +
          Real.pi * ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ - η)) = Real.pi * P.card * Real.log η := by
        rw [← mul_add, ← Finset.sum_add_distrib, Finset.sum_congr rfl htermP, hcard]; ring
      linarith
    have hUpEq : truncMulti D' Pt H' (invRadMinus η) +
        Real.pi * ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ + η)) =
        (1 / 2 : ℝ) * (∫ x in Dm, ‖gradient H' x‖ ^ 2) + Real.pi * P.card * Real.log η := by
      unfold truncMulti
      rw [hsumM]
      have : Real.pi * ∑ p ∈ P, Real.log (η / (‖p‖ * (‖p‖ + η))) +
          Real.pi * ∑ p ∈ P, Real.log (‖p‖ * (‖p‖ + η)) = Real.pi * P.card * Real.log η := by
        rw [← mul_add, ← Finset.sum_add_distrib, Finset.sum_congr rfl htermM, hcard]; ring
      linarith
    have hTrunc : punctureTrunc E P H η = (1 / 2 : ℝ) * J + Real.pi * P.card * Real.log η := by
      unfold punctureTrunc
      rw [hJ]
    constructor
    · rw [hLoEq, hTrunc]; linarith
    · rw [hUpEq, hTrunc]; linarith
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hUp (hbd.mono fun η h => h.1)
    (hbd.mono fun η h => h.2)
  exact tendsto_nhds_unique hH.tendsto_punctureEnergy hlim

end Sphere

end SandierSerfaty

end
