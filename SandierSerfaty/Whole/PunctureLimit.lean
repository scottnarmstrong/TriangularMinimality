/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.Regularity
public import SandierSerfaty.Sphere.PunctureLimit
public import SandierSerfaty.Statements.Whole.Defs.PunctureFunctional

/-!
# The puncture limit exists (comparison note, Lemma `lem:punct-limit`)

**Theorem** (`Whole.exists_tendsto_punctureFunctional`). For `E ∈ 𝒜₁` and `ξ ∈ C_c^∞(ℂ)` the truncated
functionals `P_η(ξ) = ½ ∫_{Ω_η} ξ |E|² + π log η ∑_{p ∈ Λ} ξ(p)` converge, as `η ↓ 0`, to a real number.

## Proof

Take `R ≥ 1` with `supp ξ ⊆ B(0, R)`, the local form `E = ∑_{q ∈ S} κ(· - q) + F` on `B(0, R + 1)`
(`IsAdmissibleField.exists_local_form`, `S = Λ ∩ B̄(0, R + 1)`), and `ρ ≤ ½` with the discs `B(p, ρ)`,
`p ∈ S`, pairwise `2ρ`-separated. For `0 < η < ρ`,
```
∫_{Ω_η} ξ |E|² = ∫ f_η + ∑_{p ∈ S} ξ(p) · 2π log(ρ/η),
f_η = 1_{Ω_η} ξ |E|² - ∑_{p ∈ S} ξ(p) 1_{B(p,ρ) ∖ B(p,η)} |· - p|⁻²,
```
so `P_η(ξ) = ½ ∫ f_η + π log ρ ∑_{p ∈ S} ξ(p)`. Near `p`, `E = κ(· - p) + G_p` with `G_p` bounded, so
`|ξ |E|² - ξ(p) |· - p|⁻²| ≤ (L + 2 ‖ξ‖_∞ M)/|· - p| + ‖ξ‖_∞ M²` (`L` a Lipschitz constant of `ξ`); away
from the discs `E` is bounded on `supp ξ`. Dominated convergence gives `∫ f_η → ∫ f₀`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Whole

/-- The punctured plane `Ω_η = ℂ ∖ ⋃_{p ∈ Λ} B(p, η)`. -/
@[expose] def punctured (Λ : Set ℂ) (η : ℝ) : Set ℂ := (⋃ p ∈ Λ, ball p η)ᶜ

theorem isClosed_punctured (Λ : Set ℂ) (η : ℝ) : IsClosed (punctured Λ η) :=
  (isOpen_biUnion fun _ _ => isOpen_ball).isClosed_compl

theorem measurableSet_punctured (Λ : Set ℂ) (η : ℝ) : MeasurableSet (punctured Λ η) :=
  (isClosed_punctured Λ η).measurableSet

theorem mem_punctured {Λ : Set ℂ} {η : ℝ} {x : ℂ} : x ∈ punctured Λ η ↔ ∀ p ∈ Λ, η ≤ ‖x - p‖ := by
  simp [punctured, dist_eq_norm]

/-- `P_η(ξ)` is the real number `½ ∫_{Ω_η} ξ |E|² + π log η ∑ ξ(p)` when `ξ |E|²` is integrable on `Ω_η`. -/
theorem punctureFunctional_eq_coe {Λ : Set ℂ} {E : ℂ → ℂ} {ξ : ℂ → ℝ} {η : ℝ}
    (h : IntegrableOn (fun x => ξ x * ‖E x‖ ^ 2) (punctured Λ η)) :
    punctureFunctional Λ E ξ η = (((1 / 2 : ℝ) * (∫ x in punctured Λ η, ξ x * ‖E x‖ ^ 2) +
      Real.pi * Real.log η * ∑ᶠ p ∈ Λ, ξ p : ℝ) : EReal) := by
  have h1 : (∫⁻ x in punctured Λ η, ENNReal.ofReal (ξ x * ‖E x‖ ^ 2)) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt h.2).ne
  have h2 : (∫⁻ x in punctured Λ η, ENNReal.ofReal (-(ξ x * ‖E x‖ ^ 2))) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt h.neg.2).ne
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h]
  unfold punctureFunctional
  simp only [punctured] at h1 h2 ⊢
  rw [← EReal.coe_ennreal_toReal h1, ← EReal.coe_ennreal_toReal h2]
  norm_cast

/-- Finitely many points have a positive separation. -/
theorem exists_sep (S : Finset ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 2 * ρ ≤ ‖p - q‖ := by
  classical
  by_cases hTe : ((S.offDiag).image (fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖)).Nonempty
  · have hm : 0 < ((S.offDiag).image (fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖)).min' hTe := by
      obtain ⟨pq, hpq, he⟩ := Finset.mem_image.1
        (((S.offDiag).image (fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖)).min'_mem hTe)
      rw [← he]
      exact norm_pos_iff.2 (sub_ne_zero.2 (Finset.mem_offDiag.1 hpq).2.2)
    refine ⟨min (((S.offDiag).image (fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖)).min' hTe / 2) (1 / 2),
      by positivity, min_le_right _ _, fun p hp q hq hpq => ?_⟩
    have h1 : ((S.offDiag).image (fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖)).min' hTe ≤ ‖p - q‖ :=
      Finset.min'_le _ _ (Finset.mem_image.2 ⟨(p, q), Finset.mem_offDiag.2 ⟨hp, hq, hpq⟩, rfl⟩)
    have h2 := min_le_left (((S.offDiag).image (fun pq : ℂ × ℂ => ‖pq.1 - pq.2‖)).min' hTe / 2)
      (1 / 2)
    linarith
  · refine ⟨1 / 2, by norm_num, le_rfl, fun p hp q hq hpq => ?_⟩
    exact absurd ⟨_, Finset.mem_image.2 ⟨(p, q), Finset.mem_offDiag.2 ⟨hp, hq, hpq⟩, rfl⟩⟩ hTe

/-- A `C¹` compactly supported function is Lipschitz. -/
theorem exists_lipschitz_bound {ξ : ℂ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hc : HasCompactSupport ξ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℂ, |ξ x - ξ y| ≤ L * ‖x - y‖ := by
  obtain ⟨B, hB⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hξ.continuous_fderiv (by norm_num))
  refine ⟨max B 0, le_max_right _ _, fun x y => ?_⟩
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := ξ) (C := max B 0)
    (fun z _ => hξ.differentiable (by norm_num) z) (fun z _ => (hB z).trans (le_max_left _ _))
    (mem_univ y) (mem_univ x)
  rwa [Real.norm_eq_abs] at this

theorem abs_norm_add_sq_sub_le {k G : ℂ} {M : ℝ} (hG : ‖G‖ ≤ M) :
    |‖k + G‖ ^ 2 - ‖k‖ ^ 2| ≤ 2 * M * ‖k‖ + M ^ 2 := by
  have h := norm_add_sq_real k G
  have hi := abs_le.1 (abs_real_inner_le_norm k G)
  have hkG : ‖k‖ * ‖G‖ ≤ ‖k‖ * M := mul_le_mul_of_nonneg_left hG (norm_nonneg _)
  have hG2 : ‖G‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
  rw [h, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖G‖]

theorem norm_sum_kernel_le {T : Finset ℂ} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ q ∈ T, ρ ≤ ‖x - q‖) : ‖∑ q ∈ T, kernel (x - q)‖ ≤ T.card * ρ⁻¹ := by
  refine (norm_sum_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul T (fun q => ‖kernel (x - q)‖) ρ⁻¹ fun q hq => by
    rw [norm_kernel]; exact inv_anti₀ hρ (h q hq)
  rwa [nsmul_eq_mul] at this

theorem abs_indicator_le_abs {s : Set ℂ} {f : ℂ → ℝ} (x : ℂ) : |s.indicator f x| ≤ |f x| := by
  by_cases hx : x ∈ s <;> simp [hx]

theorem measurable_annulus_term (p : ℂ) (a b : ℝ) :
    Measurable ((ball p b \ ball p a).indicator fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) :=
  (((measurable_norm.comp (measurable_id.sub_const p)).pow_const 2).inv).indicator
    (measurableSet_ball.diff measurableSet_ball)

theorem integrable_annulus_term (p : ℂ) {a b : ℝ} (ha : 0 < a) :
    Integrable ((ball p b \ ball p a).indicator fun y : ℂ => (‖y - p‖ ^ 2)⁻¹) := by
  rw [integrable_indicator_iff (measurableSet_ball.diff measurableSet_ball)]
  refine Measure.integrableOn_of_bounded (M := (a ^ 2)⁻¹)
    (ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset))
    (((measurable_norm.comp (measurable_id.sub_const p)).pow_const 2).inv).aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_ball.diff measurableSet_ball)]
  refine Eventually.of_forall fun y hy => ?_
  have hy' : a ≤ ‖y - p‖ := by
    have := hy.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hy' 2)

/-- **The puncture limit exists** (comparison note, Lemma `lem:punct-limit`). -/
theorem exists_tendsto_punctureFunctional {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E)
    {ξ : ℂ → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    ∃ w : ℝ, Tendsto (punctureFunctional Λ E ξ) (𝓝[>] 0) (𝓝 (w : EReal)) := by
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by simp)
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_ball (0 : ℂ)
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR : tsupport ξ ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  have hξ0 : ∀ x : ℂ, R ≤ ‖x‖ → ξ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR h; rw [mem_ball_zero_iff] at this; linarith
  have hξR : ∀ x : ℂ, ξ x ≠ 0 → ‖x‖ < R := fun x hx => not_le.1 fun h => hx (hξ0 x h)
  obtain ⟨F, hF, hloc⟩ := IsAdmissibleField.exists_local_form hE (R + 1)
  set S := (hE.1 (R + 1)).toFinset with hS
  have hSΛ : ∀ q ∈ S, q ∈ Λ := fun q hq => ((Set.Finite.mem_toFinset _).1 hq).1
  have hfar : ∀ q ∈ Λ, q ∉ S → R + 1 < ‖q‖ := fun q hq hqS => by
    by_contra h
    exact hqS ((Set.Finite.mem_toFinset _).2 ⟨hq, mem_closedBall_zero_iff.2 (not_lt.1 h)⟩)
  obtain ⟨ρ, hρ, hρ2, hdisj⟩ := exists_sep S
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_bound hξ1 hc
  obtain ⟨Xi, hXi⟩ := hc.exists_bound_of_continuous hξ.continuous
  have hXi' : ∀ x, |ξ x| ≤ Xi := fun x => by simpa [Real.norm_eq_abs] using hXi x
  have hXi0 : 0 ≤ Xi := (abs_nonneg _).trans (hXi' 0)
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hF.continuousOn.mono (closedBall_subset_ball (by linarith)))
  set M : ℝ := MF + S.card * ρ⁻¹ with hMdef
  have hM0 : 0 ≤ M := add_nonneg ((norm_nonneg _).trans (hMF 0 (by simp; linarith)))
    (by positivity)
  -- bounds on the field
  have hEbd : ∀ x : ℂ, ‖x‖ ≤ R → (∀ q ∈ S, ρ ≤ ‖x - q‖) →
      ‖∑ q ∈ S, kernel (x - q) + F x‖ ≤ M := fun x hx hq =>
    (norm_add_le _ _).trans (by
      have := norm_sum_kernel_le hρ hq
      have := hMF x (mem_closedBall_zero_iff.2 hx)
      rw [hMdef]; linarith)
  have hGbd : ∀ x : ℂ, ∀ p ∈ S, ‖x‖ ≤ R → x ∈ ball p ρ →
      ‖∑ q ∈ S.erase p, kernel (x - q) + F x‖ ≤ M := by
    intro x p hp hx hxp
    have hq : ∀ q ∈ S.erase p, ρ ≤ ‖x - q‖ := by
      intro q hq
      obtain ⟨hqp, hqS⟩ := Finset.mem_erase.1 hq
      have h1 := hdisj p hp q hqS (Ne.symm hqp)
      have h2 : ‖x - p‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hxp
      have h3 : ‖p - q‖ ≤ ‖x - q‖ + ‖x - p‖ := by
        have := norm_sub_le (x - q) (x - p)
        rwa [show x - q - (x - p) = p - q by ring] at this
      linarith
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_sum_kernel_le hρ hq
    have h2 := hMF x (mem_closedBall_zero_iff.2 hx)
    have h3 : ((S.erase p).card : ℝ) * ρ⁻¹ ≤ S.card * ρ⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) (by positivity)
    rw [hMdef]; linarith
  -- the functions
  set A : ℂ → ℝ := fun y => ξ y * ‖E y‖ ^ 2 with hAdef
  set c : ℝ := L + 2 * Xi * M with hcdef
  have hc0 : 0 ≤ c := by positivity
  set fη : ℝ → ℂ → ℝ := fun η x => (punctured Λ η).indicator A x -
    ∑ p ∈ S, ξ p * (ball p ρ \ ball p η).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x with hfη
  set f0 : ℂ → ℝ := fun x => A x - ∑ p ∈ S, ξ p * (ball p ρ).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x
    with hf0
  set g : ℂ → ℝ := fun x => ∑ p ∈ S, (ball p ρ).indicator (fun y => c * ‖y - p‖⁻¹) x +
    (closedBall (0 : ℂ) R).indicator (fun _ => Xi * M ^ 2) x with hg
  have hind0 : ∀ x, ∀ p ∈ S, 0 ≤ (ball p ρ).indicator (fun y => c * ‖y - p‖⁻¹) x := fun x p _ =>
    indicator_nonneg (fun y _ => by positivity) x
  have hK0 : ∀ x, 0 ≤ (closedBall (0 : ℂ) R).indicator (fun _ => Xi * M ^ 2) x := fun x =>
    indicator_nonneg (fun y _ => by positivity) x
  have hg0 : ∀ x, 0 ≤ g x := fun x => add_nonneg (Finset.sum_nonneg (hind0 x)) (hK0 x)
  have hother : ∀ x, ∀ p ∈ S, x ∈ ball p ρ → ∀ q ∈ S, q ≠ p → x ∉ ball q ρ := by
    intro x p hp hxp q hq hqp hxq
    have h1 := hdisj p hp q hq (Ne.symm hqp)
    rw [mem_ball, dist_eq_norm] at hxp hxq
    have h3 : ‖p - q‖ ≤ ‖x - q‖ + ‖x - p‖ := by
      have := norm_sub_le (x - q) (x - p)
      rwa [show x - q - (x - p) = p - q by ring] at this
    linarith
  -- membership in the punctured plane near the support
  have hmemΩ : ∀ η : ℝ, η < 1 → ∀ x : ℂ, ‖x‖ < R → (∀ q ∈ S, η ≤ ‖x - q‖) → x ∈ punctured Λ η := by
    intro η hη1 x hx hq
    rw [mem_punctured]
    intro q hqΛ
    by_cases hqS : q ∈ S
    · exact hq q hqS
    · have h1 := hfar q hqΛ hqS
      have h2 : ‖q‖ ≤ ‖x‖ + ‖x - q‖ := by
        have := norm_sub_le x (x - q); rwa [show x - (x - q) = q by ring] at this
      linarith
  -- the pointwise bound
  have hbound : ∀ η : ℝ, 0 < η → η < ρ → ∀ x : ℂ, x ∉ (S : Set ℂ) →
      (x ∈ ball (0 : ℂ) (R + 1) → E x = ∑ q ∈ S, kernel (x - q) + F x) → |fη η x| ≤ g x := by
    intro η hη0 hηρ x hxS hEx
    by_cases hball : ∃ p ∈ S, x ∈ ball p ρ
    · obtain ⟨p, hpS, hxp⟩ := hball
      have hxp0 : x ≠ p := fun h => hxS (h ▸ hpS)
      have hd : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp0)
      have hdρ : ‖x - p‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hxp
      have hB : ∑ q ∈ S, ξ q * (ball q ρ \ ball q η).indicator (fun y => (‖y - q‖ ^ 2)⁻¹) x =
          ξ p * (ball p ρ \ ball p η).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x :=
        Finset.sum_eq_single p (fun q hq hqp => by
          rw [indicator_of_notMem (fun h => hother x p hpS hxp q hq hqp h.1), mul_zero])
          (fun h => absurd hpS h)
      have hG : g x = c * ‖x - p‖⁻¹ + (closedBall (0 : ℂ) R).indicator (fun _ => Xi * M ^ 2) x := by
        rw [hg]
        simp only
        rw [Finset.sum_eq_single p (fun q hq hqp => indicator_of_notMem
          (hother x p hpS hxp q hq hqp) _) (fun h => absurd hpS h), indicator_of_mem hxp]
      simp only [hfη]
      rw [hB, hG]
      by_cases hξx : ξ x = 0
      · have hA : (punctured Λ η).indicator A x = 0 := by
          by_cases hm : x ∈ punctured Λ η <;> simp [hm, hAdef, hξx]
        rw [hA, zero_sub, abs_neg, abs_mul]
        have h1 : |ξ p| ≤ L * ‖x - p‖ := by
          have := hL x p; rwa [hξx, zero_sub, abs_neg] at this
        have h2 : |(ball p ρ \ ball p η).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x| ≤ (‖x - p‖ ^ 2)⁻¹ :=
          (abs_indicator_le_abs x).trans (by rw [abs_of_nonneg (by positivity)])
        have h3 : L * ‖x - p‖ * (‖x - p‖ ^ 2)⁻¹ = L * ‖x - p‖⁻¹ := by
          field_simp
        have h4 : L * ‖x - p‖⁻¹ ≤ c * ‖x - p‖⁻¹ :=
          mul_le_mul_of_nonneg_right (by rw [hcdef]; nlinarith) (by positivity)
        calc |ξ p| * |(ball p ρ \ ball p η).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x|
            ≤ L * ‖x - p‖ * (‖x - p‖ ^ 2)⁻¹ := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ ≤ c * ‖x - p‖⁻¹ + (closedBall (0 : ℂ) R).indicator (fun _ => Xi * M ^ 2) x := by
            rw [h3]; linarith [hK0 x]
      · have hxR := hξR x hξx
        have hxK : x ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hxR.le
        rw [indicator_of_mem hxK]
        by_cases hη' : η ≤ ‖x - p‖
        · have hmem : x ∈ punctured Λ η := by
            refine hmemΩ η (by linarith) x hxR fun q hq => ?_
            by_cases hqp : q = p
            · rw [hqp]; exact hη'
            · have := hother x p hpS hxp q hq hqp
              rw [mem_ball, dist_eq_norm, not_lt] at this
              linarith
          have hann : x ∈ ball p ρ \ ball p η := ⟨hxp, by rw [mem_ball, dist_eq_norm, not_lt]; exact hη'⟩
          rw [indicator_of_mem hmem, indicator_of_mem hann]
          simp only [hAdef]
          have hEx' := hEx (mem_ball_zero_iff.2 (by linarith))
          rw [← Finset.add_sum_erase S _ hpS, add_assoc] at hEx'
          have hGp := hGbd x p hpS hxR.le hxp
          have hk : ‖kernel (x - p)‖ ^ 2 = (‖x - p‖ ^ 2)⁻¹ := by rw [norm_kernel, inv_pow]
          have hEE := abs_norm_add_sq_sub_le (k := kernel (x - p)) hGp
          rw [← hEx', hk, norm_kernel] at hEE
          have hsplit : ξ x * ‖E x‖ ^ 2 - ξ p * (‖x - p‖ ^ 2)⁻¹ =
              (ξ x - ξ p) * (‖x - p‖ ^ 2)⁻¹ + ξ x * (‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹) := by ring
          rw [hsplit]
          have h1 : |(ξ x - ξ p) * (‖x - p‖ ^ 2)⁻¹| ≤ L * ‖x - p‖⁻¹ := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖x - p‖ ^ 2)⁻¹)]
            calc |ξ x - ξ p| * (‖x - p‖ ^ 2)⁻¹ ≤ L * ‖x - p‖ * (‖x - p‖ ^ 2)⁻¹ :=
                  mul_le_mul_of_nonneg_right (hL x p) (by positivity)
              _ = L * ‖x - p‖⁻¹ := by field_simp
          have h2 : |ξ x * (‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹)| ≤
              Xi * (2 * M * ‖x - p‖⁻¹ + M ^ 2) := by
            rw [abs_mul]
            exact mul_le_mul (hXi' x) hEE (abs_nonneg _) hXi0
          calc |(ξ x - ξ p) * (‖x - p‖ ^ 2)⁻¹ + ξ x * (‖E x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹)|
              ≤ L * ‖x - p‖⁻¹ + Xi * (2 * M * ‖x - p‖⁻¹ + M ^ 2) :=
                (abs_add_le _ _).trans (add_le_add h1 h2)
            _ = c * ‖x - p‖⁻¹ + Xi * M ^ 2 := by rw [hcdef]; ring
        · have hnm : x ∉ punctured Λ η := fun h => hη' ((mem_punctured.1 h) p (hSΛ p hpS))
          have hnann : x ∉ ball p ρ \ ball p η := fun h => h.2 (by
            rw [mem_ball, dist_eq_norm]; exact not_le.1 hη')
          rw [indicator_of_notMem hnm, indicator_of_notMem hnann, mul_zero, sub_zero, abs_zero]
          positivity
    · push Not at hball
      have hB : ∑ q ∈ S, ξ q * (ball q ρ \ ball q η).indicator (fun y => (‖y - q‖ ^ 2)⁻¹) x = 0 :=
        Finset.sum_eq_zero fun q hq => by rw [indicator_of_notMem (fun h => hball q hq h.1), mul_zero]
      simp only [hfη]
      rw [hB, sub_zero]
      by_cases hξx : ξ x = 0
      · have hA : (punctured Λ η).indicator A x = 0 := by
          by_cases hm : x ∈ punctured Λ η <;> simp [hm, hAdef, hξx]
        rw [hA, abs_zero]; exact hg0 x
      · have hxR := hξR x hξx
        have hxK : x ∈ closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hxR.le
        have hq : ∀ q ∈ S, ρ ≤ ‖x - q‖ := fun q hq => by
          have := hball q hq; rwa [mem_ball, dist_eq_norm, not_lt] at this
        have hEx' := hEx (mem_ball_zero_iff.2 (by linarith))
        have hEn : ‖E x‖ ≤ M := hEx' ▸ hEbd x hxR.le hq
        refine (abs_indicator_le_abs x).trans ?_
        simp only [hg, hAdef]
        rw [indicator_of_mem hxK, abs_mul]
        have : ‖E x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hEn 2
        have h1 : |ξ x| * |‖E x‖ ^ 2| ≤ Xi * M ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg ‖E x‖)]
          exact mul_le_mul (hXi' x) this (by positivity) hXi0
        linarith [Finset.sum_nonneg (hind0 x)]
  -- the pointwise limit
  have hlim : ∀ x : ℂ, x ∉ (S : Set ℂ) → Tendsto (fun η => fη η x) (𝓝[>] 0) (𝓝 (f0 x)) := by
    intro x hxS
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < 1 ∧ ∀ q ∈ S, η < ‖x - q‖ := by
      refine (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)).and ?_
      refine (Filter.eventually_all_finset S).2 fun q hq =>
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ?_)
      exact norm_pos_iff.2 (sub_ne_zero.2 fun h => hxS (h ▸ hq))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with η ⟨hη1, hq⟩
    simp only [hfη, hf0]
    congr 1
    · by_cases hξx : ξ x = 0
      · by_cases hm : x ∈ punctured Λ η <;> simp [hm, hAdef, hξx]
      · rw [indicator_of_mem (hmemΩ η hη1 x (hξR x hξx) fun q hq' => (hq q hq').le)]
    · refine Finset.sum_congr rfl fun q hq' => ?_
      have hxq : x ∉ ball q η := by rw [mem_ball, dist_eq_norm, not_lt]; exact (hq q hq').le
      by_cases hxρ : x ∈ ball q ρ
      · rw [indicator_of_mem hxρ, indicator_of_mem (show x ∈ ball q ρ \ ball q η from ⟨hxρ, hxq⟩)]
      · rw [indicator_of_notMem hxρ,
          indicator_of_notMem (show x ∉ ball q ρ \ ball q η from fun h => hxρ h.1)]
  -- measurability and integrability
  have hEm : AEStronglyMeasurable E volume := hE.2.1.aestronglyMeasurable
  have hAm : AEStronglyMeasurable A volume :=
    hξ.continuous.aestronglyMeasurable.mul (hEm.norm.pow 2)
  have hBm : ∀ η : ℝ, Measurable fun x =>
      ∑ p ∈ S, ξ p * (ball p ρ \ ball p η).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x := fun η =>
    Finset.measurable_sum S fun p _ => measurable_const.mul (measurable_annulus_term p η ρ)
  have hfm : ∀ η : ℝ, AEStronglyMeasurable (fη η) volume := fun η =>
    (hAm.indicator (measurableSet_punctured Λ η)).sub (hBm η).aestronglyMeasurable
  have hgint : Integrable g := by
    refine (integrable_finsetSum S fun p _ => ?_).add ?_
    · refine IntegrableOn.integrable_indicator ?_ measurableSet_ball
      refine Sphere.integrableOn_ball_of_le_inv (C := c)
        ((measurable_const.mul ((measurable_norm.comp (measurable_id.sub_const p)).inv)).aestronglyMeasurable)
        fun y _ _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_inv]
    · exact (continuousOn_const.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)).integrable_indicator
        measurableSet_closedBall
  have hgood : ∀ᵐ x : ℂ, x ∉ (S : Set ℂ) ∧
      (x ∈ ball (0 : ℂ) (R + 1) → E x = ∑ q ∈ S, kernel (x - q) + F x) := by
    have h1 : ∀ᵐ x : ℂ, x ∉ (S : Set ℂ) := S.finite_toSet.countable.ae_notMem _
    have h2 := (ae_restrict_iff' measurableSet_ball).1 hloc
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  have hDCT : Tendsto (fun η => ∫ x, fη η x) (𝓝[>] 0) (𝓝 (∫ x, f0 x)) := by
    refine tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hfm) ?_ hgint ?_
    · filter_upwards [Ioo_mem_nhdsGT hρ] with η hη
      filter_upwards [hgood] with x hx
      rw [Real.norm_eq_abs]
      exact hbound η hη.1 hη.2 x hx.1 hx.2
    · filter_upwards [hgood] with x hx
      exact hlim x hx.1
  -- the identity for `0 < η < ρ`
  have hsum : ∑ᶠ p ∈ Λ, ξ p = ∑ p ∈ S, ξ p :=
    finsum_mem_eq_sum_toFinset (hE.1 (R + 1)) fun p hp => hξ0 p (by linarith)
  have hident : ∀ η ∈ Ioo 0 ρ, IntegrableOn A (punctured Λ η) ∧
      (1 / 2 : ℝ) * (∫ x in punctured Λ η, A x) + Real.pi * Real.log η * ∑ᶠ p ∈ Λ, ξ p =
        (1 / 2 : ℝ) * (∫ x, fη η x) + Real.pi * Real.log ρ * ∑ p ∈ S, ξ p := by
    intro η hη
    have hfint : Integrable (fη η) := by
      refine Integrable.mono' hgint (hfm η) ?_
      filter_upwards [hgood] with x hx
      rw [Real.norm_eq_abs]
      exact hbound η hη.1 hη.2 x hx.1 hx.2
    have hBint : Integrable fun x =>
        ∑ p ∈ S, ξ p * (ball p ρ \ ball p η).indicator (fun y => (‖y - p‖ ^ 2)⁻¹) x :=
      integrable_finsetSum S fun p _ => (integrable_annulus_term p hη.1).const_mul _
    have hAint : Integrable ((punctured Λ η).indicator A) := by
      refine (hfint.add hBint).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, hfη, sub_add_cancel]
    refine ⟨(integrable_indicator_iff (measurableSet_punctured Λ η)).1 hAint, ?_⟩
    have hI : ∫ x, fη η x = (∫ x in punctured Λ η, A x) -
        ∑ p ∈ S, ξ p * (2 * Real.pi * Real.log (ρ / η)) := by
      simp only [hfη]
      rw [integral_sub hAint hBint, integral_indicator (measurableSet_punctured Λ η),
        integral_finsetSum S fun p _ => (integrable_annulus_term p hη.1).const_mul _]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [integral_const_mul, integral_indicator (measurableSet_ball.diff measurableSet_ball),
        Sphere.integral_inv_sq_annulus_center p hη.1 hη.2]
    rw [hI, hsum, Real.log_div hρ.ne' hη.1.ne', ← Finset.sum_mul]
    ring
  refine ⟨(1 / 2 : ℝ) * (∫ x, f0 x) + Real.pi * Real.log ρ * ∑ p ∈ S, ξ p, ?_⟩
  have hreal : Tendsto (fun η => (1 / 2 : ℝ) * (∫ x, fη η x) + Real.pi * Real.log ρ * ∑ p ∈ S, ξ p)
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) * (∫ x, f0 x) + Real.pi * Real.log ρ * ∑ p ∈ S, ξ p)) :=
    (hDCT.const_mul _).add_const _
  refine ((continuous_coe_real_ereal.tendsto _).comp hreal).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hρ] with η hη
  obtain ⟨hint, heq⟩ := hident η hη
  rw [Function.comp_apply, punctureFunctional_eq_coe hint, heq]

end Whole

end SandierSerfaty

end
