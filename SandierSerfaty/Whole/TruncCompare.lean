/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.PunctureLimit
public import SandierSerfaty.Statements.Jellium.Defs.TruncField
public import SandierSerfaty.Screening.TruncLogCalculus
public import SandierSerfaty.Screening.TruncFieldWeak

/-!
# Puncture versus truncation (comparison note, Lemma `lem:punct-trunc`)

For `E ∈ 𝒜₁` and `R > 0`, `IsAdmissibleField.exists_localData` gives the local data on `B̄(0, R)`: the
finite set `S = Λ ∩ B̄(0, R + 1)`, a separation `ρ ≤ ½` of `S`, and a bound `M` with
`|E - κ(· - p)| ≤ M` on `B(p, ρ)` and `|E| ≤ M` off the discs `B(p, ρ)` (a.e. on `B̄(0, R)`).

**Theorem** (`lintegral_truncField_neg_le`). For `0 < η < ρ` and measurable `D ⊆ B̄(0, R)`, the book
truncation of `-E` at the constant radius `η` (`truncField Λ (fun _ ↦ η) (-E)`, which is `-E` off the
discs `B(p, η)` and `-(E - κ(· - p))` on `B(p, η)`) satisfies
`∫_D |(-E)_η|² ≤ ∫_{D ∩ Ω_η} |E|² + M² |S| π η²`, and `∫_{D ∩ Ω_η} |E|² < ∞`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Whole

/-- **Local data** of an admissible field on `B̄(0, R)`. -/
theorem IsAdmissibleField.exists_localData {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E)
    (R : ℝ) :
    ∃ (S : Finset ℂ) (ρ M : ℝ), 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 ≤ M ∧
      (∀ q, q ∈ S ↔ q ∈ Λ ∧ ‖q‖ ≤ R + 1) ∧
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → 2 * ρ ≤ ‖p - q‖) ∧
      ∀ᵐ x : ℂ, ‖x‖ ≤ R →
        (∀ p ∈ S, x ∈ ball p ρ → ‖E x - kernel (x - p)‖ ≤ M) ∧
        ((∀ p ∈ S, ρ ≤ ‖x - p‖) → ‖E x‖ ≤ M) := by
  obtain ⟨F, hF, hloc⟩ := IsAdmissibleField.exists_local_form hE (R + 1)
  set S := (hE.1 (R + 1)).toFinset with hS
  obtain ⟨ρ, hρ, hρ2, hdisj⟩ := exists_sep S
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (hF.continuousOn.mono (closedBall_subset_ball (by linarith)))
  set M : ℝ := max MF 0 + S.card * ρ⁻¹ with hMdef
  refine ⟨S, ρ, M, hρ, hρ2, by positivity, fun q => ?_, hdisj, ?_⟩
  · rw [hS, Set.Finite.mem_toFinset, mem_inter_iff, mem_closedBall_zero_iff]
  have h2 := (ae_restrict_iff' measurableSet_ball).1 hloc
  filter_upwards [h2] with x hx hxR
  have hEx := hx (mem_ball_zero_iff.2 (by linarith))
  have hFx : ‖F x‖ ≤ max MF 0 := (hMF x (mem_closedBall_zero_iff.2 hxR)).trans (le_max_left _ _)
  constructor
  · intro p hp hxp
    have hq : ∀ q ∈ S.erase p, ρ ≤ ‖x - q‖ := by
      intro q hq
      obtain ⟨hqp, hqS⟩ := Finset.mem_erase.1 hq
      have h1 := hdisj p hp q hqS (Ne.symm hqp)
      have h2 : ‖x - p‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hxp
      have h3 : ‖p - q‖ ≤ ‖x - q‖ + ‖x - p‖ := by
        have := norm_sub_le (x - q) (x - p)
        rwa [show x - q - (x - p) = p - q by ring] at this
      linarith
    rw [hEx, ← Finset.add_sum_erase S _ hp]
    have e : kernel (x - p) + ∑ q ∈ S.erase p, kernel (x - q) + F x - kernel (x - p) =
        ∑ q ∈ S.erase p, kernel (x - q) + F x := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_sum_kernel_le hρ hq
    have h3 : ((S.erase p).card : ℝ) * ρ⁻¹ ≤ S.card * ρ⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_erase_le) (by positivity)
    rw [hMdef]; linarith
  · intro hq
    rw [hEx]
    refine (norm_add_le _ _).trans ?_
    have := norm_sum_kernel_le hρ hq
    rw [hMdef]; linarith

theorem volume_ball_eq_ofReal (p : ℂ) {η : ℝ} (hη : 0 ≤ η) :
    volume (ball p η) = ENNReal.ofReal (Real.pi * η ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hη,
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, mul_comm]

/-- For points of `B̄(0, R)` only the charges of `S = Λ ∩ B̄(0, R + 1)` are within distance `1`. -/
theorem lt_norm_sub_of_notMem {Λ : Set ℂ} {S : Finset ℂ} {R : ℝ}
    (hS : ∀ q, q ∈ S ↔ q ∈ Λ ∧ ‖q‖ ≤ R + 1) {x q : ℂ} (hx : ‖x‖ ≤ R) (hqΛ : q ∈ Λ) (hqS : q ∉ S) :
    1 < ‖x - q‖ := by
  have h1 : R + 1 < ‖q‖ := not_le.1 fun h => hqS ((hS q).2 ⟨hqΛ, h⟩)
  have h2 : ‖q‖ ≤ ‖x‖ + ‖x - q‖ := by
    have := norm_sub_le x (x - q); rwa [show x - (x - q) = q by ring] at this
  linarith

theorem truncField_const_eq_of_far {Λ : Set ℂ} {E : ℂ → ℂ} {η : ℝ} (hη : 0 < η) {x : ℂ}
    (hfar : ∀ q ∈ Λ, η < ‖x - q‖) : truncField Λ (fun _ => η) E x = E x := by
  unfold truncField
  rw [finsum_mem_eq_zero_of_forall_eq_zero fun q hq => Screening.gradient_truncLog_of_gt hη (hfar q hq),
    sub_zero]

theorem truncField_const_eq_of_near {Λ : Set ℂ} {E : ℂ → ℂ} {η : ℝ} (hη : 0 < η) {x p : ℂ}
    (hp : p ∈ Λ) (hxp0 : x ≠ p) (hxp : ‖x - p‖ < η) (hfar : ∀ q ∈ Λ, q ≠ p → η < ‖x - q‖) :
    truncField Λ (fun _ => η) E x = E x + kernel (x - p) := by
  unfold truncField
  have hsub : (({p} : Finset ℂ) : Set ℂ) ⊆ Λ := by simpa using hp
  rw [Screening.finsum_mem_eq_finsetSum hsub fun q hq hqp =>
      Screening.gradient_truncLog_of_gt hη (hfar q hq (by simpa using hqp)),
    Finset.sum_singleton, Screening.gradient_truncLog_of_lt (norm_pos_iff.2 (sub_ne_zero.2 hxp0)) hxp,
    kernel, neg_smul, sub_neg_eq_add]

/-- **Puncture versus truncation** (comparison note, Lemma `lem:punct-trunc`), lintegral form. -/
theorem lintegral_truncField_neg_le {Λ : Set ℂ} {E : ℂ → ℂ} {S : Finset ℂ} {ρ M R : ℝ}
    (hρ2 : ρ ≤ 1 / 2) (hS : ∀ q, q ∈ S ↔ q ∈ Λ ∧ ‖q‖ ≤ R + 1)
    (hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 2 * ρ ≤ ‖p - q‖)
    (hloc : ∀ᵐ x : ℂ, ‖x‖ ≤ R →
        (∀ p ∈ S, x ∈ ball p ρ → ‖E x - kernel (x - p)‖ ≤ M) ∧
        ((∀ p ∈ S, ρ ≤ ‖x - p‖) → ‖E x‖ ≤ M))
    {η : ℝ} (hη : 0 < η) (hηρ : η < ρ) {D : Set ℂ} (hD : MeasurableSet D)
    (hDR : D ⊆ closedBall 0 R) :
    (∫⁻ x in D, ENNReal.ofReal (‖truncField Λ (fun _ => η) (fun y => -E y) x‖ ^ 2)) ≤
        (∫⁻ x in D ∩ punctured Λ η, ENNReal.ofReal (‖E x‖ ^ 2)) +
          ENNReal.ofReal (M ^ 2 * S.card * (Real.pi * η ^ 2)) ∧
      (∫⁻ x in D ∩ punctured Λ η, ENNReal.ofReal (‖E x‖ ^ 2)) ≠ ⊤ := by
  have hη1 : η < 1 := by linarith
  -- good points: the local bounds hold and no sphere `‖x - q‖ = η`, `q ∈ S`, is hit
  have hsph : ∀ᵐ x : ℂ, ∀ q ∈ S, x ≠ q ∧ ‖x - q‖ ≠ η := by
    exact (Filter.eventually_all_finset S).2 fun q _ =>
      (Screening.ae_ne_center_ne_norm q η).mono fun x hx => ⟨sub_ne_zero.1 hx.1, hx.2⟩
  have hgood : ∀ᵐ x : ℂ, ‖x‖ ≤ R → (∀ q ∈ S, x ≠ q ∧ ‖x - q‖ ≠ η) ∧
      (∀ p ∈ S, x ∈ ball p ρ → ‖E x - kernel (x - p)‖ ≤ M) ∧
      ((∀ p ∈ S, ρ ≤ ‖x - p‖) → ‖E x‖ ≤ M) := by
    filter_upwards [hsph, hloc] with x h1 h2 hx
    exact ⟨h1, h2 hx⟩
  -- other charges are far from a point near `p`
  have hfarS : ∀ x : ℂ, ‖x‖ ≤ R → ∀ p ∈ S, ‖x - p‖ < ρ → ∀ q ∈ Λ, q ≠ p → ρ < ‖x - q‖ := by
    intro x hx p hp hxp q hqΛ hqp
    by_cases hqS : q ∈ S
    · have h1 := hdisj p hp q hqS (Ne.symm hqp)
      have h3 : ‖p - q‖ ≤ ‖x - q‖ + ‖x - p‖ := by
        have := norm_sub_le (x - q) (x - p)
        rwa [show x - q - (x - p) = p - q by ring] at this
      linarith
    · linarith [lt_norm_sub_of_notMem hS hx hqΛ hqS]
  -- the bound on the punctured part
  have hΩbd : ∀ᵐ x : ℂ, x ∈ D ∩ punctured Λ η → ‖E x‖ ≤ M + η⁻¹ := by
    filter_upwards [hgood] with x hx hxD
    obtain ⟨_, hnear, hoff⟩ := hx (mem_closedBall_zero_iff.1 (hDR hxD.1))
    by_cases hb : ∃ p ∈ S, x ∈ ball p ρ
    · obtain ⟨p, hp, hxp⟩ := hb
      have h1 := hnear p hp hxp
      have h2 : η ≤ ‖x - p‖ := (mem_punctured.1 hxD.2) p ((hS p).1 hp).1
      have h3 : ‖kernel (x - p)‖ ≤ η⁻¹ := by rw [norm_kernel]; exact inv_anti₀ hη h2
      calc ‖E x‖ = ‖(E x - kernel (x - p)) + kernel (x - p)‖ := by rw [sub_add_cancel]
        _ ≤ ‖E x - kernel (x - p)‖ + ‖kernel (x - p)‖ := norm_add_le _ _
        _ ≤ M + η⁻¹ := add_le_add h1 h3
    · push Not at hb
      have := hoff fun p hp => by
        have := hb p hp; rwa [mem_ball, dist_eq_norm, not_lt] at this
      linarith [inv_pos.2 hη]
  have hDΩ : MeasurableSet (D ∩ punctured Λ η) := hD.inter (measurableSet_punctured Λ η)
  refine ⟨?_, ?_⟩
  · rw [← lintegral_inter_add_sdiff _ _ (measurableSet_punctured Λ η)]
    refine add_le_add (le_of_eq ?_) ?_
    · refine setLIntegral_congr_fun_ae hDΩ ?_
      filter_upwards [hgood] with x hx hxD
      obtain ⟨hsp, -, -⟩ := hx (mem_closedBall_zero_iff.1 (hDR hxD.1))
      have hfar : ∀ q ∈ Λ, η < ‖x - q‖ := by
        intro q hq
        by_cases hqS : q ∈ S
        · exact lt_of_le_of_ne ((mem_punctured.1 hxD.2) q hq) (hsp q hqS).2.symm
        · linarith [lt_norm_sub_of_notMem hS (mem_closedBall_zero_iff.1 (hDR hxD.1)) hq hqS]
      rw [truncField_const_eq_of_far hη hfar, norm_neg]
    · have hsub : D \ punctured Λ η ⊆ ⋃ p ∈ S, ball p η := by
        intro x hx
        have hxn := hx.2
        rw [mem_punctured] at hxn
        push Not at hxn
        obtain ⟨q, hqΛ, hq⟩ := hxn
        by_cases hqS : q ∈ S
        · exact mem_biUnion hqS (by rw [mem_ball, dist_eq_norm]; exact hq)
        · linarith [lt_norm_sub_of_notMem hS (mem_closedBall_zero_iff.1 (hDR hx.1)) hqΛ hqS]
      have hbd : ∀ᵐ x ∂(volume.restrict (D \ punctured Λ η)),
          ENNReal.ofReal (‖truncField Λ (fun _ => η) (fun y => -E y) x‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) := by
        rw [ae_restrict_iff' (hD.diff (measurableSet_punctured Λ η))]
        filter_upwards [hgood] with x hx hxD
        have hxR := mem_closedBall_zero_iff.1 (hDR hxD.1)
        obtain ⟨hsp, hnear, -⟩ := hx hxR
        obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hsub hxD)
        rw [mem_ball, dist_eq_norm] at hxp
        have hpΛ := ((hS p).1 hp).1
        rw [truncField_const_eq_of_near hη hpΛ (hsp p hp).1 hxp fun q hq hqp =>
          lt_trans hηρ (hfarS x hxR p hp (hxp.trans hηρ) q hq hqp)]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
        have := hnear p hp (by rw [mem_ball, dist_eq_norm]; exact hxp.trans hηρ)
        rwa [show -E x + kernel (x - p) = -(E x - kernel (x - p)) by ring, norm_neg]
      calc (∫⁻ x in D \ punctured Λ η,
            ENNReal.ofReal (‖truncField Λ (fun _ => η) (fun y => -E y) x‖ ^ 2))
          ≤ ∫⁻ _ in D \ punctured Λ η, ENNReal.ofReal (M ^ 2) := lintegral_mono_ae hbd
        _ = ENNReal.ofReal (M ^ 2) * volume (D \ punctured Λ η) := by rw [setLIntegral_const]
        _ ≤ ENNReal.ofReal (M ^ 2) * ∑ p ∈ S, volume (ball p η) := by
            gcongr
            exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
        _ = ENNReal.ofReal (M ^ 2 * S.card * (Real.pi * η ^ 2)) := by
            have hsum : ∑ p ∈ S, volume (ball p η) = ENNReal.ofReal (S.card * (Real.pi * η ^ 2)) := by
              rw [Finset.sum_congr rfl fun p _ => volume_ball_eq_ofReal p hη.le, Finset.sum_const,
                nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
            rw [hsum, ← ENNReal.ofReal_mul (sq_nonneg M), mul_assoc]
  · have hfin : (∫⁻ x in D ∩ punctured Λ η, ENNReal.ofReal (‖E x‖ ^ 2)) ≤
        ∫⁻ _ in closedBall (0 : ℂ) R, ENNReal.ofReal ((M + η⁻¹) ^ 2) := by
      refine (lintegral_mono_ae ?_).trans (lintegral_mono_set (inter_subset_left.trans hDR))
      rw [ae_restrict_iff' hDΩ]
      filter_upwards [hΩbd] with x hx hxD
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hx hxD) 2)
    refine ne_top_of_le_ne_top ?_ hfin
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne

end Whole

end SandierSerfaty

end
