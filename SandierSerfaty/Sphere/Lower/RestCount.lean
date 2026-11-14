/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GridCounting
public import SandierSerfaty.Sphere.Lower.GoodSquare
public import SandierSerfaty.Sphere.Lower.SquareData

/-!
# Points outside the good squares (sphere note, Theorem 6.14, error budget (b), (d))

`Lower.card_rest_le`: the points of the chart not in a good quantized square lie in a bad square, in `K ∖ Q` for a cell
`K`, or within `2R + 1` of the boundary of the disc; their number is at most
`∑_{bad} p_j + #cells · 7R + 16 ρ (R+1)`.
-/

open MeasureTheory Set Metric
open scoped ENNReal Classical ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The blown-up points as a finite set of the plane. -/
@[expose] noncomputable def allPts {n : ℕ} (X : Fin n → ℂ) : Finset ℂ :=
  Finset.univ.image fun i => blowupScale n • X i

theorem card_filter_index {n : ℕ} (X : Fin n → ℂ) (hinj : Function.Injective fun i => blowupScale n • X i)
    (P : ℂ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i => P (blowupScale n • X i)).card = ((allPts X).filter P).card := by
  unfold allPts
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]

theorem separated_allPts {n : ℕ} (X : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) :
    ∀ p ∈ allPts X, ∀ q ∈ allPts X, p ≠ q → 1 ≤ ‖p - q‖ := by
  intro p hp q hq hpq
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
  exact hsep i j fun h => hpq (by rw [h])

theorem exists_cell {R : ℝ} (hR : 0 < R) (θ : ℝ × ℝ) (z : ℂ) : ∃ j : ℤ × ℤ, z ∈ gridSq R θ j := by
  refine ⟨(⌊(z.re - θ.1) / R⌋, ⌊(z.im - θ.2) / R⌋), ?_⟩
  have h1 := Int.floor_le ((z.re - θ.1) / R)
  have h2 := Int.lt_floor_add_one ((z.re - θ.1) / R)
  have h3 := Int.floor_le ((z.im - θ.2) / R)
  have h4 := Int.lt_floor_add_one ((z.im - θ.2) / R)
  rw [le_div_iff₀ hR] at h1 h3
  rw [div_lt_iff₀ hR] at h2 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem card_rest_le {n : ℕ} (X : Fin n → ℂ) (hinj : Function.Injective fun i => blowupScale n • X i)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {R : ℝ} {θ : ℝ × ℝ} {ρ : ℝ}
    (hR : 2 ≤ R) (hρ : 1 ≤ ρ) (t : ℤ × ℤ → ℝ) (ht1 : ∀ j ∈ cellFin R θ ρ, R - 1 ≤ t j)
    (ht2 : ∀ j ∈ cellFin R θ ρ, t j ≤ R - 1 / 2) (Good : Finset (ℤ × ℤ)) (_hG : Good ⊆ cellFin R θ ρ) :
    ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
        ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)).card : ℝ) ≤
      ∑ j ∈ cellFin R θ ρ \ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) +
        (cellFin R θ ρ).card * (7 * R) + 16 * ρ * (R + 1) := by
  have hR0 : 0 < R := by linarith
  set J := cellFin R θ ρ with hJ
  set U₁ : Finset (Fin n) := (J \ Good).biUnion fun j =>
    Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j) with hU₁
  set U₂ : Finset (Fin n) := J.biUnion fun j =>
    Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt (cellAt R θ j) R \ sqAt (cellAt R θ j) (t j) with hU₂
  set U₃ : Finset (Fin n) := Finset.univ.filter fun i => ρ - 1 - 2 * R < ‖blowupScale n • X i‖ ∧ ‖blowupScale n • X i‖ < ρ with hU₃
  have hsub : (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧ ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)) ⊆
      U₁ ∪ U₂ ∪ U₃ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hρi, hnot⟩ := hi
    obtain ⟨j, hj⟩ := exists_cell hR0 θ (blowupScale n • X i)
    by_cases hjJ : j ∈ J
    · by_cases hQ : blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)
      · have hjG : j ∉ Good := fun h => hnot ⟨j, h, hQ⟩
        refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        rw [hU₁, Finset.mem_biUnion]
        exact ⟨j, Finset.mem_sdiff.2 ⟨hjJ, hjG⟩, by simpa using hQ⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [hU₂, Finset.mem_biUnion]
        exact ⟨j, hjJ, by simpa using ⟨gridSq_subset_sqAt θ j hj, hQ⟩⟩
    · refine Finset.mem_union_right _ ?_
      rw [hU₃, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hρi⟩
      have hnc : ¬ sqAt (cellAt R θ j) R ⊆ closedBall (0 : ℂ) (ρ - 1) := fun h =>
        hjJ ((mem_cellFin hR0 hρ).2 h)
      rw [Set.not_subset] at hnc
      obtain ⟨w, hw, hwb⟩ := hnc
      rw [mem_closedBall, dist_zero_right, not_le] at hwb
      have h1 := norm_sub_le_of_mem_sqAt (gridSq_subset_sqAt θ j hj) hw
      have h2 : ‖w‖ ≤ ‖blowupScale n • X i‖ + ‖blowupScale n • X i - w‖ := by
        calc ‖w‖ = ‖blowupScale n • X i - (blowupScale n • X i - w)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖blowupScale n • X i‖ + ‖blowupScale n • X i - w‖ := norm_sub_le _ _
      linarith
  have hcard := Finset.card_le_card hsub
  have h12 := Finset.card_union_le (U₁ ∪ U₂) U₃
  have h1' := Finset.card_union_le U₁ U₂
  have c1 : (U₁.card : ℝ) ≤ ∑ j ∈ J \ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ) := by
    have := Finset.card_biUnion_le (s := J \ Good) (t := fun j =>
      Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j))
    have h' : U₁.card ≤ ∑ j ∈ J \ Good, (ptsIn X (cellAt R θ j) (t j)).card := by
      refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [card_ptsIn X hinj]
    exact_mod_cast h'
  have c2 : (U₂.card : ℝ) ≤ J.card * (7 * R) := by
    have := Finset.card_biUnion_le (s := J) (t := fun j =>
      Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt (cellAt R θ j) R \ sqAt (cellAt R θ j) (t j))
    have h' : (U₂.card : ℝ) ≤ ∑ j ∈ J, ((Finset.univ.filter fun i =>
        blowupScale n • X i ∈ sqAt (cellAt R θ j) R \ sqAt (cellAt R θ j) (t j)).card : ℝ) := by
      exact_mod_cast this
    refine h'.trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [card_filter_index X hinj (fun w => w ∈ sqAt (cellAt R θ j) R \ sqAt (cellAt R θ j) (t j))]
    exact card_filter_leftover_le (separated_allPts X hsep) _ hR (ht1 j hj) (ht2 j hj)
  have c3 : (U₃.card : ℝ) ≤ 16 * ρ * (R + 1) := by
    rw [hU₃, card_filter_index X hinj (fun w => ρ - 1 - 2 * R < ‖w‖ ∧ ‖w‖ < ρ)]
    exact card_filter_annulus_le (separated_allPts X hsep) hρ hR0.le
  have : ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧ ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)).card : ℝ) ≤
      (U₁.card : ℝ) + U₂.card + U₃.card := by
    exact_mod_cast hcard.trans (h12.trans (by omega))
  have e : (J \ Good) = J \ Good := rfl
  linarith

theorem sqAt_cell_subset_closedBall {R : ℝ} (hR : 0 < R) {θ : ℝ × ℝ} {ρ : ℝ} (hρ : 1 ≤ ρ) {j : ℤ × ℤ}
    (hj : j ∈ cellFin R θ ρ) {t : ℝ} (ht : t ≤ R) :
    sqAt (cellAt R θ j) t ⊆ closedBall (0 : ℂ) (ρ - 1) :=
  (sqAt_mono _ ht).trans ((mem_cellFin hR hρ).1 hj)

theorem sum_card_ptsIn_add_card_rest {n : ℕ} (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {R : ℝ} {θ : ℝ × ℝ} {ρ : ℝ} (hR : 0 < R)
    (hρ : 1 ≤ ρ) (t : ℤ × ℤ → ℝ) (ht : ∀ j ∈ cellFin R θ ρ, t j ≤ R - 1 / 2) (Good : Finset (ℤ × ℤ))
    (hG : Good ⊆ cellFin R θ ρ) :
    (∑ j ∈ Good, ((ptsIn X (cellAt R θ j) (t j)).card : ℝ)) +
      ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
        ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)).card : ℝ) =
      ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) := by
  set inner : Finset (Fin n) := Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ with hinner
  set P : Fin n → Prop := fun i => ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j) with hP
  set F : ℤ × ℤ → Finset (Fin n) := fun j =>
    Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j) with hF
  have hsq : ∀ j ∈ Good, sqAt (cellAt R θ j) (t j) ⊆ closedBall (0 : ℂ) (ρ - 1) := fun j hj =>
    sqAt_cell_subset_closedBall hR hρ (hG hj) (by linarith [ht j (hG hj)])
  have hFdisj : ∀ j ∈ Good, ∀ j' ∈ Good, j ≠ j' → Disjoint (F j) (F j') := by
    intro j hj j' hj' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    have := sqAt_disjoint hR θ hne (by linarith [ht j (hG hj)] : t j < R)
      (by linarith [ht j' (hG hj')] : t j' < R)
    exact Set.disjoint_left.1 this (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hi').2
  have hfilter : inner.filter P = Good.biUnion F := by
    ext i
    simp only [hinner, hP, hF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨-, j, hj, hij⟩; exact ⟨j, hj, hij⟩
    · rintro ⟨j, hj, hij⟩
      refine ⟨?_, j, hj, hij⟩
      have := hsq j hj hij
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  have hrest : (Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
      ¬ ∃ j ∈ Good, blowupScale n • X i ∈ sqAt (cellAt R θ j) (t j)) = inner.filter (fun i => ¬ P i) := by
    ext i
    simp [hinner, hP]
  have hcard : (inner.filter P).card + (inner.filter (fun i => ¬ P i)).card = inner.card :=
    Finset.card_filter_add_card_filter_not P
  rw [hfilter, Finset.card_biUnion (fun j hj j' hj' hne => hFdisj j hj j' hj' hne)] at hcard
  rw [hrest]
  have hs : ∑ j ∈ Good, (F j).card = ∑ j ∈ Good, (ptsIn X (cellAt R θ j) (t j)).card :=
    Finset.sum_congr rfl fun j _ => (card_ptsIn X hinj _ _).symm
  rw [hs] at hcard
  exact_mod_cast hcard

theorem integral_norm_gradC_sub_le_on {u v : ℂ → ℝ} (hu : LocallyLipschitz u) (hv : ContDiff ℝ ∞ v) {a : ℂ}
    {t : ℝ} {Ω : Set ℂ} (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ sqAt a t) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in Ω, ‖gradC (fun y => u y - v y) x‖ ^ 2 ≤
      (1 + ε) * (∫ x in Ω, ‖gradC u x‖ ^ 2) + (1 + 1 / ε) * ∫ x in Ω, ‖gradC v x‖ ^ 2 := by
  have hQc := isCompact_sqAt a t
  have hv1 : LocallyLipschitz v := ((hv.of_le (by norm_cast)).locallyLipschitz)
  have hw := hasWeakGradientOn_of_locallyLipschitz hu hQc
  have hwv := hasWeakGradientOn_of_locallyLipschitz hv1 hQc
  have hwd := hasWeakGradientOn_of_locallyLipschitz (hu.sub hv1) hQc
  have hmono : ∀ f : ℂ → ℝ, Integrable (fun x => f x) (volume.restrict (sqAt a t)) →
      Integrable (fun x => f x) (volume.restrict Ω) := fun f hf =>
    hf.mono_measure (Measure.restrict_mono hΩ le_rfl)
  have i1 : Integrable (fun x => ‖gradC u x‖ ^ 2) (volume.restrict Ω) :=
    hmono _ (hw.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have i2 : Integrable (fun x => ‖gradC v x‖ ^ 2) (volume.restrict Ω) :=
    hmono _ (hwv.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have i3 : Integrable (fun x => ‖gradC (fun y => u y - v y) x‖ ^ 2) (volume.restrict Ω) :=
    hmono _ (hwd.2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have e : (1 + ε) * (∫ x in Ω, ‖gradC u x‖ ^ 2) + (1 + 1 / ε) * ∫ x in Ω, ‖gradC v x‖ ^ 2 =
      ∫ x in Ω, ((1 + ε) * ‖gradC u x‖ ^ 2 + (1 + 1 / ε) * ‖gradC v x‖ ^ 2) := by
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  rw [e]
  refine integral_mono_ae i3 ((i1.const_mul _).add (i2.const_mul _)) ?_
  have hae : ∀ᵐ x ∂(volume : Measure ℂ), DifferentiableAt ℝ u x := ae_differentiableAt_of_locallyLipschitz hu
  filter_upwards [(ae_restrict_iff' hΩm).2 (hae.mono fun x hx _ => hx)] with x hx
  rw [gradC_sub_of_differentiableAt hx (hv.differentiable (by simp) x)]
  exact sq_norm_sub_le _ _ hε

end Lower

end Sphere

end SandierSerfaty

end
