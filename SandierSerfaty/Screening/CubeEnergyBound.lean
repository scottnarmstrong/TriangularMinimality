/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.LocEnergy
public import SandierSerfaty.Statements.Jellium.Defs.CubeEnergy

/-!
# The `2πF` normalization and the energy bound for the quarter truncation

* `nnRadius_pos`, `cubeRadius_pos`, `cubeRadius_le`: `0 < r̃_p ≤ ¼` for `p ∈ C` (`C` locally finite);
* `closedBall_quarter_subset_cube`: if `r̃_p < ¼` then `B̄(p, ¼) ⊆ □_ℓ`;
* `two_pi_mul_cubeEnergy`: `2π F^{□_ℓ}(E, 1) = G^1_{□_ℓ}(r̃)` (book (11.2.6), `∫ f_η = π η² / 2`);
* `half_lintegral_quarter_le`: `½ ∫_{□_ℓ} |E_{1/4}|² ≤ 2π F^{□_ℓ}(E, 1) + c₀ #(C ∩ □_ℓ)` with
  `c₀ = π log 4 + π²/16` (`cQuarter 1`), from Lemma 4.13 with `α = r̃ ≤ β = ¼` (no Prop. 11.3).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

/-! ### The radii -/

theorem nnRadius_le (C : Set ℂ) (p : ℂ) : nnRadius C p ≤ 1 / 4 := by
  unfold nnRadius
  have h : sInf (insert 1 ((fun q => ‖q - p‖) '' (C \ {p}))) ≤ 1 :=
    csInf_le ⟨0, fun x hx => by
      rcases hx with rfl | ⟨q, -, rfl⟩
      · norm_num
      · exact norm_nonneg _⟩ (mem_insert 1 _)
  linarith

theorem nnRadius_pos {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) (p : ℂ) :
    0 < nnRadius C p := by
  set s := ((hC (‖p‖ + 1)).toFinset).erase p
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, ∀ q ∈ s, δ ≤ ‖q - p‖ := by
    rcases s.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun q hq => by simp [h] at hq⟩
    · obtain ⟨q0, hq0, hmin⟩ := s.exists_min_image (fun q => ‖q - p‖) h
      exact ⟨‖q0 - p‖, norm_pos_iff.2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hq0)), hmin⟩
  have hlow : ∀ x ∈ insert (1 : ℝ) ((fun q => ‖q - p‖) '' (C \ {p})), min δ 1 ≤ x := by
    rintro x (rfl | ⟨q, ⟨hqC, hqp⟩, rfl⟩)
    · exact min_le_right _ _
    · by_cases h1 : ‖q - p‖ < 1
      · refine (min_le_left _ _).trans (hδs q (Finset.mem_erase.2 ⟨hqp, ?_⟩))
        refine (hC _).mem_toFinset.2 ⟨hqC, mem_closedBall_zero_iff.2 ?_⟩
        have := norm_sub_norm_le q p
        linarith
      · exact (min_le_right _ _).trans (not_lt.1 h1)
  unfold nnRadius
  have := le_csInf ⟨1, mem_insert 1 _⟩ hlow
  have hpos : 0 < min δ 1 := lt_min hδ one_pos
  linarith

theorem cubeRadius_pos {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) (ℓ : ℝ) (p : ℂ) :
    0 < cubeRadius C ℓ p := by
  have hn := nnRadius_pos hC p
  unfold cubeRadius
  split_ifs with h1 h2
  · exact hn
  · norm_num
  · push Not at h1 h2
    have ht : 0 < infDist p (frontier (cube ℓ)) - 1 := by linarith [h2.2]
    have ht' : 0 < 1 - (infDist p (frontier (cube ℓ)) - 1) := by linarith [h1 h2.1]
    positivity

theorem cubeRadius_le (C : Set ℂ) (ℓ : ℝ) (p : ℂ) : cubeRadius C ℓ p ≤ 1 / 4 := by
  have hn := nnRadius_le C p
  unfold cubeRadius
  split_ifs with h1 h2
  · exact hn
  · exact le_rfl
  · push Not at h1 h2
    have ht : 0 ≤ infDist p (frontier (cube ℓ)) - 1 := by linarith [h2.2]
    nlinarith [mul_nonneg ht (sub_nonneg.2 hn)]

/-! ### Changed points are deep inside the square -/

theorem infDist_frontier_cube_le {ℓ : ℝ} {p : ℂ} (hp : p ∈ cube ℓ) :
    infDist p (frontier (cube ℓ)) ≤ ℓ / 2 - p.re ∧ infDist p (frontier (cube ℓ)) ≤ p.re + ℓ / 2 ∧
      infDist p (frontier (cube ℓ)) ≤ ℓ / 2 - p.im ∧
        infDist p (frontier (cube ℓ)) ≤ p.im + ℓ / 2 := by
  have hre : p.re ∈ Icc (-(ℓ / 2)) (ℓ / 2) := hp.1
  have him : p.im ∈ Icc (-(ℓ / 2)) (ℓ / 2) := hp.2
  have hℓ : -(ℓ / 2) ≤ ℓ / 2 := hre.1.trans hre.2
  have hfr : frontier (cube ℓ) = closure (Icc (-(ℓ / 2)) (ℓ / 2)) ×ℂ
      frontier (Icc (-(ℓ / 2)) (ℓ / 2)) ∪ frontier (Icc (-(ℓ / 2)) (ℓ / 2)) ×ℂ
        closure (Icc (-(ℓ / 2)) (ℓ / 2)) := Complex.frontier_reProdIm _ _
  rw [closure_Icc, frontier_Icc hℓ] at hfr
  have hmem : ∀ z : ℂ, (z.re = ℓ / 2 ∨ z.re = -(ℓ / 2)) → z.im ∈ Icc (-(ℓ / 2)) (ℓ / 2) →
      z ∈ frontier (cube ℓ) := fun z hz hzi => by
    rw [hfr]; right
    exact ⟨by rcases hz with h | h <;> simp [h], hzi⟩
  have hmem' : ∀ z : ℂ, (z.im = ℓ / 2 ∨ z.im = -(ℓ / 2)) → z.re ∈ Icc (-(ℓ / 2)) (ℓ / 2) →
      z ∈ frontier (cube ℓ) := fun z hz hzr => by
    rw [hfr]; left
    exact ⟨hzr, by rcases hz with h | h <;> simp [h]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := infDist_le_dist_of_mem (x := p)
      (hmem ⟨ℓ / 2, p.im⟩ (Or.inl rfl) him)
    rw [Complex.dist_of_im_eq (z := p) (w := ⟨ℓ / 2, p.im⟩) rfl, Real.dist_eq, abs_of_nonpos (by simp; linarith [hre.2])] at h
    simpa using h
  · have h := infDist_le_dist_of_mem (x := p)
      (hmem ⟨-(ℓ / 2), p.im⟩ (Or.inr rfl) him)
    rw [Complex.dist_of_im_eq (z := p) (w := ⟨-(ℓ / 2), p.im⟩) rfl, Real.dist_eq, abs_of_nonneg (by simp; linarith [hre.1])] at h
    simpa using h
  · have h := infDist_le_dist_of_mem (x := p)
      (hmem' ⟨p.re, ℓ / 2⟩ (Or.inl rfl) hre)
    rw [Complex.dist_of_re_eq (z := p) (w := ⟨p.re, ℓ / 2⟩) rfl, Real.dist_eq, abs_of_nonpos (by simp; linarith [him.2])] at h
    simpa using h
  · have h := infDist_le_dist_of_mem (x := p)
      (hmem' ⟨p.re, -(ℓ / 2)⟩ (Or.inr rfl) hre)
    rw [Complex.dist_of_re_eq (z := p) (w := ⟨p.re, -(ℓ / 2)⟩) rfl, Real.dist_eq, abs_of_nonneg (by simp; linarith [him.1])] at h
    simpa using h

/-- A point whose radius was decreased below `¼` sees its whole `¼`-ball inside `□_ℓ`. -/
theorem closedBall_quarter_subset_cube {C : Set ℂ} {ℓ : ℝ} {p : ℂ}
    (hp : cubeRadius C ℓ p < 1 / 4) : closedBall p (1 / 4) ⊆ cube ℓ := by
  have hdeep : p ∈ cube ℓ ∧ 1 < infDist p (frontier (cube ℓ)) := by
    unfold cubeRadius at hp
    split_ifs at hp with h1 h2
    · exact ⟨h1.1, by linarith [h1.2]⟩
    · norm_num at hp
    · push Not at h2; exact h2
  obtain ⟨h1, h2, h3, h4⟩ := infDist_frontier_cube_le hdeep.1
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  have hr := (Complex.abs_re_le_norm (x - p)).trans hx
  have hi := (Complex.abs_im_le_norm (x - p)).trans hx
  rw [Complex.sub_re, abs_le] at hr
  rw [Complex.sub_im, abs_le] at hi
  exact ⟨⟨by linarith [hdeep.2], by linarith [hdeep.2]⟩,
    ⟨by linarith [hdeep.2], by linarith [hdeep.2]⟩⟩

/-! ### The normalization -/

theorem finite_inter_cube {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) (ℓ : ℝ) :
    (C ∩ cube ℓ).Finite := by
  refine (hC |ℓ|).subset fun z hz => ⟨hz.1, mem_closedBall_zero_iff.2 ?_⟩
  have hre : |z.re| ≤ ℓ / 2 := abs_le.2 hz.2.1
  have him : |z.im| ≤ ℓ / 2 := abs_le.2 hz.2.2
  linarith [Complex.norm_le_abs_re_add_abs_im z, le_abs_self ℓ]

end Screening

open Screening in
/-- **`2π F^{□_ℓ}(E, 1) = G^1_{□_ℓ}(r̃)`** (book (11.2.6) with `c_{2,0} = 2π`, `∫ f_η = πη²/2`). -/
theorem two_pi_mul_cubeEnergy {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    (E : ℂ → ℂ) (ℓ : ℝ) :
    ((2 * Real.pi : ℝ) : EReal) * cubeEnergy C E ℓ =
      locEnergy 1 C (cubeRadius C ℓ) E (cube ℓ) := by
  have hfin := finite_inter_cube hC ℓ
  have hsum : 2 * π * ((-(1 / 2 : ℝ)) * (∑ᶠ p ∈ C ∩ cube ℓ, -Real.log (cubeRadius C ℓ p)) -
      ∑ᶠ p ∈ C ∩ cube ℓ, ∫ x, truncLog (cubeRadius C ℓ p) (x - p)) =
      ∑ᶠ p ∈ C ∩ cube ℓ, tauM 1 (cubeRadius C ℓ p) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_congr rfl fun p _ => integral_truncLog_sub (cubeRadius_pos hC ℓ p) p,
      Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold tauM
    ring
  unfold cubeEnergy locEnergy
  set L := ∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (cubeRadius C ℓ) E x‖ ^ 2)
  by_cases hL : L = ⊤
  · rw [hL, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by positivity), EReal.top_add_coe,
      EReal.coe_mul_top_of_pos (by positivity), EReal.coe_mul_top_of_pos (by norm_num),
      EReal.top_add_coe]
  · rw [← EReal.coe_ennreal_toReal hL, ← hsum]
    norm_cast
    field_simp
    ring

open Screening in
/-- **Energy bound** (no Prop. 11.3): `½ ∫_{□_ℓ} |E_{1/4}|² ≤ 2π F^{□_ℓ}(E, 1) + c₀ #(C ∩ □_ℓ)`. -/
theorem half_lintegral_quarter_le {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) {ℓ : ℝ}
    (_hℓ : 0 < ℓ) :
    ((1 / 2 : ℝ) : EReal) *
        (((∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)) : ℝ≥0∞) :
          EReal) ≤
      ((2 * Real.pi : ℝ) : EReal) * cubeEnergy C E ℓ +
        ((cQuarter 1 * (C ∩ cube ℓ).ncard : ℝ) : EReal) := by
  have hC := hE.1
  have hfin := finite_inter_cube hC ℓ
  have hcubeb : Bornology.IsBounded (cube ℓ) :=
    (isBounded_closedBall (x := (0 : ℂ)) (r := |ℓ|)).subset fun z hz =>
      mem_closedBall_zero_iff.2 (by
        have hre : |z.re| ≤ ℓ / 2 := abs_le.2 hz.1
        have him : |z.im| ≤ ℓ / 2 := abs_le.2 hz.2
        linarith [Complex.norm_le_abs_re_add_abs_im z, le_abs_self ℓ])
  have hcubem : MeasurableSet (cube ℓ) := (isClosed_Icc.reProdIm isClosed_Icc).measurableSet
  have hle := locEnergy_le isOpen_univ hcubem hcubeb hC (isChargeField_of_mem_elec hE univ)
    (α := cubeRadius C ℓ) (β := fun _ => 1 / 4) (fun p _ => cubeRadius_pos hC ℓ p)
    (fun p _ => cubeRadius_le C ℓ p) ⟨1 / 4, fun _ _ => le_rfl⟩
    (fun p _ hp => subset_inter (subset_univ _) (closedBall_quarter_subset_cube hp))
  rw [← two_pi_mul_cubeEnergy hC E ℓ] at hle
  have htau : ∑ᶠ p ∈ C ∩ cube ℓ, tauM 1 ((fun _ : ℂ => (1 / 4 : ℝ)) p) =
      -(cQuarter 1 * (C ∩ cube ℓ).ncard) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, Set.ncard_eq_toFinset_card _ hfin,
      nsmul_eq_mul, cQuarter]
    ring
  unfold locEnergy at hle
  rw [htau] at hle
  set X := ((1 / 2 : ℝ) : EReal) *
    (((∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)) : ℝ≥0∞) : EReal)
  set c : ℝ := cQuarter 1 * (C ∩ cube ℓ).ncard
  calc X = X + ((-c : ℝ) : EReal) + (c : EReal) := by
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
    _ ≤ ((2 * Real.pi : ℝ) : EReal) * cubeEnergy C E ℓ + (c : EReal) := by
        gcongr

end SandierSerfaty

end
