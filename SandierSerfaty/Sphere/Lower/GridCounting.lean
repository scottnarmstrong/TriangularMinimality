/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GridFamily
public import SandierSerfaty.Sphere.Lower.GoodSquareAux

/-!
# Counting `1`-separated points in the pieces of the grid (sphere note, Theorem 6.14, error budget)

Three applications of Lemma 6.5 (`Lower.card_filter_mul_le_volume`), for a finite `1`-separated set `S ⊆ ℂ`:

* `Lower.card_filter_sqAt_le`: `#(S ∩ (a + [0,t]²)) · π/4 ≤ (t+1)²`;
* `Lower.card_filter_leftover_le`: `#(S ∩ (K̄ ∖ Q)) ≤ 7 R` for `Q = a + [0,t]²`, `K̄ = a + [0,R]²`, `t ∈ [R-1, R-1/2]`;
* `Lower.card_filter_annulus_le`: `#(S ∩ {ρ - 1 - 2R < |z| < ρ}) ≤ 16 ρ (R+1)`.
-/

open MeasureTheory Set Metric
open scoped ENNReal Pointwise Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem card_mul_le_of_volume {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) (A : Set ℂ)
    {B : ℝ} (hB : 0 ≤ B) (hvol : volume (A + ball (0 : ℂ) (1 / 2)) ≤ ENNReal.ofReal B) :
    ((S.filter (· ∈ A)).card : ℝ) * (Real.pi / 4) ≤ B := by
  have h3 := (card_filter_mul_le_volume hS A).trans hvol
  have h5 : ENNReal.ofReal (((S.filter (· ∈ A)).card : ℝ) * (Real.pi / 4)) ≤ ENNReal.ofReal B := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    convert h3
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h5

theorem card_le_of_mul_le {c B : ℝ} {k : ℝ} (_hk0 : 0 ≤ k) (h : k * (Real.pi / 4) ≤ B) (hc : 4 * B / Real.pi ≤ c) :
    k ≤ c := by
  have hpi := Real.pi_pos
  have : k ≤ 4 * B / Real.pi := by
    rw [le_div_iff₀ hpi]; nlinarith
  exact this.trans hc

theorem sqAt_add_ball_subset (a : ℂ) (t : ℝ) :
    sqAt a t + ball (0 : ℂ) (1 / 2) ⊆ sqAt (a - ⟨1 / 2, 1 / 2⟩) (t + 1) := by
  intro w hw
  obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_add.1 hw
  have hb' : ‖b‖ < 1 / 2 := by simpa using hb
  have hbr : |b.re| ≤ 1 / 2 := (Complex.abs_re_le_norm b).trans hb'.le
  have hbi : |b.im| ≤ 1 / 2 := (Complex.abs_im_le_norm b).trans hb'.le
  rw [abs_le] at hbr hbi
  rw [mem_sqAt] at hp ⊢
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem card_filter_sqAt_le {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) (a : ℂ) {t : ℝ}
    (ht : 0 ≤ t) : ((S.filter (· ∈ sqAt a t)).card : ℝ) * (Real.pi / 4) ≤ (t + 1) ^ 2 := by
  refine card_mul_le_of_volume hS _ (by positivity) ?_
  refine (measure_mono (sqAt_add_ball_subset a t)).trans ?_
  rw [volume_sqAt, ← ENNReal.ofReal_mul (by linarith)]
  exact le_of_eq (by congr 1; ring)

theorem leftover_add_ball_subset (a : ℂ) {R t : ℝ} :
    (sqAt a R \ sqAt a t) + ball (0 : ℂ) (1 / 2) ⊆
      sqAt (a - ⟨1 / 2, 1 / 2⟩) (R + 1) \ sqAt a (t - 1 / 2) := by
  intro w hw
  obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_add.1 hw
  have hb' : ‖b‖ < 1 / 2 := by simpa using hb
  have hbr : |b.re| ≤ 1 / 2 := (Complex.abs_re_le_norm b).trans hb'.le
  have hbi : |b.im| ≤ 1 / 2 := (Complex.abs_im_le_norm b).trans hb'.le
  rw [abs_le] at hbr hbi
  obtain ⟨hp1, hp2⟩ := hp
  constructor
  · exact sqAt_add_ball_subset a R (Set.add_mem_add hp1 (mem_ball_zero_iff.2 hb'))
  · intro hq
    apply hp2
    rw [mem_sqAt] at hq hp1 ⊢
    simp only [Complex.add_re, Complex.add_im] at hq
    obtain ⟨q1, q2, q3, q4⟩ := hq
    obtain ⟨p1, p2, p3, p4⟩ := hp1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem card_filter_leftover_le {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) (a : ℂ)
    {R t : ℝ} (hR : 2 ≤ R) (ht1 : R - 1 ≤ t) (ht2 : t ≤ R - 1 / 2) :
    ((S.filter (· ∈ sqAt a R \ sqAt a t)).card : ℝ) ≤ 7 * R := by
  have hsub := leftover_add_ball_subset a (R := R) (t := t)
  have hT : sqAt a (t - 1 / 2) ⊆ sqAt (a - ⟨1 / 2, 1 / 2⟩) (R + 1) := by
    intro z hz
    rw [mem_sqAt] at hz ⊢
    simp only [Complex.sub_re, Complex.sub_im]
    exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1], by linarith [hz.2.2.2]⟩
  have hvol : volume ((sqAt a R \ sqAt a t) + ball (0 : ℂ) (1 / 2)) ≤ ENNReal.ofReal (5 * R) := by
    refine (measure_mono hsub).trans ?_
    rw [← ofReal_measureReal (ne_top_of_le_ne_top (volume_sqAt_ne_top (a - ⟨1 / 2, 1 / 2⟩) (R + 1))
      (measure_mono Set.sdiff_subset))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [measureReal_sdiff hT (measurableSet_sqAt _ _) (volume_sqAt_ne_top _ _),
      volume_real_sqAt _ (by linarith), volume_real_sqAt _ (by linarith)]
    nlinarith
  have h0 := card_mul_le_of_volume hS _ (by linarith) hvol
  have h : ((S.filter (· ∈ sqAt a R \ sqAt a t)).card : ℝ) * (Real.pi / 4) ≤ 5 * R := by convert h0
  refine card_le_of_mul_le (Nat.cast_nonneg _) h ?_
  have hpi := Real.pi_gt_three
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith

theorem annulus_add_ball_subset {ρ R : ℝ} (_hρ : 1 ≤ ρ) :
    {z : ℂ | ρ - 1 - 2 * R < ‖z‖ ∧ ‖z‖ < ρ} + ball (0 : ℂ) (1 / 2) ⊆
      ball (0 : ℂ) (ρ + 1 / 2) \ ball (0 : ℂ) (max (ρ - 2 * R - 3 / 2) 0) := by
  intro w hw
  obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_add.1 hw
  have hb' : ‖b‖ < 1 / 2 := by simpa using hb
  obtain ⟨h1, h2⟩ := hp
  have h3 : ‖p + b‖ ≤ ‖p‖ + ‖b‖ := norm_add_le _ _
  have h4 : ‖p‖ ≤ ‖p + b‖ + ‖b‖ := by
    have := norm_sub_le (p + b) b
    simpa using this
  constructor
  · rw [mem_ball, dist_zero_right]; linarith
  · rw [mem_ball, dist_zero_right, not_lt]
    refine max_le (by linarith) (norm_nonneg _)

theorem volume_ball_zero {r : ℝ} (hr : 0 ≤ r) : volume (ball (0 : ℂ) r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

theorem card_filter_annulus_le {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) {ρ R : ℝ}
    (hρ : 1 ≤ ρ) (hR : 0 ≤ R) :
    ((S.filter (fun z => ρ - 1 - 2 * R < ‖z‖ ∧ ‖z‖ < ρ)).card : ℝ) ≤ 16 * ρ * (R + 1) := by
  set r₀ := max (ρ - 2 * R - 3 / 2) 0 with hr₀
  have hr₀0 : 0 ≤ r₀ := le_max_right _ _
  have hr₀1 : r₀ ≤ ρ + 1 / 2 := max_le (by linarith) (by linarith)
  have hsub := annulus_add_ball_subset (ρ := ρ) (R := R) hρ
  have hpi := Real.pi_pos
  have hbound : Real.pi * (ρ + 1 / 2) ^ 2 - Real.pi * r₀ ^ 2 ≤ 4 * Real.pi * ρ * (R + 1) := by
    rcases max_cases (ρ - 2 * R - 3 / 2) 0 with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [hr₀, h]
      have : (ρ + 1 / 2) ^ 2 - (ρ - 2 * R - 3 / 2) ^ 2 ≤ 4 * ρ * (R + 1) := by nlinarith
      nlinarith
    · rw [hr₀, h]
      have : (ρ + 1 / 2) ^ 2 ≤ 4 * ρ * (R + 1) := by nlinarith
      nlinarith
  have hvol : volume ({z : ℂ | ρ - 1 - 2 * R < ‖z‖ ∧ ‖z‖ < ρ} + ball (0 : ℂ) (1 / 2)) ≤
      ENNReal.ofReal (4 * Real.pi * ρ * (R + 1)) := by
    refine (measure_mono hsub).trans ?_
    have hfin : volume (ball (0 : ℂ) r₀) ≠ ⊤ := by
      rw [volume_ball_zero hr₀0]; exact ENNReal.ofReal_ne_top
    rw [measure_sdiff (ball_subset_ball hr₀1) (measurableSet_ball.nullMeasurableSet) hfin,
      volume_ball_zero (by linarith), volume_ball_zero hr₀0,
      ← ENNReal.ofReal_sub _ (by positivity)]
    exact ENNReal.ofReal_le_ofReal hbound
  have h0 := card_mul_le_of_volume hS _ (by positivity) hvol
  have h : ((S.filter (fun z => ρ - 1 - 2 * R < ‖z‖ ∧ ‖z‖ < ρ)).card : ℝ) * (Real.pi / 4) ≤
      4 * Real.pi * ρ * (R + 1) := by
    convert h0 using 5
    exact Iff.rfl
  refine card_le_of_mul_le (Nat.cast_nonneg _) h ?_
  rw [div_le_iff₀ hpi]
  nlinarith

end Lower

end Sphere

end SandierSerfaty

end
