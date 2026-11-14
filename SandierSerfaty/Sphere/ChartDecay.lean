/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.ChartLaplacian

/-!
# Decay of the chart potential at infinity (sphere note, Definition 3.3)

For `X` with `‖xᵢ‖ ≤ M` and `‖x‖ ≥ 8 (1 + M)²`:

* `Sphere.abs_chartPot_le`: `|h_X x| ≤ 4 n (1 + M)² / ‖x‖`;
* `Sphere.norm_fderiv_chartPot_le`: `‖∇h_X x‖ ≤ 16 n (1 + M)² / ‖x‖²`.
-/

open Laplacian Filter Topology InnerProductSpace
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem abs_log_le_two_mul {r : ℝ} (hr : 0 < r) (h : |r - 1| ≤ 1 / 2) : |Real.log r| ≤ 2 * |r - 1| := by
  have hr2 : 1 / 2 ≤ r := by
    have := (abs_le.1 h).1; linarith
  rcases le_total 1 r with h1 | h1
  · have h0 : 0 ≤ Real.log r := Real.log_nonneg h1
    rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    linarith [Real.log_le_sub_one_of_pos hr]
  · have h0 : Real.log r ≤ 0 := Real.log_nonpos hr.le h1
    rw [abs_of_nonpos h0, abs_of_nonpos (by linarith)]
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
    rw [Real.log_inv] at h2
    have h3 : r⁻¹ - 1 ≤ 2 * (1 - r) := by
      rw [inv_eq_one_div, div_sub_one hr.ne', div_le_iff₀ hr]
      linarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 2 * r - 1)]
    linarith

theorem norm_sub_ge {x p : ℂ} {M : ℝ} (hp : ‖p‖ ≤ M) (hx : 2 * M ≤ ‖x‖) : ‖x‖ / 2 ≤ ‖x - p‖ := by
  have := norm_sub_norm_le x p
  linarith

theorem abs_log_term_le {x p : ℂ} {M : ℝ} (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hx : 8 * (1 + M) ^ 2 ≤ ‖x‖) :
    |potV x / 2 - Real.log ‖x - p‖| ≤ 4 * (1 + M) ^ 2 / ‖x‖ := by
  have hM1 : 1 ≤ (1 + M) ^ 2 := by linarith [sq_nonneg M]
  have hx1 : 8 ≤ ‖x‖ := by linarith
  have hxpos : 0 < ‖x‖ := by linarith
  have hx2 : 2 * M ≤ ‖x‖ := by linarith [sq_nonneg M]
  have h1 := norm_sub_ge hp hx2
  have hd : 0 < ‖x - p‖ := by linarith
  set r : ℝ := (1 + ‖x‖ ^ 2) / ‖x - p‖ ^ 2 with hr
  have hrpos : 0 < r := by positivity
  have hlog : potV x / 2 - Real.log ‖x - p‖ = Real.log r / 2 := by
    rw [hr, Real.log_div (by positivity) (by positivity), Real.log_pow]
    unfold potV; push_cast; ring
  -- `|r - 1| ≤ 4 (1 + M)² / ‖x‖`
  have hsq : ‖x - p‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x p + ‖p‖ ^ 2 := by
    rw [norm_sub_sq_real]
  have hin : |inner ℝ x p| ≤ ‖x‖ * M := by
    refine (abs_real_inner_le_norm x p).trans ?_
    exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  have hnum : |1 + ‖x‖ ^ 2 - ‖x - p‖ ^ 2| ≤ 1 + 2 * ‖x‖ * M + M ^ 2 := by
    rw [hsq]
    have : 1 + ‖x‖ ^ 2 - (‖x‖ ^ 2 - 2 * inner ℝ x p + ‖p‖ ^ 2) = 1 + 2 * inner ℝ x p - ‖p‖ ^ 2 := by
      ring
    rw [this]
    have h2 : ‖p‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
    have h3 := abs_le.1 hin
    rw [abs_le]
    constructor <;> linarith [h3.1, h3.2, sq_nonneg ‖p‖, sq_nonneg M]
  have hden : ‖x‖ ^ 2 / 4 ≤ ‖x - p‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2; linarith
  have hr1 : r - 1 = (1 + ‖x‖ ^ 2 - ‖x - p‖ ^ 2) / ‖x - p‖ ^ 2 := by
    rw [hr]; field_simp
  have hbd : |r - 1| ≤ 4 * (1 + M) ^ 2 / ‖x‖ := by
    rw [hr1, abs_div, abs_of_pos (by positivity : 0 < ‖x - p‖ ^ 2), div_le_div_iff₀ (by positivity) hxpos]
    calc |1 + ‖x‖ ^ 2 - ‖x - p‖ ^ 2| * ‖x‖
        ≤ (1 + 2 * ‖x‖ * M + M ^ 2) * ‖x‖ := mul_le_mul_of_nonneg_right hnum hxpos.le
      _ ≤ (4 * (1 + M) ^ 2) * (‖x‖ ^ 2 / 4) := by
          have hxx : ‖x‖ * 1 ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left (by linarith) hxpos.le
          linarith [mul_le_mul_of_nonneg_left hxx (sq_nonneg M)]
      _ ≤ (4 * (1 + M) ^ 2) * ‖x - p‖ ^ 2 := mul_le_mul_of_nonneg_left hden (by positivity)
  have hhalf : 4 * (1 + M) ^ 2 / ‖x‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hxpos]; linarith
  rw [hlog, abs_div, abs_two]
  have := abs_log_le_two_mul hrpos (hbd.trans hhalf)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc |Real.log r| ≤ 2 * |r - 1| := this
    _ ≤ 2 * (4 * (1 + M) ^ 2 / ‖x‖) := by linarith
    _ = 4 * (1 + M) ^ 2 / ‖x‖ * 2 := by ring

theorem abs_chartPot_le {n : ℕ} (X : Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M) (hX : ∀ i, ‖X i‖ ≤ M) {x : ℂ}
    (hx : 8 * (1 + M) ^ 2 ≤ ‖x‖) :
    |chartPot X x| ≤ n * (4 * (1 + M) ^ 2 / ‖x‖) := by
  have e : chartPot X x = ∑ i, (potV x / 2 - Real.log ‖x - X i‖) := by
    unfold chartPot gKer
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Finset.sum_neg_distrib]
    ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |potV x / 2 - Real.log ‖x - X i‖| ≤ ∑ _i : Fin n, 4 * (1 + M) ^ 2 / ‖x‖ :=
        Finset.sum_le_sum fun i _ => abs_log_term_le hM (hX i) hx
    _ = n * (4 * (1 + M) ^ 2 / ‖x‖) := by simp

theorem hasFDerivAt_chartPot {n : ℕ} (X : Fin n → ℂ) {x : ℂ} (hx : ∀ i, x ≠ X i) :
    HasFDerivAt (chartPot X)
      (∑ i, ((1 + ‖x‖ ^ 2)⁻¹ • innerSL ℝ x - (‖x - X i‖ ^ 2)⁻¹ • innerSL ℝ (x - X i))) x := by
  have hg : ∀ i ∈ Finset.univ, HasFDerivAt (fun y : ℂ => gKer (y - X i))
      (-((‖x - X i‖ ^ 2)⁻¹ • innerSL ℝ (x - X i))) x := fun i _ =>
    (Torus.hasFDerivAt_log_norm_sub (hx i)).neg
  have hs := HasFDerivAt.sum hg
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using ((hasFDerivAt_id x).norm_sq).const_add 1
  have hV : HasFDerivAt potV ((1 + ‖x‖ ^ 2)⁻¹ • (2 • innerSL ℝ x)) x :=
    h1.log (by positivity)
  have h2 := hs.add (hV.const_mul ((n : ℝ) / 2))
  have e : chartPot X = fun y => ∑ i, gKer (y - X i) + (n : ℝ) / 2 * potV y := rfl
  rw [e]
  have hder : (∑ i, ((1 + ‖x‖ ^ 2)⁻¹ • innerSL ℝ x - (‖x - X i‖ ^ 2)⁻¹ • innerSL ℝ (x - X i))) =
      ∑ i, -((‖x - X i‖ ^ 2)⁻¹ • innerSL ℝ (x - X i)) +
        ((n : ℝ) / 2) • ((1 + ‖x‖ ^ 2)⁻¹ • 2 • innerSL ℝ x) := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
    simp only [two_smul]
    module
  rw [hder]
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [Finset.sum_apply]

theorem norm_fderiv_chartPot_term_le {x p : ℂ} {M : ℝ} (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hx : 8 * (1 + M) ^ 2 ≤ ‖x‖) :
    ‖(1 + ‖x‖ ^ 2)⁻¹ • innerSL ℝ x - (‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p)‖ ≤
      16 * (1 + M) ^ 2 / ‖x‖ ^ 2 := by
  have hM1 : 1 ≤ (1 + M) ^ 2 := by linarith [sq_nonneg M]
  have hx1 : 8 ≤ ‖x‖ := by linarith
  have hxpos : 0 < ‖x‖ := by linarith
  have hx2 : 2 * M ≤ ‖x‖ := by linarith [sq_nonneg M]
  have h1 := norm_sub_ge hp hx2
  have hd : 0 < ‖x - p‖ := by linarith
  have hden : ‖x‖ ^ 2 / 4 ≤ ‖x - p‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2; linarith
  -- rewrite as the inner-product functional of a vector
  have e : (1 + ‖x‖ ^ 2)⁻¹ • innerSL ℝ x - (‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p) =
      innerSL ℝ ((1 + ‖x‖ ^ 2)⁻¹ • x - (‖x - p‖ ^ 2)⁻¹ • (x - p)) := by
    simp only [map_sub, map_smulₛₗ, conj_trivial]
  rw [e, innerSL_apply_norm]
  set a : ℝ := (1 + ‖x‖ ^ 2)⁻¹ with ha
  set b : ℝ := (‖x - p‖ ^ 2)⁻¹ with hb
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  have hveq : a • x - b • (x - p) = (a * b) • (‖x - p‖ ^ 2 • x - (1 + ‖x‖ ^ 2) • (x - p)) := by
    have h1 : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    have h2 : ‖x - p‖ ^ 2 ≠ 0 := by positivity
    simp only [ha, hb, smul_sub, smul_smul]
    congr 1
    · field_simp
    · field_simp
  rw [hveq, norm_smul, Real.norm_of_nonneg (by positivity)]
  -- the numerator
  have hsq : ‖x - p‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x p + ‖p‖ ^ 2 := by rw [norm_sub_sq_real]
  have hin : |inner ℝ x p| ≤ ‖x‖ * M :=
    (abs_real_inner_le_norm x p).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  have hnum : ‖‖x - p‖ ^ 2 • x - (1 + ‖x‖ ^ 2) • (x - p)‖ ≤ 4 * (1 + M) ^ 2 * ‖x‖ ^ 2 := by
    have e2 : ‖x - p‖ ^ 2 • x - (1 + ‖x‖ ^ 2) • (x - p) =
        (‖x - p‖ ^ 2 - (1 + ‖x‖ ^ 2)) • x + (1 + ‖x‖ ^ 2) • p := by
      simp only [smul_sub, sub_smul]; abel
    rw [e2]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hc : |‖x - p‖ ^ 2 - (1 + ‖x‖ ^ 2)| ≤ 1 + 2 * ‖x‖ * M + M ^ 2 := by
      rw [hsq]
      have : ‖x‖ ^ 2 - 2 * inner ℝ x p + ‖p‖ ^ 2 - (1 + ‖x‖ ^ 2) =
          -(1 + 2 * inner ℝ x p - ‖p‖ ^ 2) := by ring
      rw [this, abs_neg]
      have h2 : ‖p‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      have h3 := abs_le.1 hin
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2, sq_nonneg ‖p‖, sq_nonneg M]
    have hc2 : |1 + ‖x‖ ^ 2| = 1 + ‖x‖ ^ 2 := abs_of_pos (by positivity)
    rw [hc2]
    have := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
    have hxx : ‖x‖ * 1 ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left (by linarith) hxpos.le
    linarith [mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2),
      mul_le_mul_of_nonneg_left hxx hM, mul_le_mul_of_nonneg_left hxx (sq_nonneg M),
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ ‖x‖) hM,
      mul_nonneg (sq_nonneg M) hxpos.le]
  have hab : a * b ≤ 1 / ‖x‖ ^ 2 * (4 / ‖x‖ ^ 2) := by
    refine mul_le_mul ?_ ?_ hbpos.le (by positivity)
    · rw [ha, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    · rw [hb, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
  calc a * b * ‖‖x - p‖ ^ 2 • x - (1 + ‖x‖ ^ 2) • (x - p)‖
      ≤ (1 / ‖x‖ ^ 2 * (4 / ‖x‖ ^ 2)) * (4 * (1 + M) ^ 2 * ‖x‖ ^ 2) :=
        mul_le_mul hab hnum (norm_nonneg _) (by positivity)
    _ = 16 * (1 + M) ^ 2 / ‖x‖ ^ 2 := by field_simp; ring

theorem norm_fderiv_chartPot_le {n : ℕ} (X : Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hX : ∀ i, ‖X i‖ ≤ M) {x : ℂ} (hx : 8 * (1 + M) ^ 2 ≤ ‖x‖) :
    ‖fderiv ℝ (chartPot X) x‖ ≤ n * (16 * (1 + M) ^ 2 / ‖x‖ ^ 2) := by
  have hM1 : 1 ≤ (1 + M) ^ 2 := by linarith [sq_nonneg M]
  have hxi : ∀ i, x ≠ X i := fun i h => by
    have := hX i
    rw [← h] at this
    linarith [sq_nonneg M]
  rw [(hasFDerivAt_chartPot X hxi).fderiv]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(1 + ‖x‖ ^ 2)⁻¹ • innerSL ℝ x - (‖x - X i‖ ^ 2)⁻¹ • innerSL ℝ (x - X i)‖
      ≤ ∑ _i : Fin n, 16 * (1 + M) ^ 2 / ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => norm_fderiv_chartPot_term_le hM (hX i) hx
    _ = n * (16 * (1 + M) ^ 2 / ‖x‖ ^ 2) := by simp

end Sphere

end SandierSerfaty

end
