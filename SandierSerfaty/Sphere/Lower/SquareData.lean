/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GridFamily
public import SandierSerfaty.Sphere.Lower.ChartPartitionAux

/-!
# The density freeze on a quantized square (data for Proposition 6.13)

For `Q = a + [0,t]²` with `0 < t ≤ R` and `m̄ = (∫_Q m)/t²`:

* `Lower.abs_blowupDens_sub_mean_le`: `|m(x) - m̄| ≤ 4 m₊ t / s_n` on `Q` (the density is `2m₊/s_n`-Lipschitz);
* `Lower.exists_square_data`: a smooth `v` with `Δ v = 2π (m - m̄)` and `∫_Q |∇ v|² ≤ 121 π² m₊² R⁶ / s_n²`.
-/

open MeasureTheory Set Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem norm_sub_le_of_mem_sqAt {a x y : ℂ} {t : ℝ} (hx : x ∈ sqAt a t) (hy : y ∈ sqAt a t) :
    ‖x - y‖ ≤ 2 * t := by
  rw [mem_sqAt] at hx hy
  have h1 : |(x - y).re| ≤ t := by
    rw [Complex.sub_re, abs_le]; constructor <;> linarith [hx.1, hx.2.1, hy.1, hy.2.1]
  have h2 : |(x - y).im| ≤ t := by
    rw [Complex.sub_im, abs_le]; constructor <;> linarith [hx.2.2.1, hx.2.2.2, hy.2.2.1, hy.2.2.2]
  have := Complex.norm_le_abs_re_add_abs_im (x - y)
  linarith

theorem abs_blowupDens_sub_mean_le {n : ℕ} (hn : 0 < n) {a x : ℂ} {t : ℝ} (ht : 0 < t) (hx : x ∈ sqAt a t) :
    |blowupDens n x - (∫ y in sqAt a t, blowupDens n y) / t ^ 2| ≤ 4 * mPlus * t / blowupScale n := by
  have hs := blowupScale_pos hn
  have hQm := measurableSet_sqAt a t
  have hI : IntegrableOn (blowupDens n) (sqAt a t) :=
    integrableOn_sqAt (measurable_blowupDens n) (blowupDens_nonneg n) (blowupDens_le n) a t
  have hvol : volume.real (sqAt a t) = t ^ 2 := volume_real_sqAt a ht.le
  have hfin : volume (sqAt a t) < ⊤ := lt_top_iff_ne_top.2 (volume_sqAt_ne_top a t)
  have h1 : ∫ y in sqAt a t, (blowupDens n x - blowupDens n y) =
      t ^ 2 * blowupDens n x - ∫ y in sqAt a t, blowupDens n y := by
    rw [integral_sub (integrableOn_const hfin.ne) hI, setIntegral_const, smul_eq_mul, hvol]
  have h2 : ‖∫ y in sqAt a t, (blowupDens n x - blowupDens n y)‖ ≤
      (4 * mPlus * t / blowupScale n) * volume.real (sqAt a t) := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun y hy => ?_
    rw [Real.norm_eq_abs]
    calc |blowupDens n x - blowupDens n y| ≤ 2 * mPlus * ‖x - y‖ / blowupScale n :=
          abs_blowupDens_sub_le hn x y
      _ ≤ 2 * mPlus * (2 * t) / blowupScale n := by
          have := mPlus_pos
          gcongr
          exact norm_sub_le_of_mem_sqAt hx hy
      _ = 4 * mPlus * t / blowupScale n := by ring
  rw [h1, hvol, Real.norm_eq_abs] at h2
  have e : blowupDens n x - (∫ y in sqAt a t, blowupDens n y) / t ^ 2 =
      (t ^ 2 * blowupDens n x - ∫ y in sqAt a t, blowupDens n y) / t ^ 2 := by
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
  linarith

theorem exists_square_data {n : ℕ} (hn : 0 < n) {a : ℂ} {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧
      (∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - (∫ y in sqAt a t, blowupDens n y) / t ^ 2)) ∧
      ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 ≤ 121 * Real.pi ^ 2 * mPlus ^ 2 * R ^ 6 / blowupScale n ^ 2 := by
  have hs := blowupScale_pos hn
  have hpi := Real.pi_pos
  have hmp := mPlus_pos
  have hR0 : 0 < R := lt_of_lt_of_le ht htR
  set mb := (∫ y in sqAt a t, blowupDens n y) / t ^ 2 with hmb
  set q : ℂ := a + ⟨t / 2, t / 2⟩ with hq
  have hqQ : q ∈ sqAt a t := by
    rw [mem_sqAt]
    simp only [hq, Complex.add_re, Complex.add_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨v, hv, hΔ, hgrad⟩ := exists_density_freeze hn q mb
  refine ⟨v, hv, hΔ, ?_⟩
  have hδq := abs_blowupDens_sub_mean_le hn ht hqQ
  have hQm := measurableSet_sqAt a t
  have hfin : volume (sqAt a t) < ⊤ := lt_top_iff_ne_top.2 (volume_sqAt_ne_top a t)
  have hbound : ∀ x ∈ sqAt a t, ‖gradC v x‖ ^ 2 ≤ (11 * Real.pi * mPlus * R ^ 2 / blowupScale n) ^ 2 := by
    intro x hx
    rw [← gradient_eq_gradC]
    have h1 := hgrad x
    have hxq : ‖x - q‖ ≤ R := by
      have := norm_sub_le_of_mem_sqAt hx hqQ
      -- `‖x - q‖ ≤ t` since `q` is the center
      rw [mem_sqAt] at hx
      have h2 : |(x - q).re| ≤ t / 2 := by
        simp only [hq, Complex.sub_re, Complex.add_re]
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2.1]
      have h3 : |(x - q).im| ≤ t / 2 := by
        simp only [hq, Complex.sub_im, Complex.add_im]
        rw [abs_le]; constructor <;> linarith [hx.2.2.1, hx.2.2.2]
      have := Complex.norm_le_abs_re_add_abs_im (x - q)
      linarith
    have hxq0 := norm_nonneg (x - q)
    have hδ' : |blowupDens n q - mb| ≤ 4 * mPlus * R / blowupScale n :=
      hδq.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htR (by positivity)) hs.le)
    have h2 : ‖gradient v x‖ ≤ 11 * Real.pi * mPlus * R ^ 2 / blowupScale n := by
      refine h1.trans ?_
      have e1 : 7 * Real.pi * mPlus * ‖x - q‖ ^ 2 / blowupScale n ≤ 7 * Real.pi * mPlus * R ^ 2 / blowupScale n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxq0 hxq 2) (by positivity)) hs.le
      have e2 : Real.pi * |blowupDens n q - mb| * ‖x - q‖ ≤ Real.pi * (4 * mPlus * R / blowupScale n) * R :=
        mul_le_mul (mul_le_mul_of_nonneg_left hδ' hpi.le) hxq hxq0 (by positivity)
      have e3 : Real.pi * (4 * mPlus * R / blowupScale n) * R = 4 * Real.pi * mPlus * R ^ 2 / blowupScale n := by
        field_simp
      have e4 : 7 * Real.pi * mPlus * R ^ 2 / blowupScale n + 4 * Real.pi * mPlus * R ^ 2 / blowupScale n =
          11 * Real.pi * mPlus * R ^ 2 / blowupScale n := by ring
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h3 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := sqAt a t) hfin
    (C := (11 * Real.pi * mPlus * R ^ 2 / blowupScale n) ^ 2) (f := fun x => ‖gradC v x‖ ^ 2)
    (fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbound x hx)
  rw [volume_real_sqAt a ht.le] at h3
  calc ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 ≤ ‖∫ x in sqAt a t, ‖gradC v x‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ (11 * Real.pi * mPlus * R ^ 2 / blowupScale n) ^ 2 * t ^ 2 := h3
    _ ≤ (11 * Real.pi * mPlus * R ^ 2 / blowupScale n) ^ 2 * R ^ 2 := by
        gcongr
    _ = 121 * Real.pi ^ 2 * mPlus ^ 2 * R ^ 6 / blowupScale n ^ 2 := by
        field_simp; ring

end Lower

end Sphere

end SandierSerfaty

end
