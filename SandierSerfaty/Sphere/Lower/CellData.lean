/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.SquareData

/-!
# Data attached to a grid cell (sphere note, Definition 6.8 and Lemma 6.6)

`Lower.exists_cell_data`: for a cell corner `a` with `a + [0,R]² ⊆ B(0, 2 s_n)` there are a side `t ∈ [R-1, R-1/2]`, an
integer `nb = ∫_{a+[0,t]²} m ≥ 1` with `m̄ = nb/t² ∈ [m₋, m₊]`, and a smooth `v` with `Δ v = 2π (m - m̄)`,
`∫_Q |∇v|² ≤ 121 π² m₊² R⁶ / s_n²`, and `|m - m̄| ≤ 4 m₊ R / s_n` on `Q`.
-/

open MeasureTheory Set Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem mean_mem_Icc {n : ℕ} (hn : 0 < n) {a : ℂ} {t : ℝ} (ht : 0 < t)
    (hQ : ∀ x ∈ sqAt a t, ‖x‖ ≤ 2 * blowupScale n) :
    mMinus ≤ (∫ x in sqAt a t, blowupDens n x) / t ^ 2 ∧
      (∫ x in sqAt a t, blowupDens n x) / t ^ 2 ≤ mPlus := by
  have hQm := measurableSet_sqAt a t
  have hfin : volume (sqAt a t) < ⊤ := lt_top_iff_ne_top.2 (volume_sqAt_ne_top a t)
  have hI : IntegrableOn (blowupDens n) (sqAt a t) :=
    integrableOn_sqAt (measurable_blowupDens n) (blowupDens_nonneg n) (blowupDens_le n) a t
  have hvol : volume.real (sqAt a t) = t ^ 2 := volume_real_sqAt a ht.le
  have h1 : mMinus * volume.real (sqAt a t) ≤ ∫ x in sqAt a t, blowupDens n x := by
    have := setIntegral_mono_on (integrableOn_const hfin.ne (C := mMinus)) hI hQm
      (fun x hx => (blowupDens_mem_Icc hn (hQ x hx)).1)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  have h2 : ∫ x in sqAt a t, blowupDens n x ≤ mPlus * volume.real (sqAt a t) := by
    have := setIntegral_mono_on hI (integrableOn_const hfin.ne (C := mPlus)) hQm
      (fun x hx => (blowupDens_mem_Icc hn (hQ x hx)).2)
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at this
  rw [hvol] at h1 h2
  have ht2 : 0 < t ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ ht2]; linarith
  · rw [div_le_iff₀ ht2]; linarith

theorem exists_cell_data {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 2 ≤ R) (hbig : 1 ≤ mMinus * (R - 3 / 4)) (a : ℂ)
    (hQ : ∀ x ∈ sqAt a R, ‖x‖ ≤ 2 * blowupScale n) :
    ∃ (t : ℝ) (nb : ℕ) (v : ℂ → ℝ), R - 1 ≤ t ∧ t ≤ R - 1 / 2 ∧ (nb : ℝ) = ∫ x in sqAt a t, blowupDens n x ∧
      ContDiff ℝ ∞ v ∧ (∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - nb / t ^ 2)) ∧
      ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 ≤ 121 * Real.pi ^ 2 * mPlus ^ 2 * R ^ 6 / blowupScale n ^ 2 ∧
      mMinus ≤ nb / t ^ 2 ∧ nb / t ^ 2 ≤ mPlus ∧
      (∀ x ∈ sqAt a t, |blowupDens n x - nb / t ^ 2| ≤ 4 * mPlus * R / blowupScale n) ∧ 1 ≤ nb := by
  have hlow : ∀ x ∈ sqAt a (R - 1 / 2), mMinus ≤ blowupDens n x := fun x hx =>
    (blowupDens_mem_Icc hn (hQ x (sqAt_mono a (by linarith) hx))).1
  obtain ⟨⟨ht1, ht2⟩, k, hk⟩ := qSide_spec n (by linarith) hlow hbig
  set t := qSide n R a with htdef
  have ht0 : 0 < t := by linarith
  have hmass : (sqMassNat n a t : ℝ) = ∫ x in sqAt a t, blowupDens n x := sqMassNat_spec hk
  have hQt : ∀ x ∈ sqAt a t, ‖x‖ ≤ 2 * blowupScale n := fun x hx => hQ x (sqAt_mono a (by linarith) hx)
  obtain ⟨v, hv, hΔ, hgrad⟩ := exists_square_data (a := a) hn ht0 (by linarith : t ≤ R)
  have hmean := mean_mem_Icc hn ht0 hQt
  rw [← hmass] at hmean hΔ
  refine ⟨t, sqMassNat n a t, v, ht1, ht2, hmass, hv, hΔ, hgrad, hmean.1, hmean.2, ?_, ?_⟩
  · intro x hx
    rw [hmass] at *
    exact (abs_blowupDens_sub_mean_le hn ht0 hx).trans (by
      have := mPlus_pos
      have := blowupScale_pos hn
      gcongr
      linarith)
  · have h1 : mMinus ≤ (sqMassNat n a t : ℝ) / t ^ 2 := hmean.1
    have ht2' : 0 < t ^ 2 := by positivity
    rw [le_div_iff₀ ht2'] at h1
    have hge : 1 ≤ (sqMassNat n a t : ℝ) := by
      have h3 : 1 ≤ mMinus * (R - 3 / 4) := hbig
      have hm1 : mMinus ≤ 1 / 150 := mMinus_le_mPlus.trans mPlus_lt.le
      have hR3 : 150 ≤ R - 3 / 4 := by
        by_contra hlt
        rw [not_le] at hlt
        nlinarith [mMinus_pos]
      have h4 : R - 3 / 4 ≤ t ^ 2 := by nlinarith
      nlinarith [mMinus_pos]
    exact_mod_cast hge

end Lower

end Sphere

end SandierSerfaty

end
