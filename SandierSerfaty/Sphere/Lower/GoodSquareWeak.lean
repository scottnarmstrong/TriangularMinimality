/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Discrepancy
public import SandierSerfaty.Analysis.WeylCalculus

/-!
# The potential `w` of a good square (sphere note, Proposition 6.13, first step)

On `Q = a + [0,t]²` with the blown-up points `S = ptsIn X a t` inside `Q`, and `v` smooth with `Δ v = 2π (m - m̄)`, put
`w = H_{1/4} + ∑_{p ∈ S} f_{1/4}(· - p) - v` (`Lower.wFun`).  Then `w - ∑_{p∈S} f_{1/4}(· - p) = H_{1/4} - v` and
`-Δ w = 2π (∑_{p ∈ S ∩ Q^{1/2}} δ_p - m̄)` in `𝒟'((Q^{1/2})°)` (`Lower.weak_eq_wFun`): this is the hypothesis of Input 6.3.
-/

open MeasureTheory Set Filter Topology Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The blown-up points that lie in the square `a + [0,t]²`. -/
@[expose] noncomputable def ptsIn {n : ℕ} (X : Fin n → ℂ) (a : ℂ) (t : ℝ) : Finset ℂ :=
  (Finset.univ.image fun i => blowupScale n • X i).filter (· ∈ sqAt a t)

theorem ptsIn_eq {n : ℕ} (X : Fin n → ℂ) (a : ℂ) (t : ℝ) :
    ptsIn X a t = (Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt a t).image
      fun i => blowupScale n • X i := by
  unfold ptsIn
  rw [Finset.filter_image]

theorem card_ptsIn {n : ℕ} (X : Fin n → ℂ) (hinj : Function.Injective fun i => blowupScale n • X i)
    (a : ℂ) (t : ℝ) :
    (ptsIn X a t).card = (Finset.univ.filter fun i => blowupScale n • X i ∈ sqAt a t).card := by
  rw [ptsIn_eq, Finset.card_image_of_injective _ hinj]

/-- `w = H_{1/4} + ∑_{p ∈ S} f_{1/4}(· - p) - v`. -/
@[expose] noncomputable def wFun {n : ℕ} (X : Fin n → ℂ) (S : Finset ℂ) (v : ℂ → ℝ) (x : ℂ) : ℝ :=
  truncPot X (1 / 4) x + ∑ p ∈ S, truncLog (1 / 4) (x - p) - v x

theorem wFun_natural {n : ℕ} (X : Fin n → ℂ) (S : Finset ℂ) (v : ℂ → ℝ) :
    (fun x => wFun X S v x - ∑ p ∈ S, truncLog (1 / 4) (x - p)) = fun x => truncPot X (1 / 4) x - v x := by
  funext x; unfold wFun; ring

theorem circleAverage_eq_zero_of_notMem {a z : ℂ} {t : ℝ} {φ : ℂ → ℝ}
    (hsupp : tsupport φ ⊆ interior (sqShrink a t (1 / 2))) (hz : z ∉ sqAt a t) :
    Real.circleAverage φ z (1 / 4) = 0 := by
  refine Real.circleAverage_const_on_circle fun w hw => ?_
  by_contra hne
  have hw' : w ∈ sqShrink a t (1 / 2) :=
    interior_subset (hsupp (subset_tsupport _ (Function.mem_support.2 hne)))
  rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hw
  have e1 : |w.re - z.re| ≤ 1 / 4 := by
    have : w.re - z.re = (w - z).re := by simp
    rw [this]; exact (Complex.abs_re_le_norm _).trans hw.le
  have e2 : |w.im - z.im| ≤ 1 / 4 := by
    have : w.im - z.im = (w - z).im := by simp
    rw [this]; exact (Complex.abs_im_le_norm _).trans hw.le
  rw [abs_le] at e1 e2
  rw [mem_sqShrink] at hw'
  apply hz
  rw [mem_sqAt]
  obtain ⟨c1, c2, c3, c4⟩ := hw'
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem apply_eq_zero_of_notMem_sqShrink {a z : ℂ} {t : ℝ} {φ : ℂ → ℝ}
    (hsupp : tsupport φ ⊆ interior (sqShrink a t (1 / 2))) (hz : z ∉ sqShrink a t (1 / 2)) : φ z = 0 := by
  by_contra hne
  exact hz (interior_subset (hsupp (subset_tsupport _ (Function.mem_support.2 hne))))

/-- **The weak equation of `w` on `(Q^{1/2})°`.** -/
theorem weak_eq_wFun {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {a : ℂ} {t : ℝ} {v : ℂ → ℝ}
    (hv : ContDiff ℝ ∞ v) {mb : ℝ} (hΔv : ∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - mb)) {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ interior (sqShrink a t (1 / 2))) :
    -(∫ x, wFun X (ptsIn X a t) v x * Δ φ x) =
      2 * Real.pi * ((∑ p ∈ (ptsIn X a t).filter (· ∈ sqShrink a t (1 / 2)), φ p) -
        mb * ∫ x, φ x) := by
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  set S := ptsIn X a t with hS
  have hlap := contDiff_lap hφ
  have hlc := hasCompactSupport_lap hc
  have hI1 : Integrable fun x => truncPot X (1 / 4) x * Δ φ x :=
    ((locallyLipschitz_truncPot X hη).continuous.mul hlap.continuous).integrable_of_hasCompactSupport
      hlc.mul_left
  have hI2 : ∀ p ∈ S, Integrable fun x : ℂ => truncLog (1 / 4) (x - p) * Δ φ x :=
    fun p _ => integrable_truncLog_mul_lap hφ hc hη p
  have hI3 : Integrable fun x => v x * Δ φ x :=
    (hv.continuous.mul hlap.continuous).integrable_of_hasCompactSupport hlc.mul_left
  have hexp : (fun x => wFun X S v x * Δ φ x) = fun x =>
      (truncPot X (1 / 4) x * Δ φ x + ∑ p ∈ S, truncLog (1 / 4) (x - p) * Δ φ x) - v x * Δ φ x := by
    funext x; unfold wFun; rw [← Finset.sum_mul]; ring
  have hsum : Integrable fun x => ∑ p ∈ S, truncLog (1 / 4) (x - p) * Δ φ x := integrable_finsetSum _ hI2
  have hI12 : Integrable fun x => truncPot X (1 / 4) x * Δ φ x +
      ∑ p ∈ S, truncLog (1 / 4) (x - p) * Δ φ x := hI1.add hsum
  rw [hexp, integral_sub hI12 hI3, integral_add hI1 hsum, integral_finsetSum _ hI2]
  have h1 := integral_truncPot_mul_lap hn X hφ hc hη
  have h2 : ∀ p ∈ S, ∫ x, truncLog (1 / 4) (x - p) * Δ φ x =
      2 * Real.pi * (Real.circleAverage φ p (1 / 4) - φ p) :=
    fun p _ => integral_truncLog_mul_lap hφ hη p
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have h3 : ∫ x, v x * Δ φ x = 2 * Real.pi * ((∫ x, blowupDens n x * φ x) - mb * ∫ x, φ x) := by
    rw [Weyl.integral_mul_lap_eq (W := Set.univ) hc.isCompact (Set.subset_univ _) isOpen_univ
      (hv.of_le (by norm_cast)).contDiffOn (hφ.of_le (by norm_cast))
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)]
    have hm : Integrable fun x => blowupDens n x * φ x :=
      ((contDiff_blowupDens n).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
    simp only [hΔv]
    have e : (fun x => 2 * Real.pi * (blowupDens n x - mb) * φ x) =
        fun x => 2 * Real.pi * (blowupDens n x * φ x - mb * φ x) := by funext x; ring
    rw [e, integral_const_mul, integral_sub hm (hφi.const_mul mb), integral_const_mul]
  rw [h3]
  -- split the circle averages over the points inside and outside the square
  have hsplit : ∑ i, Real.circleAverage φ (blowupScale n • X i) (1 / 4) =
      ∑ p ∈ S, Real.circleAverage φ p (1 / 4) := by
    rw [hS, ptsIn_eq, Finset.sum_image (fun i _ j _ h => hinj h), ← Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun i => blowupScale n • X i ∈ sqAt a t)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i => ¬ blowupScale n • X i ∈ sqAt a t), add_zero]
    intro i hi
    exact circleAverage_eq_zero_of_notMem hsupp (Finset.mem_filter.1 hi).2
  have hfilt : ∑ p ∈ S.filter (· ∈ sqShrink a t (1 / 2)), φ p = ∑ p ∈ S, φ p := by
    refine Finset.sum_filter_of_ne fun p _ hp => ?_
    by_contra hnot
    exact hp (apply_eq_zero_of_notMem_sqShrink hsupp hnot)
  rw [hfilt]
  rw [hsplit] at h1
  linarith

end Lower

end Sphere

end SandierSerfaty

end
