/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectEnergy
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A smooth cutoff for the discrepancy lemma (sphere note, Lemma 6.7)

`Lower.exists_cutoff`: there is an absolute constant `C₀` such that for every square `Q = a₀ + [0,t]²` there is a smooth
compactly supported `χ`, `0 ≤ χ ≤ 1`, with `χ = 1` on `Q¹`, `supp χ ⊆ (Q^{1/2})°`, `∇ χ = 0` off the layer `Q^{1/2} ∖ Q¹`
and `|∂_v χ| ≤ C₀ |v|`.  It is a product of four one-dimensional cutoffs `ψ(4 (· - 5/8))`, `ψ = smoothTransition`.
-/

open Set Filter Topology
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem lipschitzWith_smoothTransition : ∃ L : NNReal, LipschitzWith L Real.smoothTransition := by
  have hd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hder : Continuous (deriv Real.smoothTransition) := hd.continuous_deriv (by simp)
  have hz : ∀ x ∉ Icc (0 : ℝ) 1, deriv Real.smoothTransition x = 0 := by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [this.deriv_eq]; simp
    · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [this.deriv_eq]; simp
  obtain ⟨C, hC⟩ := hder.bounded_above_of_compact_support (HasCompactSupport.intro isCompact_Icc hz)
  refine ⟨Real.toNNReal C, lipschitzWith_of_nnnorm_deriv_le (hd.differentiable (by simp)) fun x => ?_⟩
  have := hC x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ ((norm_nonneg _).trans this)]
  exact this

theorem lipschitzWith_mul_of_le_one {f g : ℂ → ℝ} {Kf Kg : NNReal} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1) : LipschitzWith (Kf + Kg) fun x => f x * g x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have e : f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) := by ring
  rw [e]
  calc |(f x - f y) * g x + f y * (g x - g y)| ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ ≤ |f x - f y| + |g x - g y| := by
        rw [abs_mul, abs_mul]
        have a1 : |g x| ≤ 1 := by rw [abs_of_nonneg (hg0 x)]; exact hg1 x
        have a2 : |f y| ≤ 1 := by rw [abs_of_nonneg (hf0 y)]; exact hf1 y
        nlinarith [abs_nonneg (f x - f y), abs_nonneg (g x - g y), abs_nonneg (g x), abs_nonneg (f y)]
    _ ≤ Kf * dist x y + Kg * dist x y := add_le_add h1 h2
    _ = ↑(Kf + Kg) * dist x y := by push_cast; ring

/-- The one-dimensional profile `ψ(u) = smoothTransition (4 u - 5/2)`: `0` for `u ≤ 5/8`, `1` for `u ≥ 7/8`. -/
@[expose] noncomputable def prof (u : ℝ) : ℝ := Real.smoothTransition (4 * u - 5 / 2)

theorem prof_eq_zero {u : ℝ} (h : u ≤ 5 / 8) : prof u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem prof_eq_one {u : ℝ} (h : 7 / 8 ≤ u) : prof u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem prof_ne_zero {u : ℝ} (h : prof u ≠ 0) : 5 / 8 < u := by
  by_contra h'
  exact h (prof_eq_zero (not_lt.1 h'))

theorem contDiff_prof : ContDiff ℝ ∞ prof :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- The cutoff on the square `a + [0,t]²`. -/
@[expose] noncomputable def cutoff (a : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  (prof (x.re - a.re) * prof (a.re + t - x.re)) * (prof (x.im - a.im) * prof (a.im + t - x.im))

theorem contDiff_cutoff (a : ℂ) (t : ℝ) : ContDiff ℝ ∞ (cutoff a t) := by
  unfold cutoff
  have h1 : ContDiff ℝ ∞ fun x : ℂ => x.re := Complex.reCLM.contDiff
  have h2 : ContDiff ℝ ∞ fun x : ℂ => x.im := Complex.imCLM.contDiff
  exact ((contDiff_prof.comp (h1.sub contDiff_const)).mul (contDiff_prof.comp (contDiff_const.sub h1))).mul
    ((contDiff_prof.comp (h2.sub contDiff_const)).mul (contDiff_prof.comp (contDiff_const.sub h2)))

theorem prof_nonneg (u : ℝ) : 0 ≤ prof u := Real.smoothTransition.nonneg _

theorem prof_le_one (u : ℝ) : prof u ≤ 1 := Real.smoothTransition.le_one _

theorem cutoff_nonneg (a : ℂ) (t : ℝ) (x : ℂ) : 0 ≤ cutoff a t x := by
  unfold cutoff
  have := prof_nonneg (x.re - a.re); have := prof_nonneg (a.re + t - x.re)
  have := prof_nonneg (x.im - a.im); have := prof_nonneg (a.im + t - x.im)
  positivity

theorem cutoff_le_one (a : ℂ) (t : ℝ) (x : ℂ) : cutoff a t x ≤ 1 := by
  unfold cutoff
  have h1 := prof_nonneg (x.re - a.re); have h2 := prof_nonneg (a.re + t - x.re)
  have h3 := prof_nonneg (x.im - a.im); have h4 := prof_nonneg (a.im + t - x.im)
  have g1 := prof_le_one (x.re - a.re); have g2 := prof_le_one (a.re + t - x.re)
  have g3 := prof_le_one (x.im - a.im); have g4 := prof_le_one (a.im + t - x.im)
  have : prof (x.re - a.re) * prof (a.re + t - x.re) ≤ 1 := by nlinarith
  have : prof (x.im - a.im) * prof (a.im + t - x.im) ≤ 1 := by nlinarith
  nlinarith [mul_nonneg h1 h2, mul_nonneg h3 h4]

theorem cutoff_ne_zero {a : ℂ} {t : ℝ} {x : ℂ} (h : cutoff a t x ≠ 0) :
    a.re + 5 / 8 < x.re ∧ x.re < a.re + t - 5 / 8 ∧ a.im + 5 / 8 < x.im ∧ x.im < a.im + t - 5 / 8 := by
  unfold cutoff at h
  have h' := mul_ne_zero_iff.1 h
  have h1 := mul_ne_zero_iff.1 h'.1
  have h2 := mul_ne_zero_iff.1 h'.2
  have a1 := prof_ne_zero h1.1; have a2 := prof_ne_zero h1.2
  have a3 := prof_ne_zero h2.1; have a4 := prof_ne_zero h2.2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cutoff_eq_one {a : ℂ} {t : ℝ} {x : ℂ} (h1 : a.re + 7 / 8 ≤ x.re) (h2 : x.re ≤ a.re + t - 7 / 8)
    (h3 : a.im + 7 / 8 ≤ x.im) (h4 : x.im ≤ a.im + t - 7 / 8) : cutoff a t x = 1 := by
  unfold cutoff
  rw [prof_eq_one (by linarith), prof_eq_one (by linarith), prof_eq_one (by linarith),
    prof_eq_one (by linarith)]
  norm_num

theorem lipschitz_re_sub (c : ℝ) : LipschitzWith 1 fun x : ℂ => x.re - c := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  have : x.re - c - (y.re - c) = (x - y).re := by simp
  rw [this]; simpa using Complex.abs_re_le_norm (x - y)

theorem lipschitz_sub_re (c : ℝ) : LipschitzWith 1 fun x : ℂ => c - x.re := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  have : c - x.re - (c - y.re) = -(x - y).re := by simp
  rw [this, abs_neg]; simpa using Complex.abs_re_le_norm (x - y)

theorem lipschitz_im_sub (c : ℝ) : LipschitzWith 1 fun x : ℂ => x.im - c := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  have : x.im - c - (y.im - c) = (x - y).im := by simp
  rw [this]; simpa using Complex.abs_im_le_norm (x - y)

theorem lipschitz_sub_im (c : ℝ) : LipschitzWith 1 fun x : ℂ => c - x.im := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  have : c - x.im - (c - y.im) = -(x - y).im := by simp
  rw [this, abs_neg]; simpa using Complex.abs_im_le_norm (x - y)

theorem exists_lipschitz_cutoff : ∃ K : NNReal, ∀ (a : ℂ) (t : ℝ), LipschitzWith K (cutoff a t) := by
  obtain ⟨L, hL⟩ := lipschitzWith_smoothTransition
  have hprof : LipschitzWith (L * 4) prof := by
    have h4 : LipschitzWith 4 (fun u : ℝ => 4 * u - 5 / 2) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq]
      have : 4 * x - 5 / 2 - (4 * y - 5 / 2) = 4 * (x - y) := by ring
      rw [this, abs_mul]; norm_num
    exact hL.comp h4
  refine ⟨(L * 4 * 1 + L * 4 * 1) + (L * 4 * 1 + L * 4 * 1), fun a t => ?_⟩
  have f1 := hprof.comp (lipschitz_re_sub a.re)
  have f2 := hprof.comp (lipschitz_sub_re (a.re + t))
  have f3 := hprof.comp (lipschitz_im_sub a.im)
  have f4 := hprof.comp (lipschitz_sub_im (a.im + t))
  have g12 := lipschitzWith_mul_of_le_one f1 f2 (fun x => prof_nonneg _) (fun x => prof_le_one _)
    (fun x => prof_nonneg _) (fun x => prof_le_one _)
  have g34 := lipschitzWith_mul_of_le_one f3 f4 (fun x => prof_nonneg _) (fun x => prof_le_one _)
    (fun x => prof_nonneg _) (fun x => prof_le_one _)
  exact lipschitzWith_mul_of_le_one g12 g34 (fun x => mul_nonneg (prof_nonneg _) (prof_nonneg _))
    (fun x => by have := prof_le_one (x.re - a.re); have := prof_le_one (a.re + t - x.re)
                 have := prof_nonneg (x.re - a.re); have := prof_nonneg (a.re + t - x.re)
                 nlinarith)
    (fun x => mul_nonneg (prof_nonneg _) (prof_nonneg _))
    (fun x => by have := prof_le_one (x.im - a.im); have := prof_le_one (a.im + t - x.im)
                 have := prof_nonneg (x.im - a.im); have := prof_nonneg (a.im + t - x.im)
                 nlinarith)

theorem tsupport_cutoff_subset (a : ℂ) (t : ℝ) :
    tsupport (cutoff a t) ⊆ {x : ℂ | a.re + 5 / 8 ≤ x.re ∧ x.re ≤ a.re + t - 5 / 8 ∧
      a.im + 5 / 8 ≤ x.im ∧ x.im ≤ a.im + t - 5 / 8} := by
  have hcl : IsClosed {x : ℂ | a.re + 5 / 8 ≤ x.re ∧ x.re ≤ a.re + t - 5 / 8 ∧
      a.im + 5 / 8 ≤ x.im ∧ x.im ≤ a.im + t - 5 / 8} := by
    refine (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  refine closure_minimal (fun x hx => ?_) hcl
  obtain ⟨h1, h2, h3, h4⟩ := cutoff_ne_zero (Function.mem_support.1 hx)
  exact ⟨h1.le, h2.le, h3.le, h4.le⟩

theorem hasCompactSupport_cutoff (a : ℂ) (t : ℝ) : HasCompactSupport (cutoff a t) := by
  refine HasCompactSupport.intro (K := Metric.closedBall 0 (2 * (‖a‖ + |t| + 1))) (isCompact_closedBall _ _) ?_
  intro x hx
  by_contra h
  obtain ⟨h1, h2, h3, h4⟩ := cutoff_ne_zero h
  apply hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |x.re| ≤ ‖a‖ + |t| + 1 := by
    have := Complex.abs_re_le_norm a
    rw [abs_le]; constructor <;> cases abs_cases t <;> linarith [neg_abs_le a.re, le_abs_self a.re]
  have him : |x.im| ≤ ‖a‖ + |t| + 1 := by
    have := Complex.abs_im_le_norm a
    rw [abs_le]; constructor <;> cases abs_cases t <;> linarith [neg_abs_le a.im, le_abs_self a.im]
  calc ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
    _ ≤ 2 * (‖a‖ + |t| + 1) := by linarith

theorem ev_re_gt (c : ℝ) {x : ℂ} (h : c < x.re) : ∀ᶠ y in 𝓝 x, c < y.re :=
  Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds h)

theorem ev_re_lt (c : ℝ) {x : ℂ} (h : x.re < c) : ∀ᶠ y in 𝓝 x, y.re < c :=
  Complex.continuous_re.continuousAt.preimage_mem_nhds (Iio_mem_nhds h)

theorem ev_im_gt (c : ℝ) {x : ℂ} (h : c < x.im) : ∀ᶠ y in 𝓝 x, c < y.im :=
  Complex.continuous_im.continuousAt.preimage_mem_nhds (Ioi_mem_nhds h)

theorem ev_im_lt (c : ℝ) {x : ℂ} (h : x.im < c) : ∀ᶠ y in 𝓝 x, y.im < c :=
  Complex.continuous_im.continuousAt.preimage_mem_nhds (Iio_mem_nhds h)

/-- **The cutoff of Lemma 6.7.** -/
theorem exists_cutoff : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (a₀ : ℂ) (t : ℝ), ∃ χ : ℂ → ℝ,
    ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ interior (sqShrink a₀ t (1 / 2)) ∧ (∀ x ∈ sqShrink a₀ t 1, χ x = 1) ∧
      (∀ x, fderiv ℝ χ x ≠ 0 → x ∈ sqShrink a₀ t (1 / 2) ∧ x ∉ sqShrink a₀ t 1) ∧
      ∀ x v, |fderiv ℝ χ x v| ≤ C₀ * ‖v‖ := by
  obtain ⟨K, hK⟩ := exists_lipschitz_cutoff
  refine ⟨K, K.2, fun a t => ⟨cutoff a t, contDiff_cutoff a t, hasCompactSupport_cutoff a t,
    fun x => ⟨cutoff_nonneg a t x, cutoff_le_one a t x⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := tsupport_cutoff_subset a t hx
    simp only [sqShrink]
    rw [interior_sqAt]
    simp only [openSq, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro x hx
    simp only [sqShrink, sqAt, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im] at hx
    exact cutoff_eq_one (by linarith [hx.1]) (by linarith [hx.2.1]) (by linarith [hx.2.2.1])
      (by linarith [hx.2.2.2])
  · intro x hx
    by_contra hnot
    apply hx
    by_cases hq : x ∈ sqShrink a t (1 / 2)
    · have hq1 : x ∈ sqShrink a t 1 := by
        by_contra h; exact hnot ⟨hq, h⟩
      simp only [sqShrink, sqAt, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im] at hq1
      have e : cutoff a t =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [ev_re_gt (a.re + 7 / 8) (by linarith [hq1.1]),
          ev_re_lt (a.re + t - 7 / 8) (by linarith [hq1.2.1]),
          ev_im_gt (a.im + 7 / 8) (by linarith [hq1.2.2.1]),
          ev_im_lt (a.im + t - 7 / 8) (by linarith [hq1.2.2.2])] with y h1 h2 h3 h4
        exact cutoff_eq_one (by linarith) (by linarith) (by linarith) (by linarith)
      rw [e.fderiv_eq]; simp
    · simp only [sqShrink, sqAt, Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, not_and_or,
        not_le] at hq
      have e : cutoff a t =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        rcases hq with h | h | h | h
        · filter_upwards [ev_re_lt (a.re + 5 / 8) (by linarith)] with y hy
          unfold cutoff; rw [prof_eq_zero (by linarith)]; simp
        · filter_upwards [ev_re_gt (a.re + t - 5 / 8) (by linarith)] with y hy
          unfold cutoff; rw [prof_eq_zero (u := a.re + t - y.re) (by linarith)]; simp
        · filter_upwards [ev_im_lt (a.im + 5 / 8) (by linarith)] with y hy
          unfold cutoff; rw [prof_eq_zero (u := y.im - a.im) (by linarith)]; simp
        · filter_upwards [ev_im_gt (a.im + t - 5 / 8) (by linarith)] with y hy
          unfold cutoff; rw [prof_eq_zero (u := a.im + t - y.im) (by linarith)]; simp
      rw [e.fderiv_eq]; simp
  · intro x v
    have h1 := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) (hK a t)
    calc |fderiv ℝ (cutoff a t) x v| = ‖fderiv ℝ (cutoff a t) x v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (cutoff a t) x‖ * ‖v‖ := (fderiv ℝ (cutoff a t) x).le_opNorm v
      _ ≤ K * ‖v‖ := by gcongr

end Lower

end Sphere

end SandierSerfaty

end
