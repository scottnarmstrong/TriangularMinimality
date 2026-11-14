/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Puncture
public import SandierSerfaty.Torus.PotentialLocal

/-!
# Local analysis of an admissible function near a puncture (sphere note, Lemma 2.4, local part)

If `H` is admissible on `(G, P)` (Definition 2.3), there is a radius `ε` and a constant `C` such that,
for every `p ∈ P` and `x ∈ B(p, ε) ∖ {p}`,
`| |∇H(x)|² - |x - p|⁻² | ≤ C + C / |x - p|`
(`Sphere.PunctureAdmissible.exists_good`). This is the estimate that makes the remainder of
`|∇H|² = |x - p|⁻² + (remainder)` integrable near `p`.
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem abs_norm_sq_sub_le (A B : ℂ →L[ℝ] ℝ) :
    |‖A - B‖ ^ 2 - ‖B‖ ^ 2| ≤ ‖A‖ ^ 2 + 2 * ‖A‖ * ‖B‖ := by
  have h1 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
  have h2 : ‖B‖ ≤ ‖A - B‖ + ‖A‖ := by
    have := norm_sub_le A (A - B)
    rw [sub_sub_cancel] at this
    linarith
  have h3 := norm_nonneg A
  have h4 := norm_nonneg B
  have h5 := norm_nonneg (A - B)
  rw [abs_le]
  constructor <;> nlinarith

/-- Near a puncture the derivative of `H = s - log ‖· - p‖` is `∇s` minus `⟪x - p, ·⟫ / ‖x - p‖²`. -/
theorem fderiv_eq_of_eq_sub_log_c1 {H s : ℂ → ℝ} {p x : ℂ} {r : ℝ}
    (hs : ∀ y ∈ ball p r, ContDiffAt ℝ 1 s y)
    (hloc : ∀ y ∈ ball p r, y ≠ p → H y = s y - Real.log ‖y - p‖) (hx : x ∈ ball p r)
    (hxp : x ≠ p) :
    fderiv ℝ H x = fderiv ℝ s x - (‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p) := by
  have hev : H =ᶠ[𝓝 x] fun y => s y - Real.log ‖y - p‖ := by
    filter_upwards [isOpen_ball.mem_nhds hx, isOpen_ne.mem_nhds hxp] with y hy hyp
    exact hloc y hy hyp
  have hvd : DifferentiableAt ℝ s x := (hs x hx).differentiableAt (by simp)
  rw [hev.fderiv_eq]
  exact (hvd.hasFDerivAt.sub (Torus.hasFDerivAt_log_norm_sub hxp)).fderiv

theorem norm_log_part {p x : ℂ} (hxp : x ≠ p) :
    ‖(‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p)‖ = ‖x - p‖⁻¹ := by
  have hn : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp)
  rw [norm_smul, innerSL_apply_norm, norm_inv, norm_pow, norm_norm]
  field_simp

/-- The local data of an admissible function near one puncture. -/
theorem exists_local_data {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ} (hH : PunctureAdmissible G P H)
    {p : ℂ} (hp : p ∈ P) :
    ∃ r > 0, ∃ M : ℝ, 0 ≤ M ∧ ball p r ⊆ G ∧
      ∀ x ∈ ball p r, x ≠ p →
        |‖gradient H x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹| ≤ M + M / ‖x - p‖ := by
  obtain ⟨s, hs, hform⟩ := hH.local_form p hp
  have hG : G ∈ 𝓝 p := hH.isOpen.mem_nhds (hH.subset hp)
  have hE1 : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ 1 s y := hs.eventually (by simp)
  have hE2 : ∀ᶠ y in 𝓝 p, y ≠ p → H y = s y - Real.log ‖y - p‖ := by
    have := eventually_nhdsWithin_iff.1 hform
    exact this
  have hcont : ContinuousAt (fderiv ℝ s) p :=
    (hs.fderiv_right (m := 0) (by simp)).continuousAt
  have hE3 : ∀ᶠ y in 𝓝 p, ‖fderiv ℝ s y‖ ≤ ‖fderiv ℝ s p‖ + 1 := by
    have := hcont.norm.eventually (Iio_mem_nhds (lt_add_one ‖fderiv ℝ s p‖))
    filter_upwards [this] with y hy using le_of_lt hy
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hE1.and (hE2.and (hE3.and hG)))
  refine ⟨r, hr, (‖fderiv ℝ s p‖ + 1) ^ 2 + 2 * (‖fderiv ℝ s p‖ + 1), by positivity,
    fun y hy => (hball y hy).2.2.2, fun x hx hxp => ?_⟩
  set M := ‖fderiv ℝ s p‖ + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  have hfd := fderiv_eq_of_eq_sub_log_c1 (fun y hy => (hball y hy).1)
    (fun y hy => (hball y hy).2.1) hx hxp
  have hxn : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp)
  rw [Torus.norm_gradient_eq, hfd]
  have h := abs_norm_sq_sub_le (fderiv ℝ s x) ((‖x - p‖ ^ 2)⁻¹ • innerSL ℝ (x - p))
  rw [norm_log_part hxp] at h
  have hA : ‖fderiv ℝ s x‖ ≤ M := (hball x hx).2.2.1
  have hb : (‖x - p‖⁻¹) ^ 2 = (‖x - p‖ ^ 2)⁻¹ := by rw [inv_pow]
  rw [hb] at h
  refine h.trans ?_
  have hb0 : 0 ≤ ‖x - p‖⁻¹ := by positivity
  have h6 : ‖fderiv ℝ s x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have h7 : 2 * ‖fderiv ℝ s x‖ * ‖x - p‖⁻¹ ≤ 2 * M * ‖x - p‖⁻¹ := by gcongr
  have h8 : M / ‖x - p‖ = M * ‖x - p‖⁻¹ := div_eq_mul_inv _ _
  have h9 : (M ^ 2 + 2 * M) / ‖x - p‖ = (M ^ 2 + 2 * M) * ‖x - p‖⁻¹ := div_eq_mul_inv _ _
  rw [h9]
  nlinarith [mul_nonneg (sq_nonneg M) hb0]

/-- **Local analysis of an admissible function.** A common radius and constant for all punctures. -/
theorem PunctureAdmissible.exists_good {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ (∀ p ∈ P, ball p ε ⊆ G) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * ε ≤ ‖p - q‖) ∧
      ∀ p ∈ P, ∀ x ∈ ball p ε, x ≠ p →
        |‖gradient H x‖ ^ 2 - (‖x - p‖ ^ 2)⁻¹| ≤ C + C / ‖x - p‖ := by
  choose! r hr M hM hsub hbd using fun p (hp : p ∈ P) => exists_local_data hH hp
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ (∀ p ∈ P, ε < r p) ∧
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * ε ≤ ‖p - q‖) := by
    have h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
    refine h0.and (((Filter.eventually_all_finset P).2 fun p hp => ?_).and ?_)
    · exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hr p hp))
    · refine (Filter.eventually_all_finset P).2 fun p hp => (Filter.eventually_all_finset P).2
        fun q hq => ?_
      by_cases hpq : p = q
      · exact Filter.Eventually.of_forall fun ε h => absurd hpq h
      · have hpos : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
        have : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < ‖p - q‖ / 2 := Iio_mem_nhds (by positivity)
        filter_upwards [mem_nhdsWithin_of_mem_nhds this] with ε hε _
        linarith
  obtain ⟨ε, hε, hεr, hεs⟩ := hev.exists
  refine ⟨ε, ∑ p ∈ P, M p, hε, Finset.sum_nonneg fun p hp => hM p hp, fun p hp => ?_, hεs,
    fun p hp x hx hxp => ?_⟩
  · exact (ball_subset_ball (hεr p hp).le).trans (hsub p hp)
  · have hx' : x ∈ ball p (r p) := ball_subset_ball (hεr p hp).le hx
    refine (hbd p hp x hx' hxp).trans ?_
    have hle : M p ≤ ∑ q ∈ P, M q :=
      Finset.single_le_sum (f := M) (fun q hq => hM q hq) hp
    have hxn : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp)
    gcongr

end Sphere

end SandierSerfaty

end
