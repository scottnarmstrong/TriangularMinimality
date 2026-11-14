/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.WeylKernel

/-!
# Scale independence of the mollification of a weakly harmonic function

`Weyl.IsWeaklyHarmonicOn U u` says `∫_U u Δψ = 0` for every smooth compactly supported `ψ` with
`tsupport ψ ⊆ U`. The key fact (`Weyl.mollify_eq_mollify`) is that the mollifications of such a
`u` at two scales `δ, ε` agree at every point `x` whose closed disk of radius `max δ ε` lies in `U`:
the difference `rho δ (· - x) - rho ε (· - x)` is the Laplacian of a smooth compactly supported
radial function (`Weyl.exists_potential_rho_sub`, from `Weyl.exists_radialPotential`), against
which `u` pairs to zero.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- `u` is weakly harmonic on `U`: `∫_U u Δψ = 0` for every smooth compactly supported test function
`ψ` with `tsupport ψ ⊆ U`. -/
@[expose] def IsWeaklyHarmonicOn (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x in U, u x * Δ ψ x = 0

theorem setIntegral_mul_lap_eq_integral {U : Set ℂ} (u : ℂ → ℝ) {ψ : ℂ → ℝ}
    (hψ : tsupport ψ ⊆ U) : ∫ x in U, u x * Δ ψ x = ∫ x, u x * Δ ψ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [lap_eq_zero_of_notMem_tsupport (fun h => hx (hψ h)), mul_zero]

theorem IsWeaklyHarmonicOn.mono {U V : Set ℂ} {u : ℂ → ℝ} (h : IsWeaklyHarmonicOn U u)
    (hVU : V ⊆ U) : IsWeaklyHarmonicOn V u := by
  intro ψ hψ hc hs
  rw [setIntegral_mul_lap_eq_integral u hs, ← setIntegral_mul_lap_eq_integral u (hs.trans hVU)]
  exact h ψ hψ hc (hs.trans hVU)

/-- The profile of `rho δ` as a function of `s = ‖w‖²`. -/
@[expose] noncomputable def kappa (δ s : ℝ) : ℝ := prof (s / δ ^ 2) / (δ ^ 2 * kmass)

theorem rho_eq_kappa (δ : ℝ) (w : ℂ) : rho δ w = kappa δ (‖w‖ ^ 2) := rfl

theorem integral_prof_of_one_le {B : ℝ} (hB : 1 ≤ B) :
    ∫ t in (0 : ℝ)..B, prof t = ∫ t in (0 : ℝ)..1, prof t := by
  have h2 : ∫ t in (1 : ℝ)..B, prof t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.mem_uIcc] at ht
      exact prof_eq_zero_of_ge (by rcases ht with ⟨h1, _⟩ | ⟨h1, h2⟩ <;> linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (contDiff_prof.continuous.intervalIntegrable 0 1)
    (contDiff_prof.continuous.intervalIntegrable 1 B), h2, add_zero]

theorem integral_kappa {δ : ℝ} (hδ : 0 < δ) {B : ℝ} (hB : δ ^ 2 ≤ B) :
    ∫ s in (0 : ℝ)..B, kappa δ s = (∫ t in (0 : ℝ)..1, prof t) / kmass := by
  have hδ2 : δ ^ 2 ≠ 0 := by positivity
  have hM := kmass_pos.ne'
  simp only [kappa]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div (fun t => prof t) hδ2, smul_eq_mul, zero_div,
    integral_prof_of_one_le (by rwa [le_div_iff₀ (by positivity), one_mul])]
  field_simp

theorem contDiff_kappa (δ : ℝ) : ContDiff ℝ ∞ (kappa δ) :=
  (contDiff_prof.comp (contDiff_id.div_const _)).div_const _

/-- **The difference of two mollifying densities is the Laplacian of a compactly supported radial
function.** -/
theorem exists_potential_rho_sub {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (x : ℂ) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, max δ ε < ‖z - x‖ → ψ z = 0) ∧
      ∀ y, Δ ψ y = rho δ (y - x) - rho ε (y - x) := by
  have hm : 0 < min δ ε := lt_min hδ hε
  have hmx : 0 < max δ ε := lt_max_of_lt_left hδ
  obtain ⟨G, hG, hGb, hGeq⟩ := exists_radialPotential
    (κ := fun s => kappa δ s - kappa ε s) ((contDiff_kappa δ).sub (contDiff_kappa ε))
    (a := min δ ε ^ 2 / 4) (b := max δ ε ^ 2) (by positivity)
    (by
      intro s hs
      have h1 : min δ ε ^ 2 ≤ δ ^ 2 := by
        have := min_le_left δ ε; nlinarith
      have h2 : min δ ε ^ 2 ≤ ε ^ 2 := by
        have := min_le_right δ ε; nlinarith
      simp only [kappa]
      rw [prof_eq_zero_of_le (s := s / δ ^ 2) (by rw [div_le_iff₀ (by positivity)]; nlinarith),
        prof_eq_zero_of_le (s := s / ε ^ 2) (by rw [div_le_iff₀ (by positivity)]; nlinarith)]
      simp)
    (by
      intro s hs
      have h1 : δ ^ 2 ≤ max δ ε ^ 2 := by
        have := le_max_left δ ε; nlinarith
      have h2 : ε ^ 2 ≤ max δ ε ^ 2 := by
        have := le_max_right δ ε; nlinarith
      simp only [kappa]
      rw [prof_eq_zero_of_ge (s := s / δ ^ 2) (by rw [le_div_iff₀ (by positivity)]; nlinarith),
        prof_eq_zero_of_ge (s := s / ε ^ 2) (by rw [le_div_iff₀ (by positivity)]; nlinarith)]
      simp)
    (by
      have h1 : δ ^ 2 ≤ max δ ε ^ 2 := by
        have := le_max_left δ ε; nlinarith
      have h2 : ε ^ 2 ≤ max δ ε ^ 2 := by
        have := le_max_right δ ε; nlinarith
      rw [intervalIntegral.integral_sub
        ((contDiff_kappa δ).continuous.intervalIntegrable _ _)
        ((contDiff_kappa ε).continuous.intervalIntegrable _ _),
        integral_kappa hδ h1, integral_kappa hε h2, sub_self])
  refine ⟨fun z => G (‖z - x‖ ^ 2), contDiff_comp_normSq_sub hG x, ?_, ?_⟩
  · intro z hz
    apply hGb
    nlinarith
  · intro y
    rw [lap_comp_normSq_sub (hG.of_le (by norm_num)) x y, hGeq, rho_eq_kappa, rho_eq_kappa]

/-- **Mollification of a weakly harmonic function does not depend on the scale.** -/
theorem mollify_eq_mollify {U : Set ℂ} {u : ℂ → ℝ} (hu : LocallyIntegrable u volume)
    (hw : IsWeaklyHarmonicOn U u) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {x : ℂ}
    (hball : closedBall x (max δ ε) ⊆ U) : mollify δ u x = mollify ε u x := by
  obtain ⟨ψ, hψs, hψ0, hlap⟩ := exists_potential_rho_sub hδ hε x
  have hsupp : tsupport ψ ⊆ closedBall x (max δ ε) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    by_contra h
    exact hz (hψ0 z (by simpa [mem_closedBall, dist_eq_norm, not_le] using h))
  have hcs : HasCompactSupport ψ :=
    HasCompactSupport.intro (isCompact_closedBall x (max δ ε)) fun z hz =>
      hψ0 z (by simpa [mem_closedBall, dist_eq_norm, not_le] using hz)
  have hzero := hw ψ hψs hcs (hsupp.trans hball)
  rw [setIntegral_mul_lap_eq_integral u (hsupp.trans hball)] at hzero
  have hmul : ∀ y, u y * Δ ψ y = u y * rho δ (y - x) - u y * rho ε (y - x) := by
    intro y; rw [hlap y]; ring
  simp_rw [hmul] at hzero
  rw [integral_sub (integrable_mul_rho_sub hδ hu x) (integrable_mul_rho_sub hε hu x)] at hzero
  unfold mollify
  linarith

end SandierSerfaty.Weyl

end
