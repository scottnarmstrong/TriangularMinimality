/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.PunctureLimit

/-!
# Restriction and additivity of the puncture energy (sphere note, Lemma 2.4, additivity part)

* `Sphere.PunctureAdmissible.restrict`: an admissible `H` on `(G, P)` is admissible on `(G', P')`
  for an open `G' ⊆ G` whose points stay at positive distance from the punctures in `P ∖ P'`;
* `Sphere.punctureEnergy_split_ball`: for `H` admissible on `(ℂ, P)` with no puncture on the circle
  `‖z‖ = R`, `W_ℂ(H) = W_{B(0,R)}(H) + W_{‖z‖ > R}(H)`, the puncture sets being the punctures in each
  region (the circle is Lebesgue-null).
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

/-- Restriction of admissibility to an open subset. -/
theorem PunctureAdmissible.restrict {G : Set ℂ} {P : Finset ℂ} {H : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) {G' : Set ℂ} (hG' : IsOpen G') (hsub : G' ⊆ G) {P' : Finset ℂ}
    (hP'P : P' ⊆ P) (hP'G' : (P' : Set ℂ) ⊆ G')
    (hfar : ∀ q ∈ P, q ∉ P' → ∃ δ > 0, ∀ x ∈ G', δ ≤ ‖x - q‖) :
    PunctureAdmissible G' P' H where
  isOpen := hG'
  subset := hP'G'
  c2 x hx hxP' := by
    refine hH.c2 x (hsub hx) fun hxP => ?_
    obtain ⟨δ, hδ, hfar'⟩ := hfar x hxP hxP'
    have := hfar' x hx
    rw [sub_self, norm_zero] at this
    linarith
  local_form p hp := hH.local_form p (hP'P hp)
  finite_energy ε hε := by
    choose! δ hδ hfar' using hfar
    have hev : ∀ᶠ ε' in 𝓝[>] (0 : ℝ), 0 < ε' ∧ ε' < ε ∧ ∀ q ∈ P, q ∉ P' → ε' < δ q := by
      have h0 : ∀ᶠ ε' in 𝓝[>] (0 : ℝ), 0 < ε' := eventually_mem_nhdsWithin
      have h1 : ∀ᶠ ε' in 𝓝[>] (0 : ℝ), ε' < ε := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)
      refine h0.and (h1.and ?_)
      rw [Filter.eventually_all_finset]
      intro q hq
      by_cases hq' : q ∈ P'
      · exact Filter.Eventually.of_forall fun ε' h => absurd hq' h
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hδ q hq hq'))] with ε' h _ using h
    obtain ⟨ε', hε', hεε, hεδ⟩ := hev.exists
    refine (hH.finite_energy ε' hε').mono_set ?_
    intro x ⟨hxG', hx⟩
    refine ⟨hsub hxG', fun hmem => ?_⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hmem
    by_cases hp' : p ∈ P'
    · exact hx (mem_biUnion hp' (ball_subset_ball hεε.le hxp))
    · have := hfar' p hp hp' x hxG'
      rw [mem_ball, dist_eq_norm] at hxp
      have := hεδ p hp hp'
      rw [norm_sub_rev] at *
      linarith

/-- The punctures in the open ball. -/
noncomputable def innerPunct (P : Finset ℂ) (R : ℝ) : Finset ℂ := by
  classical exact P.filter fun p => ‖p‖ < R

/-- The punctures outside the closed ball. -/
noncomputable def outerPunct (P : Finset ℂ) (R : ℝ) : Finset ℂ := by
  classical exact P.filter fun p => R < ‖p‖

theorem mem_innerPunct {P : Finset ℂ} {R : ℝ} {p : ℂ} : p ∈ innerPunct P R ↔ p ∈ P ∧ ‖p‖ < R := by
  classical simp [innerPunct]

theorem mem_outerPunct {P : Finset ℂ} {R : ℝ} {p : ℂ} : p ∈ outerPunct P R ↔ p ∈ P ∧ R < ‖p‖ := by
  classical simp [outerPunct]

theorem card_innerPunct_add_card_outerPunct {P : Finset ℂ} {R : ℝ} (hP : ∀ p ∈ P, ‖p‖ ≠ R) :
    (innerPunct P R).card + (outerPunct P R).card = P.card := by
  classical
  unfold innerPunct outerPunct
  have : P.filter (fun p => R < ‖p‖) = P.filter (fun p => ¬ ‖p‖ < R) := by
    refine Finset.filter_congr fun p hp => ?_
    have := hP p hp
    constructor
    · intro h; exact not_lt.2 h.le
    · intro h; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm this)
  rw [this]
  exact Finset.card_filter_add_card_filter_not _

theorem admissible_inner {P : Finset ℂ} {H : ℂ → ℝ} {R : ℝ}
    (hH : PunctureAdmissible Set.univ P H) (hP : ∀ p ∈ P, ‖p‖ ≠ R) :
    PunctureAdmissible (ball (0 : ℂ) R) (innerPunct P R) H := by
  refine hH.restrict isOpen_ball (Set.subset_univ _) (fun p hp => (mem_innerPunct.1 hp).1)
    (fun p hp => by simpa using (mem_innerPunct.1 hp).2) fun q hq hq' => ?_
  have hqR : R ≤ ‖q‖ := by
    by_contra h
    exact hq' (mem_innerPunct.2 ⟨hq, not_le.1 h⟩)
  have hlt : R < ‖q‖ := lt_of_le_of_ne hqR (Ne.symm (hP q hq))
  refine ⟨‖q‖ - R, by linarith, fun x hx => ?_⟩
  have hx' : ‖x‖ < R := by simpa using hx
  have := norm_sub_norm_le q x
  rw [norm_sub_rev] at this
  linarith

theorem admissible_outer {P : Finset ℂ} {H : ℂ → ℝ} {R : ℝ}
    (hH : PunctureAdmissible Set.univ P H) (hP : ∀ p ∈ P, ‖p‖ ≠ R) :
    PunctureAdmissible {z : ℂ | R < ‖z‖} (outerPunct P R) H := by
  have hopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  refine hH.restrict hopen (Set.subset_univ _) (fun p hp => (mem_outerPunct.1 hp).1)
    (fun p hp => (mem_outerPunct.1 hp).2) fun q hq hq' => ?_
  have hqR : ‖q‖ < R := by
    by_contra h
    have hlt : R < ‖q‖ := lt_of_le_of_ne (not_lt.1 h) (Ne.symm (hP q hq))
    exact hq' (mem_outerPunct.2 ⟨hq, hlt⟩)
  refine ⟨R - ‖q‖, by linarith, fun x hx => ?_⟩
  have hx' : R < ‖x‖ := hx
  have := norm_sub_norm_le x q
  linarith

theorem notMem_ball_outer {q x : ℂ} {R η : ℝ} (_hq : R < ‖q‖) (hη : η ≤ ‖q‖ - R) (hx : ‖x‖ < R) :
    x ∉ ball q η := by
  intro h
  rw [mem_ball, dist_eq_norm] at h
  have := norm_sub_norm_le q x
  rw [norm_sub_rev] at h
  linarith

theorem notMem_ball_inner {q x : ℂ} {R η : ℝ} (_hq : ‖q‖ < R) (hη : η ≤ R - ‖q‖) (hx : R < ‖x‖) :
    x ∉ ball q η := by
  intro h
  rw [mem_ball, dist_eq_norm] at h
  have := norm_sub_norm_le x q
  linarith

theorem punctureTrunc_split {P : Finset ℂ} {H : ℂ → ℝ} {R : ℝ}
    (hH : PunctureAdmissible Set.univ P H) (hP : ∀ p ∈ P, ‖p‖ ≠ R) {η : ℝ} (hη : 0 < η)
    (hηP : ∀ p ∈ P, η ≤ |‖p‖ - R|) :
    punctureTrunc Set.univ P H η =
      punctureTrunc (ball (0 : ℂ) R) (innerPunct P R) H η +
        punctureTrunc {z : ℂ | R < ‖z‖} (outerPunct P R) H η := by
  set T0 : Set ℂ := Set.univ \ ⋃ p ∈ P, ball p η with hT0
  set T1 : Set ℂ := ball (0 : ℂ) R \ ⋃ p ∈ innerPunct P R, ball p η with hT1
  set T2 : Set ℂ := {z : ℂ | R < ‖z‖} \ ⋃ p ∈ outerPunct P R, ball p η with hT2
  have hEopen : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hm1 : MeasurableSet T1 :=
    measurableSet_ball.diff (Finset.measurableSet_biUnion _ fun p _ => measurableSet_ball)
  have hm2 : MeasurableSet T2 :=
    hEopen.measurableSet.diff (Finset.measurableSet_biUnion _ fun p _ => measurableSet_ball)
  have hT1eq : T1 = T0 ∩ ball (0 : ℂ) R := by
    ext x
    simp only [hT0, hT1, Set.mem_sdiff, Set.mem_univ, true_and, mem_iUnion, exists_prop,
      not_exists, not_and, mem_inter_iff, mem_innerPunct]
    constructor
    · rintro ⟨hx, hxp⟩
      refine ⟨fun p hp => ?_, hx⟩
      by_cases hpR : ‖p‖ < R
      · exact hxp p ⟨hp, hpR⟩
      · have hlt : R < ‖p‖ := lt_of_le_of_ne (not_lt.1 hpR) (Ne.symm (hP p hp))
        have := hηP p hp
        rw [abs_of_pos (by linarith)] at this
        exact notMem_ball_outer hlt this (by simpa using hx)
    · rintro ⟨hxp, hx⟩
      exact ⟨hx, fun p hp => hxp p hp.1⟩
  have hT2eq : T2 = T0 ∩ {z : ℂ | R < ‖z‖} := by
    ext x
    simp only [hT0, hT2, Set.mem_sdiff, Set.mem_univ, true_and, mem_iUnion, exists_prop,
      not_exists, not_and, mem_inter_iff, mem_outerPunct]
    constructor
    · rintro ⟨hx, hxp⟩
      refine ⟨fun p hp => ?_, hx⟩
      by_cases hpR : R < ‖p‖
      · exact hxp p ⟨hp, hpR⟩
      · have hlt : ‖p‖ < R := lt_of_le_of_ne (not_lt.1 hpR) (hP p hp)
        have := hηP p hp
        rw [abs_of_neg (by linarith)] at this
        exact notMem_ball_inner hlt (by linarith) hx
    · rintro ⟨hxp, hx⟩
      exact ⟨hx, fun p hp => hxp p hp.1⟩
  have hint : IntegrableOn (fun x => ‖gradient H x‖ ^ 2) T0 := by
    have := hH.finite_energy η hη
    simpa [hT0] using this
  have hnull : T0 =ᵐ[volume] T1 ∪ T2 := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (t := sphere (0 : ℂ) R) ?_ (Measure.addHaar_sphere volume 0 R)
      intro x ⟨hx0, hx12⟩
      by_contra hxs
      rw [mem_sphere_zero_iff_norm] at hxs
      rcases lt_or_gt_of_ne hxs with h | h
      · exact hx12 (Or.inl (by rw [hT1eq]; exact ⟨hx0, by simpa using h⟩))
      · exact hx12 (Or.inr (by rw [hT2eq]; exact ⟨hx0, h⟩))
    · rw [hT1eq, hT2eq]
      refine measure_mono_null ?_ (measure_empty (μ := volume))
      intro x ⟨hx12, hx0⟩
      exact absurd (hx12.elim (fun h => h.1) fun h => h.1) hx0
  have hdisj : Disjoint T1 T2 := by
    refine Set.disjoint_left.2 fun x hx1 hx2 => ?_
    have h1 : ‖x‖ < R := by simpa using hx1.1
    have h2 : R < ‖x‖ := hx2.1
    linarith
  have hsplit : ∫ x in T0, ‖gradient H x‖ ^ 2 =
      (∫ x in T1, ‖gradient H x‖ ^ 2) + ∫ x in T2, ‖gradient H x‖ ^ 2 := by
    rw [setIntegral_congr_set hnull]
    refine setIntegral_union hdisj hm2 (hint.mono_set ?_) (hint.mono_set ?_)
    · rw [hT1eq]; exact inter_subset_left
    · rw [hT2eq]; exact inter_subset_left
  have hcard := card_innerPunct_add_card_outerPunct hP
  have hcard' : (P.card : ℝ) = (innerPunct P R).card + (outerPunct P R).card := by
    rw [← hcard]; push_cast; ring
  unfold punctureTrunc
  rw [hcard']
  have : (∫ x in Set.univ \ ⋃ p ∈ P, ball p η, ‖gradient H x‖ ^ 2) =
      ∫ x in T0, ‖gradient H x‖ ^ 2 := rfl
  rw [this, hsplit]
  ring

/-- **Lemma 2.4, additivity.** For `H` admissible on `(ℂ, P)` with no puncture on `‖z‖ = R`,
`W_ℂ(H) = W_{B(0,R)}(H) + W_{‖z‖ > R}(H)`. -/
theorem punctureEnergy_split_ball {P : Finset ℂ} {H : ℂ → ℝ} {R : ℝ}
    (hH : PunctureAdmissible Set.univ P H) (hP : ∀ p ∈ P, ‖p‖ ≠ R) :
    punctureEnergy Set.univ P H =
      punctureEnergy (ball (0 : ℂ) R) (innerPunct P R) H +
        punctureEnergy {z : ℂ | R < ‖z‖} (outerPunct P R) H := by
  have h1 := (hH.tendsto_punctureEnergy)
  have h2 := (admissible_inner hH hP).tendsto_punctureEnergy
  have h3 := (admissible_outer hH hP).tendsto_punctureEnergy
  have h23 := h2.add h3
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ ∀ p ∈ P, η ≤ |‖p‖ - R| := by
    have h0 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := eventually_mem_nhdsWithin
    refine h0.and ?_
    rw [Filter.eventually_all_finset]
    intro p hp
    have hpos : 0 < |‖p‖ - R| := abs_pos.2 (sub_ne_zero.2 (hP p hp))
    have h5 : ∀ᶠ η in 𝓝 (0 : ℝ), η < |‖p‖ - R| := Iio_mem_nhds hpos
    filter_upwards [mem_nhdsWithin_of_mem_nhds h5] with η h using h.le
  have h4 : Tendsto (punctureTrunc Set.univ P H) (𝓝[>] 0)
      (𝓝 (punctureEnergy (ball (0 : ℂ) R) (innerPunct P R) H +
        punctureEnergy {z : ℂ | R < ‖z‖} (outerPunct P R) H)) := by
    refine h23.congr' ?_
    filter_upwards [hev] with η ⟨hη, hηP⟩
    exact (punctureTrunc_split hH hP hη hηP).symm
  exact tendsto_nhds_unique h1 h4

end Sphere

end SandierSerfaty

end
