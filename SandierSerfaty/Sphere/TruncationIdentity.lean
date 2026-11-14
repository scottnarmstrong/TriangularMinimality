/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.TruncIdentity

/-!
# The truncation identity (sphere note, Lemma 3.10)

For `H` admissible on `(G, P)` with `Δ H = 2π ϱ` on `G ∖ P` (`ϱ ∈ C¹(G)`), pairwise disjoint closed
discs `\bar B(p, α_p) ⊆ G` and `H_α = H - ∑_p f_{α_p}(· - p)`,
```
W_G(H) = ½ ∫_G |∇H_α|² + π ∑_p log α_p - 2π ∑_p ∫_{B(p, α_p)} f_{α_p}(x - p) ϱ(x) dx.
```
(`Sphere.truncation_identity`).  The hypothesis `-ΔH = 2π(∑ δ_p - ϱ)` of the sphere note, in the sense of
distributions on `G`, is used only through its pointwise consequence `ΔH = 2π ϱ` on `G ∖ P`
(admissibility gives `H ∈ C²(G ∖ P)`), so the statement here is the slightly stronger one.
-/

open MeasureTheory Filter Topology Set SandierSerfaty.Analysis Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem setIntegral_union_finset {f : ℂ → ℝ} {D : Set ℂ} {T : ℂ → Set ℂ} {P : Finset ℂ}
    (hT : ∀ p ∈ P, MeasurableSet (T p))
    (hDT : ∀ p ∈ P, Disjoint D (T p)) (hTT : (↑P : Set ℂ).Pairwise (Function.onFun Disjoint T))
    (iD : IntegrableOn f D) (iT : ∀ p ∈ P, IntegrableOn f (T p)) :
    ∫ x in D ∪ ⋃ p ∈ P, T p, f x = (∫ x in D, f x) + ∑ p ∈ P, ∫ x in T p, f x := by
  rw [setIntegral_union (Set.disjoint_iUnion₂_right.2 hDT) (Finset.measurableSet_biUnion P hT) iD
    (integrableOn_finset_iUnion.2 iT), integral_biUnion_finset P hT hTT iT]

theorem exists_radius_lower {P : Finset ℂ} {r : ℂ → ℝ} (hr : ∀ p ∈ P, 0 < r p) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ P, m ≤ r p := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image P r hne
    exact ⟨r p₀, hr p₀ hp₀, hmin⟩

/-- **Truncation identity** (sphere note, Lemma 3.10). -/
theorem truncation_identity {G : Set ℂ} {P : Finset ℂ} {H ϱ : ℂ → ℝ} {r : ℂ → ℝ}
    (hH : PunctureAdmissible G P H) (hϱ : ContDiffOn ℝ 1 ϱ G)
    (hΔ : ∀ x ∈ G, x ∉ (P : Set ℂ) → Laplacian.laplacian H x = 2 * Real.pi * ϱ x)
    (hr : ∀ p ∈ P, 0 < r p) (hsub : ∀ p ∈ P, Metric.closedBall p (r p) ⊆ G)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint (Metric.closedBall p (r p)) (Metric.closedBall q (r q))) :
    punctureEnergy G P H =
      (1 / 2 : ℝ) * (∫ x in G, ‖gradient (fun y => H y - ∑ p ∈ P, truncLog (r p) (y - p)) x‖ ^ 2) +
        Real.pi * ∑ p ∈ P, Real.log (r p) -
        2 * Real.pi * ∑ p ∈ P, ∫ x in Metric.ball p (r p), truncLog (r p) (x - p) * ϱ x := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_radius_lower hr
  have hϱc : ContinuousOn ϱ G := hϱ.continuousOn
  have hno : ∀ p ∈ P, ∀ q ∈ P, q ≠ p → q ∉ Metric.closedBall p (r p) := fun p hp q hq hqp hqm =>
    (Set.disjoint_left.1 (hdisj p hp q hq (Ne.symm hqp))) hqm
      (Metric.mem_closedBall_self (hr q hq).le)
  have hloc : ∀ p ∈ P, ∃ u : ℂ → ℝ, ContDiffAt ℝ 1 u p ∧
      (∀ x, x ≠ p → ‖x - p‖ ≤ r p → ContDiffAt ℝ 2 u x) ∧
      (∀ x, x ≠ p → ‖x - p‖ ≤ r p → Laplacian.laplacian u x = 2 * Real.pi * ϱ x) ∧
      (∀ x, x ≠ p → u x = H x + Real.log ‖x - p‖ - Real.log (r p)) ∧
      (∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < r p → H x = u x + truncLog (r p) (x - p)) :=
    fun p hp => exists_local_potential hH hΔ hp (hsub p hp) (hno p hp)
  choose! u hu1 hu2 hu3 hu4 hu5 using hloc
  set Hα : ℂ → ℝ := fun y => H y - ∑ p ∈ P, truncLog (r p) (y - p) with hHα
  set D₀ : Set ℂ := G \ ⋃ p ∈ P, Metric.ball p (r p) with hD₀
  set T : ℂ → ℝ → Set ℂ := fun p η => {x : ℂ | ‖x - p‖ ∈ Ico η (r p)} with hT
  have hGopen : IsOpen G := hH.isOpen
  have hD₀m : MeasurableSet D₀ :=
    hGopen.measurableSet.diff
      (Finset.measurableSet_biUnion P fun p _ => Metric.isOpen_ball.measurableSet)
  have hTm : ∀ p η, MeasurableSet (T p η) := fun p η =>
    measurable_norm.comp (measurable_id.sub measurable_const) measurableSet_Ico
  have hballG : ∀ p ∈ P, Metric.ball p (r p) ⊆ G := fun p hp =>
    Metric.ball_subset_closedBall.trans (hsub p hp)
  have hbdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (Metric.ball p (r p)) (Metric.ball q (r q)) :=
    fun p hp q hq hpq => (hdisj p hp q hq hpq).mono Metric.ball_subset_closedBall
      Metric.ball_subset_closedBall
  have hTball : ∀ p η, T p η ⊆ Metric.ball p (r p) := fun p η x hx => by
    rw [mem_ball_iff_norm]; exact hx.2
  have hTT : ∀ η, (↑P : Set ℂ).Pairwise (Function.onFun Disjoint fun p => T p η) :=
    fun η p hp q hq hpq => (hbdisj p hp q hq hpq).mono (hTball p η) (hTball q η)
  have hDT : ∀ η, ∀ p ∈ P, Disjoint D₀ (T p η) := fun η p hp =>
    Set.disjoint_left.2 fun x hxD hxT => hxD.2 (Set.mem_biUnion hp (hTball p η hxT))
  have hq_far : ∀ p ∈ P, ∀ y ∈ Metric.ball p (r p), ∀ q ∈ P, q ≠ p → r q ≤ ‖y - q‖ := by
    intro p hp y hy q hq hqp
    by_contra hlt
    rw [not_le] at hlt
    have h1 : y ∈ Metric.closedBall q (r q) := by rw [mem_closedBall_iff_norm]; exact hlt.le
    exact Set.disjoint_left.1 (hdisj p hp q hq (Ne.symm hqp)) (Metric.ball_subset_closedBall hy) h1
  have hα_far : ∀ y : ℂ, (∀ p ∈ P, r p ≤ ‖y - p‖) → Hα y = H y := by
    intro y hy
    simp only [hHα]
    rw [Finset.sum_eq_zero fun p hp => Screening.truncLog_eq_zero (hr p hp) (hy p hp), sub_zero]
  have hα_ball : ∀ p ∈ P, ∀ y ∈ Metric.ball p (r p), y ≠ p → Hα y = u p y := by
    intro p hp y hy hyp
    have hn : ‖y - p‖ < r p := mem_ball_iff_norm.1 hy
    have hn0 : 0 < ‖y - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hyp)
    simp only [hHα]
    rw [Finset.sum_eq_single p (fun q hq hqp => Screening.truncLog_eq_zero (hr q hq)
      (hq_far p hp y hy q hq hqp)) (fun h => absurd hp h), hu5 p hp y hn0 hn]
    ring
  -- gradients agree almost everywhere
  have hsph : ∀ᵐ x : ℂ ∂volume, ∀ p ∈ P, ‖x - p‖ ≠ r p := by
    refine (Filter.eventually_all_finset P).2 fun p _ => ?_
    have h0 : volume (Metric.sphere p (r p)) = 0 := Measure.addHaar_sphere volume p (r p)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx h
    exact hx (mem_sphere_iff_norm.2 h)
  have hgD : ∀ᵐ x : ℂ ∂volume.restrict D₀, ‖gradient Hα x‖ ^ 2 = ‖gradient H x‖ ^ 2 := by
    refine (ae_restrict_iff' hD₀m).2 ?_
    filter_upwards [hsph] with x hx hxD
    have hfar : ∀ p ∈ P, r p < ‖x - p‖ := fun p hp => by
      have h1 : r p ≤ ‖x - p‖ := by
        by_contra hlt
        rw [not_le] at hlt
        exact hxD.2 (Set.mem_biUnion hp (mem_ball_iff_norm.2 hlt))
      exact lt_of_le_of_ne h1 (Ne.symm (hx p hp))
    have hopen : IsOpen (⋂ p ∈ P, {y : ℂ | r p < ‖y - p‖}) :=
      isOpen_biInter_finset fun p _ =>
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    have hev : Hα =ᶠ[𝓝 x] H := by
      filter_upwards [hopen.mem_nhds (Set.mem_iInter₂.2 fun p hp => hfar p hp)] with y hy
      exact hα_far y fun p hp => (Set.mem_iInter₂.1 hy p hp).le
    rw [Screening.gradient_congr_nhds hev]
  have hgB : ∀ p ∈ P, ∀ᵐ x : ℂ ∂volume.restrict (Metric.ball p (r p)),
      ‖gradient Hα x‖ ^ 2 = ‖gradient (u p) x‖ ^ 2 := by
    intro p hp
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 ?_
    filter_upwards [(Set.countable_singleton p).ae_notMem volume] with x hx hxb
    have hxp : x ≠ p := hx
    have hopen : IsOpen (Metric.ball p (r p) ∩ {y : ℂ | y ≠ p}) :=
      Metric.isOpen_ball.inter isOpen_ne
    have hev : Hα =ᶠ[𝓝 x] u p := by
      filter_upwards [hopen.mem_nhds ⟨hxb, hxp⟩] with y hy
      exact hα_ball p hp y hy.1 hy.2
    rw [Screening.gradient_congr_nhds hev]
  -- integrability
  have hfin : ∀ η : ℝ, 0 < η →
      IntegrableOn (fun x => ‖gradient H x‖ ^ 2) (G \ ⋃ p ∈ P, Metric.ball p η) :=
    hH.finite_energy
  have hD₀η : ∀ η : ℝ, η ≤ m → D₀ ⊆ G \ ⋃ p ∈ P, Metric.ball p η := fun η hηm x hx =>
    ⟨hx.1, fun h => by
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 h
      exact hx.2 (Set.mem_biUnion hp (Metric.ball_subset_ball (hηm.trans (hm p hp)) hxp))⟩
  have iD : IntegrableOn (fun x => ‖gradient H x‖ ^ 2) D₀ := (hfin m hm0).mono_set (hD₀η m le_rfl)
  have hTsub : ∀ η : ℝ, η ≤ m → ∀ p ∈ P, T p η ⊆ G \ ⋃ q ∈ P, Metric.ball q η := by
    intro η hηm p hp x hx
    refine ⟨hballG p hp (hTball p η hx), fun h => ?_⟩
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 h
    by_cases hqp : q = p
    · subst hqp; exact absurd (mem_ball_iff_norm.1 hxq) (not_lt.2 hx.1)
    · have h1 : x ∈ Metric.closedBall q (r q) :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball (hηm.trans (hm q hq)) hxq)
      exact Set.disjoint_left.1 (hdisj p hp q hq (Ne.symm hqp))
        (Metric.ball_subset_closedBall (hTball p η hx)) h1
  have iDα : IntegrableOn (fun x => ‖gradient Hα x‖ ^ 2) D₀ := iD.congr_fun_ae (hgD.mono fun x hx => hx.symm)
  have iBα : ∀ p ∈ P, IntegrableOn (fun x => ‖gradient Hα x‖ ^ 2) (Metric.ball p (r p)) :=
    fun p hp => (integrableOn_norm_gradient_sq_at (hu1 p hp) (hu2 p hp)).congr_fun_ae ((hgB p hp).mono fun x hx => hx.symm)
  -- decompositions
  have hsetη : ∀ η : ℝ, η ≤ m → G \ ⋃ p ∈ P, Metric.ball p η = D₀ ∪ ⋃ p ∈ P, T p η := by
    intro η hηm
    refine Set.Subset.antisymm ?_ (Set.union_subset (hD₀η η hηm)
      (Set.iUnion₂_subset fun p hp => hTsub η hηm p hp))
    rintro x ⟨hxG, hxn⟩
    by_cases hex : ∃ p ∈ P, x ∈ Metric.ball p (r p)
    · obtain ⟨p, hp, hxp⟩ := hex
      right
      refine Set.mem_biUnion hp ⟨?_, mem_ball_iff_norm.1 hxp⟩
      by_contra hlt
      rw [not_le] at hlt
      exact hxn (Set.mem_biUnion hp (mem_ball_iff_norm.2 hlt))
    · left
      exact ⟨hxG, fun h => hex (by obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 h; exact ⟨p, hp, hxp⟩)⟩
  have hsetG : G = D₀ ∪ ⋃ p ∈ P, Metric.ball p (r p) := by
    refine Set.Subset.antisymm ?_ (Set.union_subset Set.sdiff_subset
      (Set.iUnion₂_subset fun p hp => hballG p hp))
    intro x hxG
    by_cases hex : ∃ p ∈ P, x ∈ Metric.ball p (r p)
    · obtain ⟨p, hp, hxp⟩ := hex
      exact Or.inr (Set.mem_biUnion hp hxp)
    · exact Or.inl ⟨hxG, fun h => hex (by
        obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 h; exact ⟨p, hp, hxp⟩)⟩
  have hI_η : ∀ η : ℝ, 0 < η → η ≤ m →
      ∫ x in G \ ⋃ p ∈ P, Metric.ball p η, ‖gradient H x‖ ^ 2 =
        (∫ x in D₀, ‖gradient H x‖ ^ 2) + ∑ p ∈ P, ∫ x in T p η, ‖gradient H x‖ ^ 2 := by
    intro η hη hηm
    rw [hsetη η hηm]
    exact setIntegral_union_finset (fun p _ => hTm p η) (hDT η) (hTT η) iD
      (fun p hp => (hfin η hη).mono_set (hTsub η hηm p hp))
  have hI_G : ∫ x in G, ‖gradient Hα x‖ ^ 2 = (∫ x in D₀, ‖gradient Hα x‖ ^ 2) +
      ∑ p ∈ P, ∫ x in Metric.ball p (r p), ‖gradient Hα x‖ ^ 2 := by
    have := setIntegral_union_finset (f := fun x => ‖gradient Hα x‖ ^ 2) (D := D₀)
      (T := fun p => Metric.ball p (r p)) (P := P) (fun p _ => Metric.isOpen_ball.measurableSet)
      (fun p hp => Set.disjoint_left.2 fun x hxD hxb => hxD.2 (Set.mem_biUnion hp hxb))
      (fun p hp q hq hpq => hbdisj p hp q hq hpq) iDα iBα
    rwa [← hsetG] at this
  have hDeq : ∫ x in D₀, ‖gradient Hα x‖ ^ 2 = ∫ x in D₀, ‖gradient H x‖ ^ 2 :=
    integral_congr_ae hgD
  have hBeq : ∀ p ∈ P, ∫ x in Metric.ball p (r p), ‖gradient Hα x‖ ^ 2 =
      ∫ x in Metric.ball p (r p), ‖gradient (u p) x‖ ^ 2 := fun p hp => integral_congr_ae (hgB p hp)
  -- the limit
  have hlim : ∀ p ∈ P, Tendsto (fun η : ℝ => (1 / 2 : ℝ) * (∫ x in T p η, ‖gradient H x‖ ^ 2) +
      Real.pi * Real.log η) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * (∫ x in Metric.ball p (r p), ‖gradient (u p) x‖ ^ 2) +
        Real.pi * Real.log (r p) -
        2 * Real.pi * ∫ x in Metric.ball p (r p), truncLog (r p) (x - p) * ϱ x)) := fun p hp =>
    tendsto_annulus_energy_at (H₁ := H) (hr p hp) (hu1 p hp) (hu2 p hp) (hϱc.mono (hsub p hp))
      (hu3 p hp) (hu5 p hp)
  have hsum := tendsto_finsetSum P hlim
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η ≤ m := by
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hm0] with η h1 h2 using ⟨h1, h2.2⟩
  have hmain := (hsum.const_add ((1 / 2 : ℝ) * ∫ x in D₀, ‖gradient H x‖ ^ 2)).congr'
    (f₂ := punctureTrunc G P H) (by
    filter_upwards [hev] with η hη
    simp only [punctureTrunc]
    rw [hI_η η hη.1 hη.2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring)
  have hEq : punctureEnergy G P H = (1 / 2 : ℝ) * (∫ x in D₀, ‖gradient H x‖ ^ 2) +
      ∑ p ∈ P, ((1 / 2 : ℝ) * (∫ x in Metric.ball p (r p), ‖gradient (u p) x‖ ^ 2) +
        Real.pi * Real.log (r p) -
        2 * Real.pi * ∫ x in Metric.ball p (r p), truncLog (r p) (x - p) * ϱ x) :=
    hmain.limUnder_eq
  rw [hEq, hI_G, hDeq, Finset.sum_congr rfl hBeq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end Sphere

end SandierSerfaty

end
