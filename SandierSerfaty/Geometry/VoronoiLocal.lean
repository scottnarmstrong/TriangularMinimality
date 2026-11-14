/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.Voronoi

/-!
# Local structure of a Voronoi diagram at a point

For a locally finite set of sites `P ⊆ ℂ` and a point `x`, `nearestSites P x` is the set of sites
whose cell contains `x` (the sites at minimal distance from `x`).

* `finite_nearestSites`: there are finitely many nearest sites;
* `exists_local_cone`: **local cone lemma.** Near `x`, the cell of a nearest site `r` is cut out by
  the bisectors with the other nearest sites only: there is `δ > 0` such that for `‖y - x‖ < δ`,
  `y ∈ voronoiCell P r ↔ ∀ q ∈ nearestSites P x, ‖y - r‖ ≤ ‖y - q‖`;
* `exists_extremal`, `exists_extremal'`: among at least three points on a circle about `x`, each
  point `r` has an extremal neighbour on each side: all points lie weakly to the left (resp. right)
  of the chord from `r` to it, and one strictly.


-/

open Metric Set

public section

namespace SandierSerfaty

/-- Planar cross product. -/
@[expose] def cross (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

/-- Standing hypotheses on a site set (periodic sites satisfy them). -/
structure IsVoronoiSiteSet (P : Set ℂ) : Prop where
  locallyFinite : LocallyFiniteSites P
  isBounded_cell : ∀ p ∈ P, Bornology.IsBounded (voronoiCell P p)

/-- Sites nearest to `x`. -/
@[expose] def nearestSites (P : Set ℂ) (x : ℂ) : Set ℂ := {p | p ∈ P ∧ x ∈ voronoiCell P p}

variable {P : Set ℂ} {x : ℂ}

theorem cross_conj (a b : ℂ) :
    cross ((starRingEnd ℂ) a) ((starRingEnd ℂ) b) = -cross a b := by
  simp only [cross, Complex.conj_re, Complex.conj_im]; ring

theorem norm_sub_eq_of_mem_nearestSites {p q : ℂ} (hp : p ∈ nearestSites P x)
    (hq : q ∈ nearestSites P x) : ‖x - p‖ = ‖x - q‖ :=
  le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)

/-- A site is nearest iff it is no farther than a given nearest site. -/
theorem mem_nearestSites_iff {p q : ℂ} (hp : p ∈ nearestSites P x) (hq : q ∈ P) :
    q ∈ nearestSites P x ↔ ‖x - q‖ ≤ ‖x - p‖ := by
  refine ⟨fun h => (norm_sub_eq_of_mem_nearestSites hp h).ge, fun h => ⟨hq, fun q' hq' => ?_⟩⟩
  exact h.trans (hp.2 q' hq')

theorem finite_nearestSites (hP : LocallyFiniteSites P) (x : ℂ) : (nearestSites P x).Finite := by
  rcases (nearestSites P x).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rw [h]; exact finite_empty
  · refine (hP x ‖x - p‖).subset fun q hq => ⟨hq.1, ?_⟩
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact (norm_sub_eq_of_mem_nearestSites hp hq).ge

/-- **Local cone lemma.** Near `x`, the cell of a nearest site `r` is cut out by the bisectors with
the other nearest sites only. -/
theorem exists_local_cone (hP : LocallyFiniteSites P) (x : ℂ) :
    ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ∀ r ∈ nearestSites P x,
      (y ∈ voronoiCell P r ↔ ∀ q ∈ nearestSites P x, ‖y - r‖ ≤ ‖y - q‖) := by
  rcases (nearestSites P x).eq_empty_or_nonempty with hN | ⟨p₀, hp₀⟩
  · exact ⟨1, one_pos, fun y _ r hr => by rw [hN] at hr; exact absurd hr (notMem_empty r)⟩
  set R₀ := ‖x - p₀‖ with hR₀
  set G : Set ℂ := (P ∩ closedBall x (R₀ + 1)) \ nearestSites P x with hG
  have hGfin : G.Finite := (hP x (R₀ + 1)).sdiff
  have hfar : ∀ q ∈ P, q ∉ nearestSites P x → R₀ < ‖x - q‖ := fun q hq hqN => by
    by_contra h
    exact hqN ((mem_nearestSites_iff hp₀ hq).2 (not_lt.1 h))
  obtain ⟨g, hg0, hg⟩ : ∃ g > 0, ∀ q ∈ G, g ≤ ‖x - q‖ - R₀ := by
    rcases hGfin.toFinset.eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun q hq => ?_⟩
      have : q ∈ hGfin.toFinset := hGfin.mem_toFinset.2 hq
      rw [h] at this; exact absurd this (Finset.notMem_empty q)
    · obtain ⟨q₁, hq₁, hmin⟩ := hGfin.toFinset.exists_min_image (fun q => ‖x - q‖ - R₀) h
      rw [Set.Finite.mem_toFinset] at hq₁
      refine ⟨_, ?_, fun q hq => hmin q (hGfin.mem_toFinset.2 hq)⟩
      have := hfar q₁ hq₁.1.1 hq₁.2
      linarith
  set δ := min g 1 / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, fun y hy r hr => ⟨fun h q hq => h q hq.1, fun h q hq => ?_⟩⟩
  by_cases hqN : q ∈ nearestSites P x
  · exact h q hqN
  · have hgap : R₀ + 2 * δ ≤ ‖x - q‖ := by
      by_cases hqB : ‖x - q‖ ≤ R₀ + 1
      · have := hg q ⟨⟨hq, by rwa [mem_closedBall, dist_eq_norm, norm_sub_rev]⟩, hqN⟩
        have : min g 1 ≤ g := min_le_left _ _
        linarith
      · have : min g 1 ≤ 1 := min_le_right _ _
        linarith
    have h1 : ‖y - r‖ ≤ ‖y - x‖ + ‖x - r‖ := norm_sub_le_norm_sub_add_norm_sub y x r
    have h2 : ‖x - q‖ ≤ ‖x - y‖ + ‖y - q‖ := norm_sub_le_norm_sub_add_norm_sub x y q
    have h3 : ‖x - r‖ = R₀ := norm_sub_eq_of_mem_nearestSites hr hp₀
    rw [norm_sub_rev x y] at h2
    linarith

/-! ### Extremal neighbours on a circle -/

private def dot (a b : ℂ) : ℝ := a.re * b.re + a.im * b.im

private theorem normSq_eq_dot (a : ℂ) : ‖a‖ ^ 2 = dot a a := by
  rw [Complex.sq_norm, Complex.normSq_apply, dot]

/-- For `q ≠ r` on a circle about `x`, `⟪x - r, q - r⟫ = ‖q - r‖² / 2 > 0`. -/
private theorem dot_pos_of_circle {x r q : ℂ} {R : ℝ} (hr : ‖r - x‖ = R) (hq : ‖q - x‖ = R)
    (hqr : q ≠ r) : 0 < dot (x - r) (q - r) := by
  have h1 := normSq_eq_dot (r - x)
  have h2 := normSq_eq_dot (q - x)
  have h3 : 0 < dot (q - r) (q - r) := by
    rw [← normSq_eq_dot]; have := norm_pos_iff.2 (sub_ne_zero.2 hqr); positivity
  rw [hr] at h1; rw [hq] at h2
  simp only [dot, Complex.sub_re, Complex.sub_im] at *
  nlinarith

/-- The two-dimensional identity behind the angular order seen from `r`. -/
private theorem cross_identity (e a b : ℂ) :
    dot e e * cross a b = dot e a * cross e b - cross e a * dot e b := by
  simp only [dot, cross]; ring

/-- A line through a point `r` of a circle meets the circle in at most one other point. -/
theorem eq_of_cross_eq_zero {x r p q : ℂ} {R : ℝ} (hr : ‖r - x‖ = R) (hp : ‖p - x‖ = R)
    (hq : ‖q - x‖ = R) (hpr : p ≠ r) (hqr : q ≠ r) (h : cross (p - r) (q - r) = 0) : q = p := by
  have h1 := normSq_eq_dot (r - x)
  have h2 := normSq_eq_dot (p - x)
  have h3 := normSq_eq_dot (q - x)
  rw [hr] at h1; rw [hp] at h2; rw [hq] at h3
  have hp0 : 0 < dot (p - r) (p - r) := by
    rw [← normSq_eq_dot]; have := norm_pos_iff.2 (sub_ne_zero.2 hpr); positivity
  have hq0 : 0 < dot (q - r) (q - r) := by
    rw [← normSq_eq_dot]; have := norm_pos_iff.2 (sub_ne_zero.2 hqr); positivity
  simp only [dot, cross, Complex.sub_re, Complex.sub_im] at *
  set a := p.re - r.re; set b := p.im - r.im; set c := q.re - r.re; set d := q.im - r.im
  set u := r.re - x.re; set v := r.im - x.im
  have hpc : a * a + 2 * (a * u + b * v) + b * b = 0 := by
    have e1 : (p.re - x.re) = a + u := by simp [a, u]
    have e2 : (p.im - x.im) = b + v := by simp [b, v]
    rw [e1, e2] at h2
    linear_combination h1 - h2
  have hqc : c * c + 2 * (c * u + d * v) + d * d = 0 := by
    have e1 : (q.re - x.re) = c + u := by simp [c, u]
    have e2 : (q.im - x.im) = d + v := by simp [d, v]
    rw [e1, e2] at h3
    linear_combination h1 - h3
  have hab : 0 < a * a + b * b := hp0
  set t := (a * c + b * d) / (a * a + b * b)
  have hc : c = t * a := by
    rw [div_mul_eq_mul_div, eq_div_iff hab.ne']; linear_combination (-b) * h
  have hd : d = t * b := by
    rw [div_mul_eq_mul_div, eq_div_iff hab.ne']; linear_combination a * h
  have ht0 : t ≠ 0 := by
    rintro ht
    rw [ht, zero_mul] at hc hd
    rw [hc, hd] at hq0; norm_num at hq0
  have ht1 : t = 1 := by
    rw [hc, hd] at hqc
    have h' : (a * a + b * b) * (t * (t - 1)) = 0 := by linear_combination hqc - t * hpc
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd h hab.ne'
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h ht0
      · linarith
  rw [ht1, one_mul] at hc hd
  apply Complex.ext
  · simp only [c, a] at hc; linarith
  · simp only [d, b] at hd; linarith

/-- **Extremal neighbour.** Among at least three points on a circle about `x`, each point `r` has a
neighbour `q⁺` such that all points lie weakly to the left of the directed chord `r → q⁺`, and one
strictly. -/
theorem exists_extremal {N : Finset ℂ} {x r : ℂ} {R : ℝ} (hN : ∀ q ∈ N, ‖q - x‖ = R) (hr : r ∈ N)
    (h3 : 3 ≤ N.card) :
    ∃ qp ∈ N, qp ≠ r ∧ (∀ q ∈ N, 0 ≤ cross (qp - r) (q - r)) ∧
      ∃ q ∈ N, 0 < cross (qp - r) (q - r) := by
  have hne : (N.erase r).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hr]; omega
  obtain ⟨qp, hqp, hmin⟩ := (N.erase r).exists_min_image
    (fun q => cross (x - r) (q - r) / dot (x - r) (q - r)) hne
  have hqpr : qp ≠ r := Finset.ne_of_mem_erase hqp
  have hqpN : qp ∈ N := Finset.mem_of_mem_erase hqp
  have hee : 0 < dot (x - r) (x - r) := by
    rw [← normSq_eq_dot]
    have hxr : x - r ≠ 0 := by
      intro h
      have h1 : ‖r - x‖ = 0 := by rw [← norm_neg, neg_sub, h, norm_zero]
      have h2 : ‖qp - x‖ = 0 := by rw [hN qp hqpN, ← hN r hr, h1]
      apply hqpr
      rw [norm_eq_zero, sub_eq_zero] at h1 h2
      rw [h1, h2]
    have := norm_pos_iff.2 hxr; positivity
  have hweak : ∀ q ∈ N, 0 ≤ cross (qp - r) (q - r) := by
    intro q hq
    by_cases hqr : q = r
    · subst hqr; simp [cross]
    have hdq := dot_pos_of_circle (hN r hr) (hN q hq) hqr
    have hdp := dot_pos_of_circle (hN r hr) (hN qp hqpN) hqpr
    have hm := hmin q (Finset.mem_erase.2 ⟨hqr, hq⟩)
    rw [div_le_div_iff₀ hdp hdq] at hm
    have hid := cross_identity (x - r) (qp - r) (q - r)
    have : 0 ≤ dot (x - r) (x - r) * cross (qp - r) (q - r) := by nlinarith
    exact nonneg_of_mul_nonneg_right (by linarith) hee |> fun h => by nlinarith
  refine ⟨qp, hqpN, hqpr, hweak, ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hzero : ∀ q ∈ N, q = r ∨ q = qp := by
    intro q hq
    by_cases hqr : q = r
    · exact Or.inl hqr
    · exact Or.inr (eq_of_cross_eq_zero (hN r hr) (hN qp hqpN) (hN q hq) hqpr hqr
        (le_antisymm (hcon q hq) (hweak q hq)))
  have : N ⊆ {r, qp} := fun q hq => by
    rcases hzero q hq with h | h <;> simp [h]
  have := Finset.card_le_card this
  have := Finset.card_le_two (a := r) (b := qp)
  omega

/-- **Extremal neighbour, mirror form.** -/
theorem exists_extremal' {N : Finset ℂ} {x r : ℂ} {R : ℝ} (hN : ∀ q ∈ N, ‖q - x‖ = R)
    (hr : r ∈ N) (h3 : 3 ≤ N.card) :
    ∃ qm ∈ N, qm ≠ r ∧ (∀ q ∈ N, cross (qm - r) (q - r) ≤ 0) ∧
      ∃ q ∈ N, cross (qm - r) (q - r) < 0 := by
  set c := starRingEnd ℂ
  have hinj : Function.Injective c := (starRingEnd ℂ).injective
  have hN' : ∀ q ∈ N.image c, ‖q - c x‖ = R := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hq
    rw [← map_sub, Complex.norm_conj, hN q₀ hq₀]
  have h3' : 3 ≤ (N.image c).card := by rwa [Finset.card_image_of_injective _ hinj]
  obtain ⟨qp, hqp, hqpr, hweak, q₁, hq₁, hstrict⟩ :=
    exists_extremal hN' (Finset.mem_image_of_mem c hr) h3'
  obtain ⟨qm, hqm, rfl⟩ := Finset.mem_image.1 hqp
  obtain ⟨q₂, hq₂, rfl⟩ := Finset.mem_image.1 hq₁
  refine ⟨qm, hqm, fun h => hqpr (by rw [h]), fun q hq => ?_, q₂, hq₂, ?_⟩
  · have := hweak (c q) (Finset.mem_image_of_mem c hq)
    rw [← map_sub, ← map_sub, cross_conj] at this
    linarith
  · rw [← map_sub, ← map_sub, cross_conj] at hstrict
    linarith

end SandierSerfaty

end
