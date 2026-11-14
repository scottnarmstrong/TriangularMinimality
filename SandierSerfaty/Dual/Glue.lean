/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.Gauge
public import SandierSerfaty.Dual.LipschitzGlue

/-!
# The glued trial potential

`cellH R P p z = Fpair R (‖z - p‖, gauge P p (z - p))` is the trial function of the cell of the site
`p`. `gluedH R P` takes `cellH R P p` on the cell of any nearest site `p`; it is well defined because the
cells agree on common boundaries (`cellH_eq_of_mem_two`). It is locally Lipschitz off the sites
(`exists_lipschitzOnWith_ball`), by the gluing of Lipschitz pieces over the finitely many nearest cells.
-/

open Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

variable {ι : Type*}

/-- The trial function of the cell of the site `p`: `B(r) + ∑ᵢ (r/t)^{kᵢ} Dᵢ(t)` with `t = r/gauge`. -/
@[expose] noncomputable def cellH (R : RadialData ι) (P : Set ℂ) (p z : ℂ) : ℝ :=
  Fpair R (‖z - p‖, gauge P p (z - p))

open Classical in
/-- The glued trial potential: `cellH` of any nearest site. -/
@[expose] noncomputable def gluedH (R : RadialData ι) (P : Set ℂ) (z : ℂ) : ℝ :=
  if h : ∃ p ∈ P, z ∈ voronoiCell P p then cellH R P (Classical.choose h) z else 0

variable {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ} {p p' z : ℂ}

theorem exists_cell (hS : SepSites P d₀) (z : ℂ) : ∃ p ∈ P, z ∈ voronoiCell P p :=
  exists_mem_voronoiCell hS.nonempty hS.locallyFinite z

/-- **Gluing** (matching of traces): the cells' trial functions agree on common boundaries. -/
theorem cellH_eq_of_mem_two (hS : SepSites P d₀) (hp : p ∈ P) (hp' : p' ∈ P)
    (hz : z ∈ voronoiCell P p) (hz' : z ∈ voronoiCell P p') : cellH R P p z = cellH R P p' z := by
  by_cases h : p = p'
  · rw [h]
  · obtain ⟨h1, h2⟩ := gauge_eq_one_of_mem_two hS hp hp' h hz hz'
    obtain ⟨h3, -⟩ := gauge_eq_one_of_mem_two hS hp' hp (Ne.symm h) hz' hz
    unfold cellH
    rw [h1, h3, h2]

theorem gluedH_eq_cellH (hS : SepSites P d₀) (hp : p ∈ P) (hz : z ∈ voronoiCell P p) :
    gluedH R P z = cellH R P p z := by
  have h : ∃ p ∈ P, z ∈ voronoiCell P p := ⟨p, hp, hz⟩
  simp only [gluedH, h, ↓reduceDIte]
  exact cellH_eq_of_mem_two hS (Classical.choose_spec h).1 hp (Classical.choose_spec h).2 hz

theorem lipschitzWith_norm_sub (p : ℂ) : LipschitzWith 1 (fun z : ℂ => ‖z - p‖) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  simp only [NNReal.coe_one, one_mul]
  calc |‖x - p‖ - ‖y - p‖| ≤ ‖(x - p) - (y - p)‖ := abs_norm_sub_norm_le _ _
    _ = ‖x - y‖ := by congr 1; ring

theorem lipschitzWith_gauge_sub (hS : SepSites P d₀) (hp : p ∈ P) :
    LipschitzWith (Real.toNNReal (1 / d₀)) (fun z : ℂ => gauge P p (z - p)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have := (lipschitzWith_gauge hS hp).dist_le_mul (x - p) (y - p)
  simpa [dist_sub_right] using this

/-- On the part of the cell of `p` at distance in `[a, b]` from `p`, `cellH` is Lipschitz with a
constant independent of the site. -/
theorem exists_lipschitzOnWith_cellH (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    {R₁ T₀ : ℝ} (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁) (hT : R₁ ≤ T₀)
    {M : ι → ℝ} (hM : Bnd R d₀ T₀ M) {a b : ℝ} (ha : 0 < a) :
    ∃ K : NNReal, ∀ p ∈ P,
      LipschitzOnWith K (cellH R P p) {z | z ∈ voronoiCell P p ∧ a ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ b} := by
  have hIcc : Icc a b ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le ha ht.1
  obtain ⟨KB, hKB⟩ := (hR.contDiffOn_B.mono hIcc).exists_lipschitzOnWith one_ne_zero
    (convex_Icc a b) isCompact_Icc
  have hKs := lipschitzOnWith_serF hR hM hS.pos
  refine ⟨KB + Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) * max 1 (Real.toNNReal (1 / d₀)), ?_⟩
  intro p hp
  set A := {z | z ∈ voronoiCell P p ∧ a ≤ ‖z - p‖ ∧ ‖z - p‖ ≤ b} with hA
  have h1 : LipschitzOnWith KB (fun z : ℂ => R.B ‖z - p‖) A := by
    have := hKB.comp (lipschitzWith_norm_sub p).lipschitzOnWith (s := A)
      (fun z hz => (⟨hz.2.1, hz.2.2⟩ : ‖z - p‖ ∈ Icc a b))
    rw [mul_one] at this
    exact this
  have h2 : LipschitzOnWith (Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) * max 1 (Real.toNNReal (1 / d₀)))
      (fun z : ℂ => serF R (‖z - p‖, gauge P p (z - p))) A := by
    have hmap : LipschitzWith (max 1 (Real.toNNReal (1 / d₀)))
        (fun z : ℂ => (‖z - p‖, gauge P p (z - p))) :=
      (lipschitzWith_norm_sub p).prodMk (lipschitzWith_gauge_sub hS hp)
    refine hKs.comp hmap.lipschitzOnWith (s := A) fun z hz => ?_
    have hne : z ≠ p := by
      intro h; subst h
      have h1 := hz.2.1
      rw [sub_self, norm_zero] at h1
      linarith
    exact mem_cone_of_mem_cell hS hp hR₁ hT hz.1 hne
  exact h1.add h2

/-- **`W^{1,∞}` regularity off the sites**: `gluedH` is Lipschitz on a ball about every
point which is not a site. -/
theorem exists_lipschitzOnWith_ball (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) {x : ℂ}
    (hx : x ∉ P) : ∃ K : NNReal, ∃ δ > 0, LipschitzOnWith K (gluedH R P) (ball x δ) := by
  classical
  obtain ⟨R₁, hR₁⟩ := hS.bdd
  set T₀ := max R₁ (d₀ + 1) with hT₀
  obtain ⟨M, hMs, hMb⟩ := hR.summable T₀ (lt_of_lt_of_le (by linarith) (le_max_right _ _))
  have hM : Bnd R d₀ T₀ M := ⟨hMs, hMb⟩
  have hN := finite_nearestSites hS.locallyFinite x
  obtain ⟨p₀, hp₀, hxp₀⟩ := exists_cell hS x
  have hp₀N : p₀ ∈ nearestSites P x := ⟨hp₀, hxp₀⟩
  set m := ‖x - p₀‖ with hm
  have hmpos : 0 < m := norm_pos_iff.2 (sub_ne_zero.2 fun h => hx (h ▸ hp₀))
  obtain ⟨δc, hδc, hcone⟩ := exists_local_cone hS.locallyFinite x
  set δ := min δc (m / 2) with hδ
  have hδpos : 0 < δ := lt_min hδc (by positivity)
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_cellH hR hS hR₁ (le_max_left _ _) hM
    (a := m / 2) (b := 3 * m / 2) (by positivity)
  refine ⟨K, δ, hδpos, ?_⟩
  have hcov : ball x δ ⊆ ⋃ r ∈ hN.toFinset, voronoiCell P r := by
    intro y hy
    have hyd : ‖y - x‖ < δc := by
      have := mem_ball_iff_norm.1 hy
      exact lt_of_lt_of_le this (min_le_left _ _)
    obtain ⟨r, hrN, hrmin⟩ := hN.toFinset.exists_min_image (fun r => ‖y - r‖)
      ⟨p₀, hN.mem_toFinset.2 hp₀N⟩
    have hrN' : r ∈ nearestSites P x := hN.mem_toFinset.1 hrN
    simp only [mem_iUnion]
    refine ⟨r, hrN, (hcone y hyd r hrN').2 fun q hq => hrmin q (hN.mem_toFinset.2 hq)⟩
  refine lipschitzOnWith_of_convex_cover hN.toFinset (fun r => voronoiCell P r) (convex_ball x δ)
    (fun r => isClosed_voronoiCell P r) (fun r => convex_voronoiCell P r) hcov ?_
  intro r hrF
  have hrN : r ∈ nearestSites P x := hN.mem_toFinset.1 hrF
  have hrm : ‖x - r‖ = m := norm_sub_eq_of_mem_nearestSites hrN hp₀N
  have hsub : voronoiCell P r ∩ ball x δ ⊆
      {z | z ∈ voronoiCell P r ∧ m / 2 ≤ ‖z - r‖ ∧ ‖z - r‖ ≤ 3 * m / 2} := by
    intro z hz
    refine ⟨hz.1, ?_, ?_⟩
    · have h1 : ‖z - x‖ < δ := mem_ball_iff_norm.1 hz.2
      have h2 : ‖x - r‖ ≤ ‖x - z‖ + ‖z - r‖ := norm_sub_le_norm_sub_add_norm_sub x z r
      rw [norm_sub_rev x z] at h2
      have : δ ≤ m / 2 := min_le_right _ _
      linarith
    · have h1 : ‖z - x‖ < δ := mem_ball_iff_norm.1 hz.2
      have h2 : ‖z - r‖ ≤ ‖z - x‖ + ‖x - r‖ := norm_sub_le_norm_sub_add_norm_sub z x r
      have : δ ≤ m / 2 := min_le_right _ _
      linarith
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have hrP : r ∈ P := hrN.1
  rw [gluedH_eq_cellH hS hrP hy.1, gluedH_eq_cellH hS hrP hz.1]
  exact (hK r hrP).dist_le_mul y (hsub hy) z (hsub hz)

end Dual

end SandierSerfaty

end
