/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Assembly.FiniteEnergy

/-!
# The radii `r̃ = cubeRadius C ℓ` satisfy the screening hypotheses (H3), (H4)

For the square `sq 0 t = □_t` with `t = ℓ` (screening note, `prop:I6`, hypotheses (H3), (H4)):

* `cubeRadius_eq_quarter_of_notMem`: `r̃_p = ¼` if `p ∉ □_{ℓ-2}` (depth `< 1`);
* `cubeRadius_eq_nnRadius`: `r̃_p = r_p` if `p ∈ □_{ℓ-2s}`, `s ≥ 2` (depth `≥ s ≥ 2`);
* `cubeRadius_add_le`: `r̃_p + r̃_q ≤ ‖p - q‖` for distinct `p, q ∈ C ∩ □_{ℓ-2s}`, `s ≥ 2`
  (`r_p ≤ ¼ ‖p - q‖`).
-/

open MeasureTheory Metric Filter Topology Set

public section

namespace SandierSerfaty

namespace Assembly

/-- A point of the closed square of depth `< 1` has `r̃ = ¼` (hypothesis (H3)). -/
theorem cubeRadius_eq_quarter_of_notMem (C : Set ℂ) {ℓ : ℝ} {p : ℂ} (hp : p ∉ cube (ℓ - 2)) :
    cubeRadius C ℓ p = 1 / 4 := by
  unfold cubeRadius
  by_cases hpc : p ∈ cube ℓ
  · have hlt : infDist p (frontier (cube ℓ)) < 1 := by
      obtain ⟨h1, h2, h3, h4⟩ := Screening.infDist_frontier_cube_le hpc
      by_contra hge
      apply hp
      have hre : p.re ∈ Icc (-(ℓ / 2)) (ℓ / 2) := hpc.1
      have him : p.im ∈ Icc (-(ℓ / 2)) (ℓ / 2) := hpc.2
      push Not at hge
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
    split_ifs with h1 h2
    · linarith [h1.2]
    · rfl
    · exact absurd (Or.inr hlt.le) h2
  · split_ifs with h1 h2
    · exact absurd h1.1 hpc
    · rfl
    · exact absurd (Or.inl hpc) h2

/-- A point at `‖·‖_∞`-depth `≥ s` in `□_ℓ` has distance `≥ s` from the frontier. -/
theorem le_infDist_frontier_cube {ℓ s : ℝ} (hs : 0 ≤ s) {p : ℂ} (hp : p ∈ cube (ℓ - 2 * s)) :
    s ≤ infDist p (frontier (cube ℓ)) := by
  have hre : p.re ∈ Icc (-((ℓ - 2 * s) / 2)) ((ℓ - 2 * s) / 2) := hp.1
  have him : p.im ∈ Icc (-((ℓ - 2 * s) / 2)) ((ℓ - 2 * s) / 2) := hp.2
  have hℓ : 0 ≤ ℓ := by linarith [hre.1, hre.2]
  have hne : (frontier (cube ℓ)).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨⟨0, ⟨by simp; linarith, by simp; linarith⟩, ⟨by simp; linarith, by simp; linarith⟩⟩, ?_⟩
    intro huniv
    have : ((ℓ / 2 + 1 : ℝ) : ℂ) ∈ cube ℓ := by rw [huniv]; trivial
    have h2 := this.1.2
    norm_num at h2
  rw [le_infDist hne]
  intro y hy
  have hyc : y ∈ cube ℓ := (isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hy
  have hyi : y ∉ interior (cube ℓ) := by
    exact hy.2
  have hyre : y.re ∈ Icc (-(ℓ / 2)) (ℓ / 2) := hyc.1
  have hyim : y.im ∈ Icc (-(ℓ / 2)) (ℓ / 2) := hyc.2
  have hint : ¬ (y.re ∈ Ioo (-(ℓ / 2)) (ℓ / 2) ∧ y.im ∈ Ioo (-(ℓ / 2)) (ℓ / 2)) := by
    intro h
    apply hyi
    rw [cube, Complex.interior_reProdIm, interior_Icc]
    exact h
  rw [dist_eq_norm]
  have h1 := Complex.abs_re_le_norm (p - y)
  have h2 := Complex.abs_im_le_norm (p - y)
  rw [Complex.sub_re] at h1
  rw [Complex.sub_im] at h2
  by_cases hr : y.re ∈ Ioo (-(ℓ / 2)) (ℓ / 2)
  · have hi : ¬ y.im ∈ Ioo (-(ℓ / 2)) (ℓ / 2) := fun h => hint ⟨hr, h⟩
    have : y.im = ℓ / 2 ∨ y.im = -(ℓ / 2) := by
      by_contra hcon
      push Not at hcon
      exact hi ⟨lt_of_le_of_ne hyim.1 (Ne.symm hcon.2), lt_of_le_of_ne hyim.2 hcon.1⟩
    rcases this with h | h
    · have : s ≤ |p.im - y.im| := by rw [h, abs_sub_comm, abs_of_nonneg (by linarith [him.2])]; linarith [him.2]
      linarith
    · have : s ≤ |p.im - y.im| := by rw [h, abs_of_nonneg (by linarith [him.1])]; linarith [him.1]
      linarith
  · have : y.re = ℓ / 2 ∨ y.re = -(ℓ / 2) := by
      by_contra hcon
      push Not at hcon
      exact hr ⟨lt_of_le_of_ne hyre.1 (Ne.symm hcon.2), lt_of_le_of_ne hyre.2 hcon.1⟩
    rcases this with h | h
    · have : s ≤ |p.re - y.re| := by rw [h, abs_sub_comm, abs_of_nonneg (by linarith [hre.2])]; linarith [hre.2]
      linarith
    · have : s ≤ |p.re - y.re| := by rw [h, abs_of_nonneg (by linarith [hre.1])]; linarith [hre.1]
      linarith

theorem cubeRadius_eq_nnRadius (C : Set ℂ) {ℓ s : ℝ} (hs : 2 ≤ s) {p : ℂ}
    (hp : p ∈ cube (ℓ - 2 * s)) : cubeRadius C ℓ p = nnRadius C p := by
  unfold cubeRadius
  have hpc : p ∈ cube ℓ := cube_mono (by linarith) hp
  split_ifs with h h'
  · rfl
  · exact absurd ⟨hpc, hs.trans (le_infDist_frontier_cube (by linarith) hp)⟩ h
  · exact absurd ⟨hpc, hs.trans (le_infDist_frontier_cube (by linarith) hp)⟩ h

theorem nnRadius_le_dist (C : Set ℂ) {p q : ℂ} (hq : q ∈ C) (hqp : q ≠ p) :
    nnRadius C p ≤ 1 / 4 * ‖q - p‖ := by
  unfold nnRadius
  have : sInf (insert 1 ((fun q => ‖q - p‖) '' (C \ {p}))) ≤ ‖q - p‖ :=
    csInf_le ⟨0, fun x hx => by
      rcases hx with rfl | ⟨q, -, rfl⟩
      · norm_num
      · exact norm_nonneg _⟩ (mem_insert_of_mem _ ⟨q, ⟨hq, hqp⟩, rfl⟩)
  linarith

/-- (H4): disjointness of the `r̃`-balls of the points deep inside the square. -/
theorem cubeRadius_add_le (C : Set ℂ) {ℓ s : ℝ} (hs : 2 ≤ s) {p q : ℂ} (hpC : p ∈ C) (hqC : q ∈ C)
    (hp : p ∈ cube (ℓ - 2 * s)) (hq : q ∈ cube (ℓ - 2 * s)) (hpq : p ≠ q) :
    cubeRadius C ℓ p + cubeRadius C ℓ q ≤ ‖p - q‖ := by
  rw [cubeRadius_eq_nnRadius C hs hp, cubeRadius_eq_nnRadius C hs hq]
  have h1 := nnRadius_le_dist C hqC (Ne.symm hpq)
  have h2 := nnRadius_le_dist C hpC hpq
  rw [norm_sub_rev] at h1
  linarith [norm_nonneg (p - q)]

end Assembly

end SandierSerfaty

end
