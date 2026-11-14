/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartPartitionAux
public import SandierSerfaty.Sphere.Lower.Apriori

/-!
# Partition of the chart energy into squares (sphere note, Lemma 6.10(i) refined, Theorem 6.14 setup)

`Lower.chart_partition_lower`: for pairwise disjoint squares `Q_j ⊆ closedBall 0 (ρ - 1)`,
`∑_j (𝔉(Q_j) + π ∑_{Q_j} log λ) - C₁ #(points outside all Q_j) - π ∑ log₊(1/(2 (ρ - |p|)))
   ≤ W_{B(0,ρ)}(H) + π ∑_{inner} log λ(x_i)`.
-/

open MeasureTheory Set Filter Topology Laplacian Metric
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The per-point term of the truncation identity. -/
@[expose] noncomputable def pointTerm {n : ℕ} (X : Fin n → ℂ) (ρ : ℝ) (i : Fin n) : ℝ :=
  Real.pi * Real.log (depthRadius ρ (blowupScale n • X i)) -
    2 * Real.pi * (∫ x in ball (blowupScale n • X i) (depthRadius ρ (blowupScale n • X i)),
      truncLog (depthRadius ρ (blowupScale n • X i)) (x - blowupScale n • X i) * blowupDens n x) +
    Real.pi * Real.log (lam (X i))

theorem pointTerm_ge {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) {ρ : ℝ} (hρ2 : ρ ≤ 2 * blowupScale n) {i : Fin n}
    (hi : ‖blowupScale n • X i‖ < ρ) :
    -constC1 - Real.pi * logPlus (1 / (2 * (ρ - ‖blowupScale n • X i‖))) ≤ pointTerm X ρ i := by
  have hs := blowupScale_pos hn
  have hp := Real.pi_pos
  set p := blowupScale n • X i with hpdef
  have hα := depthRadius_pos hi
  have hlog := log_min_ge (d := ρ - ‖p‖) (by linarith)
  have e : depthRadius ρ p = min (1 / 4) ((ρ - ‖p‖) / 2) := rfl
  have hlogα : Real.log (1 / 4) - logPlus (1 / (2 * (ρ - ‖p‖))) ≤ Real.log (depthRadius ρ p) := by
    rw [e]; exact hlog
  have hsubset : ball p (depthRadius ρ p) ⊆ ball 0 ρ := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball, dist_zero_right]
    have h1 : depthRadius ρ p ≤ (ρ - ‖p‖) / 2 := min_le_right _ _
    have h3 : ‖x‖ ≤ ‖x - p‖ + ‖p‖ := by
      have := norm_add_le (x - p) p
      simpa using this
    linarith
  have hint := integral_truncLog_ball_mul_le (M := mPlus) hα (p := p) (ϱ := blowupDens n)
    (contDiff_blowupDens n).continuous.continuousOn (fun x _ => blowupDens_nonneg n x)
    (fun x _ => blowupDens_le n x)
  have hαq := depthRadius_le_quarter ρ p
  have hα2 : depthRadius ρ p ^ 2 ≤ (1 / 4) ^ 2 := by gcongr
  have hint2 : ∫ x in ball p (depthRadius ρ p), truncLog (depthRadius ρ p) (x - p) * blowupDens n x ≤
      mPlus * (Real.pi * (1 / 4) ^ 2 / 2) := by
    refine hint.trans ?_
    have := mPlus_pos
    nlinarith [mul_nonneg this.le hp.le]
  have hx : ‖X i‖ ≤ 2 := by
    rw [hpdef, norm_smul, Real.norm_of_nonneg hs.le] at hi
    by_contra h
    rw [not_le] at h
    nlinarith
  have hlam : Real.log (2 / 5) ≤ Real.log (lam (X i)) := by
    refine Real.log_le_log (by norm_num) ?_
    unfold lam
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [norm_nonneg (X i)]
  have h1 : Real.pi * Real.log (1 / 4) = -(Real.pi * Real.log 4) := by
    rw [one_div, Real.log_inv]; ring
  have h2 : Real.pi * Real.log (2 / 5) = -(Real.pi * Real.log (5 / 2)) := by
    rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num, Real.log_inv]; ring
  have h3 := mul_le_mul_of_nonneg_left hlogα hp.le
  have h4 := mul_le_mul_of_nonneg_left hlam hp.le
  have h5 := mul_le_mul_of_nonneg_left hint2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  unfold pointTerm constC1
  rw [← hpdef]
  linarith

theorem pointTerm_quarter {n : ℕ} (X : Fin n → ℂ) {ρ : ℝ} {i : Fin n}
    (hi : ‖blowupScale n • X i‖ ≤ ρ - 1) :
    pointTerm X ρ i = Real.pi * Real.log (1 / 4) -
      2 * Real.pi * (∫ x, truncLog (1 / 4) (x - blowupScale n • X i) * blowupDens n x) +
      Real.pi * Real.log (lam (X i)) := by
  have hα : depthRadius ρ (blowupScale n • X i) = 1 / 4 := by
    unfold depthRadius
    exact min_eq_left (by linarith)
  unfold pointTerm
  rw [hα]
  congr 2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [mem_ball, dist_eq_norm, not_lt] at hx
  rw [Screening.truncLog_eq_zero (by norm_num) hx, zero_mul]

theorem sum_ptsIn_eq {n : ℕ} (X : Fin n → ℂ) (hinj : Function.Injective fun i => blowupScale n • X i)
    (a : ℂ) (t : ℝ) (h : ℂ → ℝ) :
    ∑ q ∈ ptsIn X a t, h q = ∑ i ∈ Finset.univ.filter (fun i => blowupScale n • X i ∈ sqAt a t),
      h (blowupScale n • X i) := by
  rw [ptsIn_eq, Finset.sum_image (fun i _ j _ hij => hinj hij)]

theorem sum_innerBlown_eq {n : ℕ} (X : Fin n → ℂ) (hinj : Function.Injective fun i => blowupScale n • X i)
    (ρ : ℝ) (h : ℂ → ℝ) :
    ∑ p ∈ innerBlown X ρ, h p = ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ),
      h (blowupScale n • X i) := by
  unfold innerBlown
  rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]

/-- The chart energy is bounded below by the sum over disjoint squares. -/
theorem chart_partition_lower {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖)
    {ρ : ℝ} (_hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2 * blowupScale n) (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ)
    {ι : Type*} (J : Finset ι) (a : ι → ℂ) (t : ι → ℝ)
    (hsq : ∀ j ∈ J, ∀ x ∈ sqAt (a j) (t j), ‖x‖ ≤ ρ - 1)
    (hdisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (sqAt (a j) (t j)) (sqAt (a j') (t j'))) :
    ∑ j ∈ J, (fnQ X (a j) (t j) + chartSum X (a j) (t j)) -
      constC1 * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ ∧
        ¬ ∃ j ∈ J, blowupScale n • X i ∈ sqAt (a j) (t j)).card : ℝ) -
      Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
    punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
      Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ), Real.log (lam (X i)) := by
  have hs := blowupScale_pos hn
  have hp := Real.pi_pos
  have hinj := injective_of_sep X hsep
  set Z := innerBlown X ρ with hZ
  set inner : Finset (Fin n) := Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ) with hinner
  -- admissibility etc.
  have hadm := blowupPot_admissible hn X hX hρ
  have hmem : ∀ p ∈ Z, ∃ i, ‖blowupScale n • X i‖ < ρ ∧ blowupScale n • X i = p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩
  have hΔ : ∀ x ∈ ball (0 : ℂ) ρ, x ∉ (↑Z : Set ℂ) →
      Laplacian.laplacian (blowupPot X) x = 2 * Real.pi * blowupDens n x := by
    intro x hx hxP
    refine laplacian_blowupPot hn X fun i h => ?_
    rcases lt_or_gt_of_ne (hρ i) with hlt | hgt
    · exact hxP (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩, h.symm⟩))
    · rw [mem_ball, dist_zero_right] at hx
      rw [h] at hx
      linarith
  have hsepZ : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → 1 ≤ ‖p - q‖ := by
    intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := hmem p hp
    obtain ⟨j, hj, rfl⟩ := hmem q hq
    exact hsep i j fun h => hpq (by rw [h])
  have hρ' : ∀ p ∈ Z, ‖p‖ < ρ := fun p hp => by
    have := hadm.subset hp
    simpa using this
  have hϱ : ContDiffOn ℝ 1 (blowupDens n) (ball (0 : ℂ) ρ) :=
    ((contDiff_blowupDens n).of_le (by exact_mod_cast le_top)).contDiffOn
  have heq := chart_truncation_eq hadm hϱ hΔ hsepZ
  have hint := integrableOn_truncated_grad hadm hΔ (fun p hp => depthRadius_pos (hρ' p hp))
    (fun p hp => depthRadius_closedBall_subset hρ' hp)
    (fun p hp q hq hpq => depthRadius_disjoint hsepZ hp hq hpq)
  set g : ℂ → ℝ := fun x => ‖gradient (fun y => blowupPot X y -
    ∑ p ∈ Z, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2 with hg
  -- the partition of the Dirichlet energy
  have hQball : ∀ j ∈ J, sqAt (a j) (t j) ⊆ ball (0 : ℂ) ρ := by
    intro j hj x hx
    rw [mem_ball, dist_zero_right]
    linarith [hsq j hj x hx]
  have hpart : ∑ j ∈ J, ∫ x in sqAt (a j) (t j), g x ≤ ∫ x in ball (0 : ℂ) ρ, g x := by
    rw [← integral_biUnion_finset J (fun j _ => measurableSet_sqAt (a j) (t j))
      (fun j hj j' hj' hne => hdisj j hj j' hj' hne)
      (fun j hj => hint.mono_set (hQball j hj))]
    refine setIntegral_mono_set hint (Eventually.of_forall fun x => by simp [hg]) ?_
    exact Eventually.of_forall fun x hx => by
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hx
      exact hQball j hj hxj
  have hAj : ∀ j ∈ J, ∫ x in sqAt (a j) (t j), g x =
      ∫ x in sqAt (a j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 :=
    fun j hj => integral_sq_trunc_eq hn X hinj (measurableSet_sqAt _ _) (hsq j hj)
  -- the pointwise terms
  have hsum : punctureEnergy (ball 0 ρ) Z (blowupPot X) + Real.pi * ∑ i ∈ inner, Real.log (lam (X i)) =
      1 / 2 * (∫ x in ball (0 : ℂ) ρ, g x) + ∑ i ∈ inner, pointTerm X ρ i := by
    rw [heq]
    unfold pointTerm
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, sum_innerBlown_eq X hinj ρ (fun p => Real.log (depthRadius ρ p)),
      sum_innerBlown_eq X hinj ρ (fun p => ∫ x in ball p (depthRadius ρ p),
        truncLog (depthRadius ρ p) (x - p) * blowupDens n x)]
    ring
  -- split the points into those in the squares and the rest
  set G : Fin n → Prop := fun i => ∃ j ∈ J, blowupScale n • X i ∈ sqAt (a j) (t j) with hG
  set F : ι → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i => blowupScale n • X i ∈ sqAt (a j) (t j)) with hF
  have hFdisj : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (F j) (F j') := by
    intro j hj j' hj' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact Set.disjoint_left.1 (hdisj j hj j' hj' hne) (Finset.mem_filter.1 hi).2
      (Finset.mem_filter.1 hi').2
  have hfilter : inner.filter G = J.biUnion F := by
    ext i
    simp only [hinner, hG, hF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨-, j, hj, hij⟩; exact ⟨j, hj, hij⟩
    · rintro ⟨j, hj, hij⟩
      refine ⟨?_, j, hj, hij⟩
      have := hsq j hj _ hij
      linarith
  have hsplit := Finset.sum_filter_add_sum_filter_not inner G (pointTerm X ρ)
  rw [hfilter, Finset.sum_biUnion (fun j hj j' hj' hne => hFdisj j hj j' hj' hne)] at hsplit
  have hrest_filter : inner.filter (fun i => ¬ G i) = Finset.univ.filter fun i =>
      ‖blowupScale n • X i‖ < ρ ∧ ¬ ∃ j ∈ J, blowupScale n • X i ∈ sqAt (a j) (t j) := by
    ext i
    simp [hinner, hG, Finset.mem_filter]
  -- the square terms
  have hsqterm : ∀ j ∈ J, ∑ i ∈ F j, pointTerm X ρ i =
      fnQ X (a j) (t j) + chartSum X (a j) (t j) -
        1 / 2 * ∫ x in sqAt (a j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 := by
    intro j hj
    have h1 : ∀ i ∈ F j, pointTerm X ρ i = (Real.pi * Real.log (1 / 4) -
        2 * Real.pi * (∫ x, truncLog (1 / 4) (x - blowupScale n • X i) * blowupDens n x)) +
        Real.pi * Real.log (lam (X i)) := by
      intro i hi
      rw [pointTerm_quarter X (hsq j hj _ (Finset.mem_filter.1 hi).2)]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h2 := sum_ptsIn_eq X hinj (a j) (t j) (fun q => Real.pi * Real.log (1 / 4) -
      2 * Real.pi * ∫ x, truncLog (1 / 4) (x - q) * blowupDens n x)
    unfold fnQ chartSum
    rw [h2]
    ring
  -- the rest
  have hrest : ∀ i ∈ inner.filter (fun i => ¬ G i), -constC1 -
      Real.pi * logPlus (1 / (2 * (ρ - ‖blowupScale n • X i‖))) ≤ pointTerm X ρ i :=
    fun i hi => pointTerm_ge hn X hρ2 (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2
  have hrest_sum : -(constC1 * ((inner.filter (fun i => ¬ G i)).card : ℝ)) -
      Real.pi * ∑ i ∈ inner, logPlus (1 / (2 * (ρ - ‖blowupScale n • X i‖))) ≤
      ∑ i ∈ inner.filter (fun i => ¬ G i), pointTerm X ρ i := by
    have h1 := Finset.sum_le_sum hrest
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
    have h2 : ∑ i ∈ inner.filter (fun i => ¬ G i), logPlus (1 / (2 * (ρ - ‖blowupScale n • X i‖))) ≤
        ∑ i ∈ inner, logPlus (1 / (2 * (ρ - ‖blowupScale n • X i‖))) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => logPlus_nonneg _
    have h3 := mul_le_mul_of_nonneg_left h2 hp.le
    linarith
  have hΛ : ∑ p ∈ Z, logPlus (1 / (2 * (ρ - ‖p‖))) =
      ∑ i ∈ inner, logPlus (1 / (2 * (ρ - ‖blowupScale n • X i‖))) :=
    sum_innerBlown_eq X hinj ρ (fun p => logPlus (1 / (2 * (ρ - ‖p‖))))
  rw [Finset.sum_congr rfl hsqterm] at hsplit
  have hAsum : ∑ j ∈ J, ∫ x in sqAt (a j) (t j), g x =
      ∑ j ∈ J, ∫ x in sqAt (a j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 :=
    Finset.sum_congr rfl hAj
  rw [hrest_filter] at hrest_sum hsplit
  rw [hΛ]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hsplit
  have h12 : 1 / 2 * ∑ j ∈ J, ∫ x in sqAt (a j) (t j), g x ≤ 1 / 2 * ∫ x in ball (0 : ℂ) ρ, g x := by
    linarith
  rw [Finset.sum_add_distrib]
  rw [hAsum] at h12
  linarith [hsum]

theorem integrableOn_chart_grad {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {ρ : ℝ}
    (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ) :
    IntegrableOn (fun x => ‖gradient (fun y => blowupPot X y -
      ∑ p ∈ innerBlown X ρ, truncLog (depthRadius ρ p) (y - p)) x‖ ^ 2) (ball (0 : ℂ) ρ) := by
  have hadm := blowupPot_admissible hn X hX hρ
  have hmem : ∀ p ∈ innerBlown X ρ, ∃ i, ‖blowupScale n • X i‖ < ρ ∧ blowupScale n • X i = p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨i, (Finset.mem_filter.1 hi).2, rfl⟩
  have hΔ : ∀ x ∈ ball (0 : ℂ) ρ, x ∉ (↑(innerBlown X ρ) : Set ℂ) →
      Laplacian.laplacian (blowupPot X) x = 2 * Real.pi * blowupDens n x := by
    intro x hx hxP
    refine laplacian_blowupPot hn X fun i h => ?_
    rcases lt_or_gt_of_ne (hρ i) with hlt | hgt
    · exact hxP (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩, h.symm⟩))
    · rw [mem_ball, dist_zero_right] at hx
      rw [h] at hx
      linarith
  have hsepZ : ∀ p ∈ innerBlown X ρ, ∀ q ∈ innerBlown X ρ, p ≠ q → 1 ≤ ‖p - q‖ := by
    intro p hp q hq hpq
    obtain ⟨i, hi, rfl⟩ := hmem p hp
    obtain ⟨j, hj, rfl⟩ := hmem q hq
    exact hsep i j fun h => hpq (by rw [h])
  have hρ' : ∀ p ∈ innerBlown X ρ, ‖p‖ < ρ := fun p hp => by
    have := hadm.subset hp
    simpa using this
  exact integrableOn_truncated_grad hadm hΔ (fun p hp => depthRadius_pos (hρ' p hp))
    (fun p hp => depthRadius_closedBall_subset hρ' hp)
    (fun p hp q hq hpq => depthRadius_disjoint hsepZ hp hq hpq)

theorem integrableOn_E_closedBall {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {ρ : ℝ}
    (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ) :
    IntegrableOn (fun x => ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) (closedBall (0 : ℂ) (ρ - 1)) := by
  have hinj := injective_of_sep X hsep
  have hsub : closedBall (0 : ℂ) (ρ - 1) ⊆ ball (0 : ℂ) ρ := closedBall_subset_ball (by linarith)
  have h := (integrableOn_chart_grad hn X hX hsep hρ).mono_set hsub
  exact h.congr_fun_ae (ae_sq_trunc_eq hn X hinj measurableSet_closedBall
    (fun x hx => by simpa using hx))

theorem integral_E_le_truncDirichlet {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {ρ : ℝ}
    (hρ : ∀ i, ‖blowupScale n • X i‖ ≠ ρ) :
    ∫ x in closedBall (0 : ℂ) (ρ - 1), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 ≤ truncDirichlet X ρ := by
  have hinj := injective_of_sep X hsep
  have hsub : closedBall (0 : ℂ) (ρ - 1) ⊆ ball (0 : ℂ) ρ := closedBall_subset_ball (by linarith)
  rw [← integral_sq_trunc_eq hn X hinj measurableSet_closedBall (fun x hx => by simpa using hx)]
  unfold truncDirichlet
  exact setIntegral_mono_set (integrableOn_chart_grad hn X hX hsep hρ)
    (Filter.Eventually.of_forall fun x => by positivity) (Filter.Eventually.of_forall hsub)

end Lower

end Sphere

end SandierSerfaty

end
