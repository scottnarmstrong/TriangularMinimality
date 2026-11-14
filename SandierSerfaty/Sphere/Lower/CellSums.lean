/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.CellFamily

/-!
# Sums over the cells of the strip energies and discrepancies (sphere note, Theorem 6.14, budget (a), (c))

`Lower.ChartCtx` collects the standing facts about a chart.  For a family of cells with `CellSpec`:

* `Lower.sum_cell_energy_le`: `∑_j ∫_{Q_j} |∇H_{1/4}|² ≤ truncDirichlet`;
* `Lower.cell_strip_energy_le`: `S_j ≤ 2 ∫_{strip⁺(K_j)} G + 2 ∫_{Q_j} |∇v_j|²`;
* `Lower.cell_discrepancy_le`: `|p_j - n̄_j| ≤ C_D ((1 + m₊) t_j + √t_j (∫_{lay(K_j)} G)^{1/2})`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The standing facts about a chart. -/
structure ChartCtx (n : ℕ) (X : Fin n → ℂ) (ρ : ℝ) : Prop where
  pos : 0 < n
  inj : Function.Injective X
  sep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖
  ne : ∀ i, ‖blowupScale n • X i‖ ≠ ρ
  le : ρ ≤ 2 * blowupScale n
  ge : blowupScale n / 2 ≤ ρ

theorem ChartCtx.one_le {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ} (h : ChartCtx n X ρ) : 1 ≤ ρ := by
  have := two_le_blowupScale h.pos
  linarith [h.ge]

theorem ChartCtx.injz {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ} (h : ChartCtx n X ρ) :
    Function.Injective fun i => blowupScale n • X i := injective_of_sep X h.sep

theorem sqAt_cell_norm_le {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (h : ChartCtx n X ρ) (hR : 0 < R)
    {j : ℤ × ℤ} (hj : j ∈ cellFin R θ ρ) {t : ℝ} (ht : t ≤ R) {x : ℂ} (hx : x ∈ sqAt (cellAt R θ j) t) :
    ‖x‖ ≤ ρ - 1 := by
  have := sqAt_cell_subset_closedBall hR h.one_le hj ht hx
  rwa [mem_closedBall, dist_zero_right] at this

theorem sum_cell_energy_le {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (h : ChartCtx n X ρ) (hR : 0 < R)
    {t : ℤ × ℤ → ℝ} (ht : ∀ j ∈ cellFin R θ ρ, t j ≤ R - 1 / 2) (J : Finset (ℤ × ℤ))
    (hJ : J ⊆ cellFin R θ ρ) :
    ∑ j ∈ J, ∫ x in sqAt (cellAt R θ j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 ≤ truncDirichlet X ρ := by
  have hQ : ∀ j ∈ J, ∀ x ∈ sqAt (cellAt R θ j) (t j), ‖x‖ ≤ ρ - 1 := fun j hj x hx =>
    sqAt_cell_norm_le h hR (hJ hj) (by linarith [ht j (hJ hj)]) hx
  have e : ∀ j ∈ J, ∫ x in sqAt (cellAt R θ j) (t j), ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 =
      ∫ x in sqAt (cellAt R θ j) (t j), gradDensity X ρ x := fun j hj =>
    setIntegral_congr_fun (measurableSet_sqAt _ _) fun x hx => (gradDensity_eq X (hQ j hj x hx)).symm
  rw [Finset.sum_congr rfl e]
  refine (sum_setIntegral_le (fun j _ => measurableSet_sqAt _ _) (fun j hj j' hj' hne =>
    sqAt_disjoint hR θ hne (by linarith [ht j (hJ hj)]) (by linarith [ht j' (hJ hj')]))
    (gradDensity_nonneg X ρ) (integrable_gradDensity h.pos X h.inj h.sep h.ne)).trans ?_
  exact integral_gradDensity_le h.pos X h.inj h.sep h.ne

theorem cell_strip_energy_le {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (h : ChartCtx n X ρ) (hR : 0 < R)
    {j : ℤ × ℤ} (hj : j ∈ cellFin R θ ρ) {t : ℝ} (ht1 : R - 1 ≤ t) (ht2 : t ≤ R - 1 / 2) {L : ℝ}
    (hL : 0 ≤ L) {v : ℂ → ℝ} (hv : ContDiff ℝ ∞ v) :
    stripEnergy (fun y => truncPot X (1 / 4) y - v y) (cellAt R θ j) t L ≤
      2 * (∫ z in stripSq R θ (L / 2) (2 * L + 1) j, gradDensity X ρ z) +
        2 * ∫ x in sqAt (cellAt R θ j) t, ‖gradC v x‖ ^ 2 := by
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  set a := cellAt R θ j with ha
  set Ω := sqShrink a t (L / 2) \ sqShrink a t (2 * L) with hΩ
  have hΩm : MeasurableSet Ω := (measurableSet_sqShrink _ _ _).diff (measurableSet_sqShrink _ _ _)
  have hΩQ : Ω ⊆ sqAt a t := Set.sdiff_subset.trans (sqShrink_subset_sqAt a t (by linarith))
  have hQ : ∀ x ∈ sqAt a t, ‖x‖ ≤ ρ - 1 := fun x hx => sqAt_cell_norm_le h hR hj (by linarith) hx
  have h1 := integral_norm_gradC_sub_le_on (locallyLipschitz_truncPot X hη) hv hΩm hΩQ (ε := 1) one_pos
  have hint : IntegrableOn (fun x => ‖gradC v x‖ ^ 2) (sqAt a t) :=
    (hasWeakGradientOn_of_locallyLipschitz ((hv.of_le (by norm_cast)).locallyLipschitz)
      (isCompact_sqAt a t)).2.1.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have e1 : ∫ x in Ω, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 = ∫ x in Ω, gradDensity X ρ x :=
    setIntegral_congr_fun hΩm fun x hx => (gradDensity_eq X (hQ x (hΩQ hx))).symm
  have e2 : ∫ x in Ω, gradDensity X ρ x ≤ ∫ x in stripSq R θ (L / 2) (2 * L + 1) j, gradDensity X ρ x :=
    setIntegral_mono_set (integrable_gradDensity h.pos X h.inj h.sep h.ne).integrableOn
      (Filter.Eventually.of_forall fun x => gradDensity_nonneg X ρ x)
      (Filter.Eventually.of_forall (strip_subset_stripSq θ j ht1 ht2 (by linarith)))
  have e3 : ∫ x in Ω, ‖gradC v x‖ ^ 2 ≤ ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => by positivity)
      (Filter.Eventually.of_forall hΩQ)
  unfold stripEnergy
  rw [← e1] at e2
  norm_num at h1
  linarith

theorem cell_layer_le {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ} (h : ChartCtx n X ρ) (hR : 0 < R)
    {j : ℤ × ℤ} (hj : j ∈ cellFin R θ ρ) {t : ℝ} (ht1 : R - 1 ≤ t) (ht2 : t ≤ R - 1 / 2) :
    ∫ x in sqShrink (cellAt R θ j) t (1 / 2) \ sqShrink (cellAt R θ j) t 1,
        ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 ≤ ∫ z in stripSq R θ (1 / 2) 2 j, gradDensity X ρ z := by
  set a := cellAt R θ j with ha
  have hΩm : MeasurableSet (sqShrink a t (1 / 2) \ sqShrink a t 1) :=
    (measurableSet_sqShrink _ _ _).diff (measurableSet_sqShrink _ _ _)
  have hΩQ : sqShrink a t (1 / 2) \ sqShrink a t 1 ⊆ sqAt a t :=
    Set.sdiff_subset.trans (sqShrink_subset_sqAt a t (by norm_num))
  have hQ : ∀ x ∈ sqAt a t, ‖x‖ ≤ ρ - 1 := fun x hx => sqAt_cell_norm_le h hR hj (by linarith) hx
  have e1 : ∫ x in sqShrink a t (1 / 2) \ sqShrink a t 1, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2 =
      ∫ x in sqShrink a t (1 / 2) \ sqShrink a t 1, gradDensity X ρ x :=
    setIntegral_congr_fun hΩm fun x hx => (gradDensity_eq X (hQ x (hΩQ hx))).symm
  rw [e1]
  have hsub := strip_subset_stripSq θ j ht1 ht2 (s₁ := 1 / 2) (s₂ := 1) (by norm_num)
  have : (1 : ℝ) + 1 = 2 := by norm_num
  rw [this] at hsub
  exact setIntegral_mono_set (integrable_gradDensity h.pos X h.inj h.sep h.ne).integrableOn
    (Filter.Eventually.of_forall fun x => gradDensity_nonneg X ρ x) (Filter.Eventually.of_forall hsub)

/-- The sum of the discrepancies over the cells. -/
theorem exists_disc_sum : ∃ C_D : ℝ, 0 ≤ C_D ∧ ∀ {n : ℕ} {X : Fin n → ℂ} {ρ R : ℝ} {θ : ℝ × ℝ}
    (_h : ChartCtx n X ρ), 3 ≤ R → ∀ {t : ℤ × ℤ → ℝ} {nb : ℤ × ℤ → ℕ} {v : ℤ × ℤ → ℂ → ℝ},
    CellSpec n R θ ρ t nb v →
    (∑ j ∈ cellFin R θ ρ, ∫ z in stripSq R θ (1 / 2) 2 j, gradDensity X ρ z) * R ≤
      12 * (2 - 1 / 2) * ∫ z, gradDensity X ρ z →
    ∑ j ∈ cellFin R θ ρ, |(nb j : ℝ) - (ptsIn X (cellAt R θ j) (t j)).card| ≤
      C_D * ((1 + mPlus) * ((cellFin R θ ρ).card * R) +
        Real.sqrt ((cellFin R θ ρ).card * R) *
          Real.sqrt (12 * (2 - 1 / 2) * (∫ z, gradDensity X ρ z) / R)) := by
  obtain ⟨C_D, hC_D, hdisc⟩ := exists_discrepancy
  refine ⟨C_D, hC_D, fun {n X ρ R θ} h hR {t nb v} spec hband => ?_⟩
  set J := cellFin R θ ρ with hJ
  have hR0 : 0 < R := by linarith
  have hint0 : 0 ≤ ∫ z, gradDensity X ρ z := integral_nonneg (gradDensity_nonneg X ρ)
  set l : ℤ × ℤ → ℝ := fun j => ∫ z in stripSq R θ (1 / 2) 2 j, gradDensity X ρ z with hl
  have hl0 : ∀ j, 0 ≤ l j := fun j => setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall (gradDensity_nonneg X ρ))
  have hper : ∀ j ∈ J, |(nb j : ℝ) - (ptsIn X (cellAt R θ j) (t j)).card| ≤
      C_D * ((1 + mPlus) * t j + Real.sqrt (t j) * Real.sqrt (l j)) := by
    intro j hj
    obtain ⟨ht1, ht2, hnb, -⟩ := spec j hj
    have hd := hdisc h.pos X h.sep (cellAt R θ j) (t := t j) (by linarith)
    rw [← hnb, ← card_ptsIn X h.injz, abs_sub_comm] at hd
    refine hd.trans ?_
    have hlay := cell_layer_le h hR0 hj ht1 ht2
    gcongr
  have hsum1 : ∑ j ∈ J, |(nb j : ℝ) - (ptsIn X (cellAt R θ j) (t j)).card| ≤
      ∑ j ∈ J, C_D * ((1 + mPlus) * t j + Real.sqrt (t j) * Real.sqrt (l j)) :=
    Finset.sum_le_sum hper
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum1
  have ht0 : ∀ j ∈ J, 0 ≤ t j := fun j hj => by linarith [(spec j hj).1]
  have hCS0 := Real.sum_sqrt_mul_sqrt_le J (f := fun j => max (t j) 0) (g := l) (fun j => le_max_right _ _) hl0
  have emax : ∀ j ∈ J, max (t j) 0 = t j := fun j hj => max_eq_left (ht0 j hj)
  have hCS : ∑ j ∈ J, Real.sqrt (t j) * Real.sqrt (l j) ≤
      Real.sqrt (∑ j ∈ J, t j) * Real.sqrt (∑ j ∈ J, l j) := by
    have e2 : ∑ j ∈ J, Real.sqrt (max (t j) 0) * Real.sqrt (l j) =
        ∑ j ∈ J, Real.sqrt (t j) * Real.sqrt (l j) :=
      Finset.sum_congr rfl fun j hj => by rw [emax j hj]
    have e3 : ∑ j ∈ J, max (t j) 0 = ∑ j ∈ J, t j := Finset.sum_congr rfl emax
    rw [e2, e3] at hCS0
    exact hCS0
  have htsum : ∑ j ∈ J, t j ≤ J.card * R := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j hj => by linarith [(spec j hj).2.1]
  have hlsum : ∑ j ∈ J, l j ≤ 12 * (2 - 1 / 2) * (∫ z, gradDensity X ρ z) / R := by
    rw [le_div_iff₀ hR0]; exact hband
  have hs1 : Real.sqrt (∑ j ∈ J, t j) ≤ Real.sqrt (J.card * R) := Real.sqrt_le_sqrt htsum
  have hs2 : Real.sqrt (∑ j ∈ J, l j) ≤ Real.sqrt (12 * (2 - 1 / 2) * (∫ z, gradDensity X ρ z) / R) :=
    Real.sqrt_le_sqrt hlsum
  have hmul := mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hc : (1 + mPlus) * ∑ j ∈ J, t j ≤ (1 + mPlus) * (J.card * R) :=
    mul_le_mul_of_nonneg_left htsum (by have := mPlus_pos; positivity)
  calc _ ≤ C_D * ((1 + mPlus) * ∑ j ∈ J, t j + ∑ j ∈ J, Real.sqrt (t j) * Real.sqrt (l j)) := hsum1
    _ ≤ C_D * ((1 + mPlus) * (J.card * R) + Real.sqrt (J.card * R) *
        Real.sqrt (12 * (2 - 1 / 2) * (∫ z, gradDensity X ρ z) / R)) := by
      gcongr
      linarith

end Lower

end Sphere

end SandierSerfaty

end
