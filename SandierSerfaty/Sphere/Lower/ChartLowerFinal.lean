/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ChartLargeError

/-!
# The lower bound for one chart, with explicit error (sphere note, Theorem 6.14, per-chart form)

`Lower.chart_lower_bound`: under `TorusBoundStatement` and `Input63Statement`, for `L ≥ L₀` and every chart (`ChartCtx`) whose
truncated Dirichlet energy is at most `C_A n`,
`c_* #inner - K₁ n / L - K₂ L⁸ √n - π ∑ log₊(1/(2(ρ - |p|))) ≤ W_{B(0,ρ)}(H) + π ∑ log λ`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem chart_lower_small {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ} (h : ChartCtx n X ρ) {L : ℝ} (hL1 : 1 ≤ L)
    (hsmall : Real.sqrt n < L ^ 4) {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    cStar * ((innerBlown X ρ).card : ℝ) - K₁ * ((n : ℝ) / L) -
        (K₂ + (constC1 + |cStar|)) * (L ^ 8 * Real.sqrt n) -
        Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
      punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
        Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ), Real.log (lam (X i)) := by
  have hC1' := constC1_nonneg
  have hL0 : 0 < L := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.pos
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos h.one_le
  have hpart := chart_partition_lower h.pos X h.inj h.sep hρ0 h.le h.ne (∅ : Finset (ℤ × ℤ))
    (fun _ => (0 : ℂ)) (fun _ => (0 : ℝ)) (by simp) (by simp)
  simp only [Finset.sum_empty, Finset.notMem_empty, false_and, exists_false, not_false_eq_true, and_true,
    zero_sub] at hpart
  have hcard : ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) ≤ n := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i => ‖blowupScale n • X i‖ < ρ
    simpa using (Nat.cast_le (α := ℝ)).2 this
  have hin : ((innerBlown X ρ).card : ℝ) =
      ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) := by
    rw [card_innerBlown h.pos X h.inj ρ]
  have hnn : (n : ℝ) ≤ L ^ 8 * Real.sqrt n := by
    have h1 : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (by positivity)).symm
    have h2 : Real.sqrt n * Real.sqrt n ≤ Real.sqrt n * L ^ 4 :=
      mul_le_mul_of_nonneg_left hsmall.le (Real.sqrt_nonneg _)
    have h3 : L ^ 4 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    have h4 : Real.sqrt n * L ^ 4 ≤ Real.sqrt n * L ^ 8 :=
      mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    nlinarith
  have hc10 : 0 ≤ constC1 + |cStar| := by positivity
  have hcs : cStar * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) ≤
      |cStar| * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
  have h6 : (constC1 + |cStar|) * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) ≤
      (constC1 + |cStar|) * (L ^ 8 * Real.sqrt n) := mul_le_mul_of_nonneg_left (hcard.trans hnn) hc10
  have h7 : 0 ≤ K₁ * ((n : ℝ) / L) := by positivity
  have h8 : 0 ≤ K₂ * (L ^ 8 * Real.sqrt n) := by positivity
  have e1 : (constC1 + |cStar|) * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) =
      constC1 * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) +
        |cStar| * ((Finset.univ.filter fun i => ‖blowupScale n • X i‖ < ρ).card : ℝ) := by ring
  have e2 : (K₂ + (constC1 + |cStar|)) * (L ^ 8 * Real.sqrt n) =
      K₂ * (L ^ 8 * Real.sqrt n) + (constC1 + |cStar|) * (L ^ 8 * Real.sqrt n) := by ring
  rw [hin]
  linarith [hpart, hcs, h6, h7, h8, e1, e2]

theorem chart_lower_bound (hR1 : Assembly.TorusBoundStatement) (hI : Input63Statement) {CA : ℝ} (hCA : 0 ≤ CA) :
    ∃ K₁ K₂ L₀ : ℝ, 1 ≤ L₀ ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ {L : ℝ}, L₀ ≤ L → ∀ {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ},
      ChartCtx n X ρ → truncDirichlet X ρ ≤ CA * n →
      cStar * ((innerBlown X ρ).card : ℝ) - K₁ * (n / L) - K₂ * (L ^ 8 * Real.sqrt n) -
          Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
        punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
          Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ), Real.log (lam (X i)) := by
  obtain ⟨Cscr, ℓ₀, C, hCscr, hℓ₀, hC1, hGS⟩ := exists_goodSquareSpec hR1 hI
  obtain ⟨CD, hCD, hDS⟩ := exists_discSumSpec
  have hC1' := constC1_nonneg
  have hK₁ := chartK₁_nonneg hCA (by linarith : 0 ≤ Cscr) (by linarith : 0 ≤ C) hCD
  have hK₂ := chartK₂_nonneg hCA (by linarith : 0 ≤ Cscr) (by linarith : 0 ≤ C)
  refine ⟨chartK₁ CA Cscr C CD, chartK₂ CA Cscr C + (constC1 + |cStar|),
    max (max 100 ℓ₀) (1 / mMinus + 1), ?_, hK₁, by positivity, ?_⟩
  · exact (by norm_num : (1 : ℝ) ≤ 100).trans ((le_max_left _ _).trans (le_max_left _ _))
  intro L hL n X ρ h hCA'
  have hL100 : 100 ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLℓ : ℓ₀ ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLbig : 1 / mMinus + 1 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  by_cases hlarge : L ^ 4 ≤ Real.sqrt n
  · -- large `n`: the grid argument
    have hR0 : 0 < L ^ 2 := by positivity
    have hL2 : L ≤ L ^ 2 := by nlinarith
    have hR2 : 2 ≤ L ^ 2 := by nlinarith
    have hm0 := mMinus_pos
    have hbig : 1 ≤ mMinus * (L ^ 2 - 3 / 4) := by
      have h1 : 1 / mMinus ≤ L ^ 2 - 3 / 4 := by linarith
      rw [div_le_iff₀ hm0] at h1
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h.pos
    have hu1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
    have hu0 : 0 < Real.sqrt n := by linarith
    have hε0 : 0 < L ^ 4 / Real.sqrt n := by positivity
    have hε1 : L ^ 4 / Real.sqrt n ≤ 1 := by rw [div_le_one hu0]; exact hlarge
    have hG := integrable_gradDensity h.pos X h.inj h.sep h.ne
    obtain ⟨θ, -, hθ⟩ := exists_good_offset (R := L ^ 2) (a₁ := L / 2) (b₁ := 2 * L + 1) (a₂ := 1 / 2)
      (b₂ := 2) hR0 (by linarith) (by norm_num) hG (measurable_gradDensity X ρ) (gradDensity_nonneg X ρ)
    obtain ⟨hb1, hb2⟩ := hθ (cellFin (L ^ 2) θ ρ)
    obtain ⟨t, nb, v, spec⟩ := exists_cellSpec h.pos hR2 hbig θ h.one_le h.le
    obtain ⟨rest, hrest0, hrest, hpre⟩ :=
      large_chart_pre hCscr (by linarith : 0 ≤ C) hGS h spec hL100 hLℓ hε0 hε1
    have herr := large_chart_error hCscr hC1 hCD hCA hDS h hCA' hL100 hlarge spec hb1 hb2 hrest
    have h1 : 0 ≤ (constC1 + |cStar|) * (L ^ 8 * Real.sqrt n) := by positivity
    have e : (chartK₂ CA Cscr C + (constC1 + |cStar|)) * (L ^ 8 * Real.sqrt n) =
        chartK₂ CA Cscr C * (L ^ 8 * Real.sqrt n) + (constC1 + |cStar|) * (L ^ 8 * Real.sqrt n) := by ring
    linarith
  · rw [not_le] at hlarge
    exact chart_lower_small h hL1 hlarge hK₁ hK₂

end Lower

end Sphere

end SandierSerfaty

end
