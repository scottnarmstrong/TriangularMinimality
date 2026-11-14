/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.TwoChartAssemble
public import SandierSerfaty.Sphere.Lower.ChartSetup

/-!
# The sphere lower bound (sphere note, Theorem 6.14)

`Lower.lower_bound`: assuming `TorusBoundStatement`, `Input63Statement` and `RingBoundStatement`,
for every `ε > 0` there is `n₀` such that every minimizer `Y` of `n ≥ n₀` points satisfies
`(C_tri - ε) n ≤ 𝔎(Y)`, i.e. `liminf 𝔎 / n ≥ C_tri`.
-/

open MeasureTheory Set Metric Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

theorem cStar_sub : cStar - Real.pi * Real.log blowupKappa = Real.pi * cTri := by
  have hk := blowupKappa_pos
  have hpi := Real.pi_pos
  unfold cStar cTri
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  field_simp
  push_cast
  ring

theorem charts_arith {cs lk ct K n a b ΦS ΦN nS nN PS PN Lam pi : ℝ}
    (hdec : pi * K + pi * n * lk = ΦS + ΦN)
    (hS : cs * nS - a - b - pi * PS ≤ ΦS) (hN : cs * nN - a - b - pi * PN ≤ ΦN) (hcard : nS + nN = n)
    (hsig : pi * PS + pi * PN ≤ pi * Lam) (hcs : cs - pi * lk = pi * ct) :
    pi * (ct * n) - 2 * (a + b) - pi * Lam ≤ pi * K := by
  have h1 : cs * nS + cs * nN = cs * n := by rw [← mul_add, hcard]
  have h2 : (cs - pi * lk) * n = pi * (ct * n) := by rw [hcs]; ring
  have h3 : (cs - pi * lk) * n = cs * n - pi * n * lk := by ring
  linarith

theorem final_arith {pi ε n ct K E Lam X1 PA : ℝ} (hπ : 0 < pi) (hε : 0 < ε) (hn : 0 ≤ n)
    (hmain : pi * (ct * n) - 2 * E - pi * Lam ≤ pi * K) (e : 2 * E + pi * Lam = X1 + PA)
    (hX1 : X1 ≤ pi * ε / 4 * n) (hPA : PA ≤ pi * (ε / 2 * n)) : pi * ((ct - ε) * n) ≤ pi * K := by
  have h0 : 0 ≤ pi * (ε * n) := by positivity
  have h1 : pi * ((ct - ε) * n) = pi * (ct * n) - pi * (ε * n) := by ring
  have h2 : pi * ε / 4 * n = (1 / 4) * (pi * (ε * n)) := by ring
  have h3 : pi * (ε / 2 * n) = (1 / 2) * (pi * (ε * n)) := by ring
  linarith

/-- The conclusion of `Lower.chart_lower_bound`, as a named `Prop`. -/
@[expose] def ChartLowerSpec (CA K₁ K₂ L₀ : ℝ) : Prop :=
  ∀ {L : ℝ}, L₀ ≤ L → ∀ {n : ℕ} {X : Fin n → ℂ} {ρ : ℝ}, ChartCtx n X ρ → truncDirichlet X ρ ≤ CA * n →
    cStar * ((innerBlown X ρ).card : ℝ) - K₁ * (n / L) - K₂ * (L ^ 8 * Real.sqrt n) -
        Real.pi * ∑ p ∈ innerBlown X ρ, logPlus (1 / (2 * (ρ - ‖p‖))) ≤
      punctureEnergy (ball 0 ρ) (innerBlown X ρ) (blowupPot X) +
        Real.pi * ∑ i ∈ Finset.univ.filter (fun i => ‖blowupScale n • X i‖ < ρ), Real.log (lam (X i))

theorem pointwise_lower {CA K₁ K₂ L₀ CU' : ℝ} (hspec : ChartLowerSpec CA K₁ K₂ L₀)
    (hCAdef : CA = 2 * Real.pi * CU' + 2 * Real.pi * |Real.log blowupKappa| + 2 * constC1 +
      40 * Real.pi / blowupKappa) {L : ℝ} (hL : L₀ ≤ L) {n : ℕ} (hn : 2 ≤ n) {Y : Fin n → R3}
    (hY : IsSphereMinimizer Y) (hKY : normalizedEnergy Y ≤ CU' * n) :
    Real.pi * (cTri * n) - 2 * (K₁ * ((n : ℝ) / L) + K₂ * (L ^ 8 * Real.sqrt n)) -
        Real.pi * (20 * Real.sqrt n / blowupKappa) ≤ Real.pi * normalizedEnergy Y := by
  have hk := blowupKappa_pos
  have hpi := Real.pi_pos
  have hn0 : 0 < n := by omega
  obtain ⟨X, hXi, hX0, hKY', hsepS, hsepN⟩ := exists_chart_setup hn hY
  obtain ⟨r, ⟨hr1, hr2⟩, hrX, hΛ⟩ := exists_cut_radius hn0 X
  have hr0 : 0 < r := by linarith
  have hKb : normalizedEnergy (fun i => stereo (X i)) ≤ CU' * n := by rw [hKY']; exact hKY
  have hAp := apriori_energy hn X hXi hX0 hr1 hr2 hrX hsepS hsepN hKb hΛ
  have hAp' : truncDirichlet X (blowupScale n * r) + truncDirichlet (fun i => invC (X i)) (blowupScale n * r⁻¹) ≤
      CA * n := by rw [hCAdef]; exact hAp
  have hS0 := truncDirichlet_nonneg X (blowupScale n * r)
  have hN0 := truncDirichlet_nonneg (fun i => invC (X i)) (blowupScale n * r⁻¹)
  have ctxS := chartCtx_south hn0 hXi hsepS hr1 hr2 hrX
  have ctxN := chartCtx_north hn0 hXi hsepN hr1 hr2 hrX
  have hS := hspec hL ctxS (by linarith)
  have hN := hspec hL ctxN (by linarith)
  have hdec := charts_energy_split hn0 hXi hX0 hr0 hrX
  have hcard := charts_card hn0 hXi hX0 hr0 hrX
  have hlog := charts_logPlus hn0 hXi hr0
  rw [hKY'] at hdec
  have hΛ' : lambdaSum X r ≤ 20 * Real.sqrt n / blowupKappa := hΛ
  have hcs := cStar_sub
  have hsig : Real.pi * (∑ p ∈ innerBlown X (blowupScale n * r), logPlus (1 / (2 * (blowupScale n * r - ‖p‖)))) +
        Real.pi * (∑ p ∈ innerBlown (fun i => invC (X i)) (blowupScale n * r⁻¹),
          logPlus (1 / (2 * (blowupScale n * r⁻¹ - ‖p‖)))) ≤ Real.pi * (20 * Real.sqrt n / blowupKappa) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hlog.trans hΛ') hpi.le
  have := charts_arith (cs := cStar) (lk := Real.log blowupKappa) (ct := cTri)
    (K := normalizedEnergy Y) (n := n) (a := K₁ * ((n : ℝ) / L)) (b := K₂ * (L ^ 8 * Real.sqrt n))
    hdec hS hN hcard hsig hcs
  linarith

/-- **Theorem 6.14 (the lower bound).** -/
theorem lower_bound (hR1 : Assembly.TorusBoundStatement) (hI : Input63Statement) (hRing : RingBoundStatement) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ Y : Fin n → R3, IsSphereMinimizer Y →
      (cTri - ε) * n ≤ normalizedEnergy Y := by
  obtain ⟨CU, hCU⟩ := hRing
  have hk := blowupKappa_pos
  have hpi := Real.pi_pos
  have hC1' := constC1_nonneg
  set CU' : ℝ := max CU 0 with hCU'def
  have hCU'0 : 0 ≤ CU' := le_max_right _ _
  have hCU' : ∀ n : ℕ, 2 ≤ n → ∀ Y : Fin n → R3, IsSphereMinimizer Y → normalizedEnergy Y ≤ CU' * n :=
    fun n hn Y hY => (hCU n hn Y hY).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  set CA : ℝ := 2 * Real.pi * CU' + 2 * Real.pi * |Real.log blowupKappa| + 2 * constC1 +
    40 * Real.pi / blowupKappa with hCAdef
  have hCA : 0 ≤ CA := by positivity
  obtain ⟨K₁, K₂, L₀, hL₀, hK₁, hK₂, hchart⟩ := chart_lower_bound hR1 hI hCA
  have hCAdef : CA = 2 * Real.pi * CU' + 2 * Real.pi * |Real.log blowupKappa| + 2 * constC1 +
      40 * Real.pi / blowupKappa := rfl
  intro ε hε
  set L : ℝ := max L₀ (8 * K₁ / (Real.pi * ε)) with hLdef
  have hLL : L₀ ≤ L := le_max_left _ _
  have hL1 : 1 ≤ L := hL₀.trans hLL
  have hL0 : 0 < L := by linarith
  have hKL : 2 * K₁ ≤ Real.pi * ε / 4 * L := by
    have h1 : 8 * K₁ / (Real.pi * ε) ≤ L := le_max_right _ _
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  set A : ℝ := 2 * K₂ / Real.pi * L ^ 8 + 20 / blowupKappa with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨⌈(2 * A / ε) ^ 2⌉₊ + 2, fun n hn Y hY => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (2 * A / ε) ^ 2 ≤ n := by
    have := Nat.le_ceil ((2 * A / ε) ^ 2)
    have h2 : ((⌈(2 * A / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈(2 * A / ε) ^ 2⌉₊ ≤ n)
    linarith
  have hu : 2 * A / ε ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hnR
  have hu0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hu2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hmain := pointwise_lower (CA := CA) (K₁ := K₁) (K₂ := K₂) (L₀ := L₀) hchart hCAdef hLL hn2 hY
    (hCU' n hn2 Y hY)
  set E : ℝ := K₁ * ((n : ℝ) / L) + K₂ * (L ^ 8 * Real.sqrt n) with hE
  -- conclude
  have hA : A ≤ ε / 2 * Real.sqrt n := by
    rw [div_le_iff₀ hε] at hu
    linarith
  have hpiA : Real.pi * A * Real.sqrt n ≤ Real.pi * (ε / 2 * n) := by
    have h1 : A * Real.sqrt n ≤ ε / 2 * Real.sqrt n * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hA hu0
    have h2 : A * Real.sqrt n ≤ ε / 2 * n := by
      calc A * Real.sqrt n ≤ ε / 2 * Real.sqrt n * Real.sqrt n := h1
        _ = ε / 2 * (Real.sqrt n * Real.sqrt n) := by ring
        _ = ε / 2 * n := by rw [hu2]
    calc Real.pi * A * Real.sqrt n = Real.pi * (A * Real.sqrt n) := by ring
      _ ≤ Real.pi * (ε / 2 * n) := mul_le_mul_of_nonneg_left h2 hpi.le
  have hK1n : 2 * K₁ * ((n : ℝ) / L) ≤ Real.pi * ε / 4 * n := by
    have h1 : 2 * K₁ * ((n : ℝ) / L) = 2 * K₁ * n / L := by ring
    rw [h1, div_le_iff₀ hL0]
    have := mul_le_mul_of_nonneg_right hKL (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    calc 2 * K₁ * (n : ℝ) ≤ (Real.pi * ε / 4 * L) * n := this
      _ = Real.pi * ε / 4 * n * L := by ring
  have e : 2 * E + Real.pi * (20 * Real.sqrt n / blowupKappa) =
      2 * K₁ * ((n : ℝ) / L) + Real.pi * A * Real.sqrt n := by
    rw [hE, hAdef]
    field_simp
    ring
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h5 : Real.pi * ((cTri - ε) * n) ≤ Real.pi * normalizedEnergy Y :=
    final_arith (Lam := 20 * Real.sqrt n / blowupKappa) (X1 := 2 * K₁ * ((n : ℝ) / L))
      (PA := Real.pi * A * Real.sqrt n) hpi hε hn' hmain e hK1n hpiA
  exact le_of_mul_le_mul_left h5 hpi

end Lower

end Sphere

end SandierSerfaty

end
