/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.MainComparison
public import SandierSerfaty.Screening.Density
public import SandierSerfaty.Statements.Whole.Defs.WholeEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy

/-!
# The comparison inequality CMP (comparison note, Theorem `thm:CMP`)

**Theorem** (`twoPi_mul_neutralEnergy_neg_le_wholeEnergy`). For every cutoff family `χ` and every
`E ∈ 𝒜₁` (`IsAdmissibleField Λ E`), in `[-∞, +∞]`:
```
2π W^neu(-E, 1) ≤ W(E).
```

## Proof

Let `M₁ > W(E)` be real (`neutralEnergy_neg_le_of_wholeEnergy_lt`). Eventually in `R`,
`W(E, χ_R) < M₁ |K_R|`.

* *Energy bound and density* (comparison note Corollaries `cor:EB`, `cor:finite-density`). With `R = ℓ/2 + 4`, MC
  and the quarter-truncation bound `half_lintegral_quarter_le` give
  `½ ∫_{□_ℓ} |(-E)_{1/4}|² ≤ W(E, χ_R) + 2 C(L) #(Λ ∩ K_R) ≤ K ℓ²` (the growth bound of `𝒜₁`), so
  `#(Λ ∩ □_ℓ)/ℓ² → 1` (`tendsto_ncard_cube_div_sq`) and `W^neu(-E, 1) = limsup ℓ⁻² F^{□_ℓ}`.
* *Limit.* MC gives `ℓ⁻² F^{□_ℓ} ≤ (2π)⁻¹ (M₁ + |M₁| ((ℓ+8)²/ℓ² - 1) + C(L) #(Λ ∩ □_{ℓ+8} ∖ □_ℓ)/ℓ²)`,
  and the right side tends to `M₁/(2π)` by density.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Whole

open Screening

theorem IsCutoffFamily.tsupport_subset_cube {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {R : ℝ}
    (hR : 1 < R) : tsupport (χ R) ⊆ cube (2 * R) := by
  rw [cube_two_mul]; exact (hχ.1 R hR).2.2.2.1

theorem IsCutoffFamily.eq_one {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {R : ℝ} (hR : 1 < R) :
    ∀ x ∈ cube (2 * (R - 1)), χ R x = 1 := by
  rw [cube_two_mul]; exact (hχ.1 R hR).2.2.2.2

theorem localEnergy_eq_coe_toReal {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E) {ξ : ℂ → ℝ}
    (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    localEnergy Λ E ξ = ((localEnergy Λ E ξ).toReal : EReal) := by
  obtain ⟨w, hw⟩ := exists_tendsto_punctureFunctional hE hξ hc
  unfold localEnergy
  rw [hw.limsup_eq, EReal.toReal_coe]

theorem le_coe_div_of_coe_mul_le {F : EReal} {c r : ℝ} (hc : 0 < c) (h : (c : EReal) * F ≤ r) :
    F ≤ ((r / c : ℝ) : EReal) := by
  induction F using EReal.rec with
  | bot => exact bot_le
  | top =>
    rw [EReal.coe_mul_top_of_pos hc] at h
    exact absurd h (not_le.2 (EReal.coe_lt_top r))
  | coe y =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff, le_div_iff₀ hc]
    linarith

theorem coe_mul_le_coe_mul {x : EReal} {c r : ℝ} (hc : 0 ≤ c) (h : x ≤ r) :
    (c : EReal) * x ≤ ((c * r : ℝ) : EReal) := by
  rcases hc.eq_or_lt with h0 | h0
  · rw [← h0]; simp
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos h0]; exact bot_le
  | top => exact absurd h (not_le.2 (EReal.coe_lt_top r))
  | coe y =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.1 h) hc

theorem le_ofReal_of_half_le {X : ℝ≥0∞} {r : ℝ} (h : ((1 / 2 : ℝ) : EReal) * (X : EReal) ≤ r) :
    X ≤ ENNReal.ofReal (2 * r) := by
  by_cases hX : X = ⊤
  · rw [hX, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num)] at h
    exact absurd h (not_le.2 (EReal.coe_lt_top r))
  · rw [← EReal.coe_ennreal_toReal hX, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h
    rw [← ENNReal.ofReal_toReal hX]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem cube_subset_ball_three (R : ℝ) (hR : 0 < R) : cube (2 * R) ⊆ ball 0 (3 * R) := by
  intro x hx
  rw [mem_cube_iff_cubeNorm, cubeNorm] at hx
  rw [mem_ball_zero_iff]
  calc ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
    _ ≤ 2 * R := by linarith [le_max_left |x.re| |x.im|, le_max_right |x.re| |x.im|]
    _ < 3 * R := by linarith

theorem cube_mono {a b : ℝ} (h : a ≤ b) : cube a ⊆ cube b := fun x hx => by
  rw [mem_cube_iff_cubeNorm] at hx ⊢; linarith

/-- The CMP bound for a real `M₁ > W(E)`: `W^neu(-E, 1) ≤ M₁ / (2π)`. -/
theorem neutralEnergy_neg_le_of_wholeEnergy_lt {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {Λ : Set ℂ}
    {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E) {M₁ : ℝ} (hM : wholeEnergy χ Λ E < M₁) :
    neutralEnergy Λ (fun x => -E x) ≤ ((M₁ / (2 * Real.pi) : ℝ) : EReal) := by
  set Et : ℂ → ℂ := fun x => -E x with hEtdef
  have hEt : Et ∈ elec Λ := neg_mem_elec hE
  have hC := hE.1
  obtain ⟨L₀, hL₀⟩ := hχ.2
  set L : ℝ := max L₀ 1 with hLdef
  have hL : 1 ≤ L := le_max_right _ _
  have hLg : ∀ R : ℝ, 1 < R → ∀ x, ‖gradient (χ R) x‖ ≤ L := fun R hR x =>
    (hL₀ R hR x).trans (le_max_left _ _)
  obtain ⟨Θ₀, hΘ₀⟩ := hE.2.2.2.2
  set Θ : ℝ := max Θ₀ 0 with hΘdef
  have hΘ0 : 0 ≤ Θ := le_max_right _ _
  set C : ℝ := mcConst L with hCdef
  have hc0C : cQuarter 1 ≤ C := cQuarter_le_mcConst hL
  have hC0 : 0 ≤ C := cQuarter_one_pos.le.trans hc0C
  set W : ℝ → ℝ := fun R => (localEnergy Λ E (χ R)).toReal with hWdef
  have hW : ∀ R : ℝ, 1 < R → localEnergy Λ E (χ R) = (W R : EReal) := fun R hR =>
    localEnergy_eq_coe_toReal hE (hχ.1 R hR).1 (hχ.1 R hR).2.1
  -- eventually `W(E, χ_R) < M₁ |K_R|`
  have hev : ∀ᶠ R : ℝ in atTop, W R < M₁ * (2 * R) ^ 2 := by
    have h1 := Filter.eventually_lt_of_limsup_lt hM
    filter_upwards [h1, eventually_gt_atTop 1] with R hR hR1
    rw [hW R hR1, ← EReal.coe_mul, EReal.coe_lt_coe_iff,
      inv_mul_lt_iff₀ (by positivity)] at hR
    linarith
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hev
  -- MC
  have hMC : ∀ ℓ : ℝ, ∀ R : ℝ, 1 < R → ℓ / 2 + 4 ≤ R →
      ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ ≤
        ((W R + C * (Λ ∩ (cube (2 * R) \ cube ℓ)).ncard : ℝ) : EReal) := by
    intro ℓ R hR1 hR
    have := twoPi_mul_cubeEnergy_le_localEnergy hE (hχ.1 R hR1).1 (hχ.1 R hR1).2.1
      (fun x => ((hχ.1 R hR1).2.2.1 x).1) (fun x => ((hχ.1 R hR1).2.2.1 x).2)
      (IsCutoffFamily.tsupport_subset_cube hχ hR1) (IsCutoffFamily.eq_one hχ hR1) hL (hLg R hR1) hR
    rwa [hW R hR1, ← EReal.coe_add] at this
  -- the count in `K_R`
  have hcount : ∀ R : ℝ, 1 < R → ((Λ ∩ cube (2 * R)).ncard : ℝ) ≤ 9 * Θ * Real.pi * R ^ 2 := by
    intro R hR
    have hfin : (Λ ∩ ball 0 (3 * R)).Finite :=
      (hC (3 * R)).subset (inter_subset_inter_right _ ball_subset_closedBall)
    have h1 : (Λ ∩ cube (2 * R)).ncard ≤ (Λ ∩ ball 0 (3 * R)).ncard :=
      ncard_le_ncard (inter_subset_inter_right _ (cube_subset_ball_three R (by linarith))) hfin
    have h2 := hΘ₀ (3 * R) (by linarith)
    have h3 : Θ₀ * (Real.pi * (3 * R) ^ 2) ≤ Θ * (Real.pi * (3 * R) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    calc ((Λ ∩ cube (2 * R)).ncard : ℝ) ≤ (Λ ∩ ball 0 (3 * R)).ncard := by exact_mod_cast h1
      _ ≤ 9 * Θ * Real.pi * R ^ 2 := by linarith
  -- the energy bound and density
  set ℓ₀ : ℝ := max 8 (2 * max R₀ 2) with hℓ₀
  set K : ℝ := 2 * (4 * |M₁| + 18 * C * Θ * Real.pi) with hK
  have hEB : ∀ ℓ ≥ ℓ₀, ∫⁻ x in cube ℓ, ENNReal.ofReal
      (‖truncField Λ (fun _ ↦ 1 / 4) Et x‖ ^ 2) ≤ ENNReal.ofReal (K * ℓ ^ 2) := by
    intro ℓ hℓ
    have hℓ8 : 8 ≤ ℓ := (le_max_left _ _).trans hℓ
    have hℓR : 2 * max R₀ 2 ≤ ℓ := (le_max_right _ _).trans hℓ
    set R : ℝ := ℓ / 2 + 4 with hRdef
    have hR1 : 1 < R := by linarith
    have hRR₀ : R₀ ≤ R := by linarith [le_max_left R₀ 2]
    have hRℓ : R ≤ ℓ := by linarith
    have hq := half_lintegral_quarter_le hEt (by linarith : (0 : ℝ) < ℓ)
    have hmc := hMC ℓ R hR1 le_rfl
    have hfinK := finite_inter_cube hC (2 * R)
    have hn1 : ((Λ ∩ (cube (2 * R) \ cube ℓ)).ncard : ℝ) ≤ (Λ ∩ cube (2 * R)).ncard := by
      exact_mod_cast ncard_le_ncard (inter_subset_inter_right _ sdiff_subset) hfinK
    have hn2 : ((Λ ∩ cube ℓ).ncard : ℝ) ≤ (Λ ∩ cube (2 * R)).ncard := by
      exact_mod_cast ncard_le_ncard (inter_subset_inter_right _ (cube_mono (by linarith))) hfinK
    have hn := hcount R hR1
    have hWR := hR₀ R hRR₀
    have hsum : ((1 / 2 : ℝ) : EReal) * ((∫⁻ x in cube ℓ, ENNReal.ofReal
        (‖truncField Λ (fun _ ↦ 1 / 4) Et x‖ ^ 2) : ℝ≥0∞) : EReal) ≤
        ((W R + C * (Λ ∩ (cube (2 * R) \ cube ℓ)).ncard + cQuarter 1 * (Λ ∩ cube ℓ).ncard : ℝ) :
          EReal) := by
      refine hq.trans ?_
      rw [EReal.coe_add]
      exact add_le_add_left hmc _
    refine (le_ofReal_of_half_le hsum).trans (ENNReal.ofReal_le_ofReal ?_)
    have hM1 : M₁ * (2 * R) ^ 2 ≤ |M₁| * (2 * ℓ) ^ 2 := by
      have h1 : (2 * R) ^ 2 ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      linarith [mul_le_mul_of_nonneg_right (le_abs_self M₁) (sq_nonneg (2 * R)),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg M₁)]
    have hRsq : R ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by linarith) hRℓ 2
    have hcn : C * ((Λ ∩ (cube (2 * R) \ cube ℓ)).ncard : ℝ) +
        cQuarter 1 * (Λ ∩ cube ℓ).ncard ≤ 2 * C * (9 * Θ * Real.pi * ℓ ^ 2) := by
      have hb : ((Λ ∩ cube (2 * R)).ncard : ℝ) ≤ 9 * Θ * Real.pi * ℓ ^ 2 :=
        hn.trans (mul_le_mul_of_nonneg_left hRsq (by positivity))
      have h1 : C * ((Λ ∩ (cube (2 * R) \ cube ℓ)).ncard : ℝ) ≤ C * (9 * Θ * Real.pi * ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left (hn1.trans hb) hC0
      have h2 : cQuarter 1 * ((Λ ∩ cube ℓ).ncard : ℝ) ≤ C * (9 * Θ * Real.pi * ℓ ^ 2) :=
        mul_le_mul hc0C (hn2.trans hb) (Nat.cast_nonneg _) hC0
      linarith
    rw [hK]
    linarith [mul_nonneg (abs_nonneg M₁) (sq_nonneg ℓ),
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hΘ0) Real.pi_pos.le) (sq_nonneg ℓ)]
  have hdens := tendsto_ncard_cube_div_sq hEt ⟨K, ℓ₀, hEB⟩
  -- the neutral energy is the `limsup`
  have hNE : neutralEnergy Λ Et =
      limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy Λ Et ℓ) atTop := by
    unfold neutralEnergy
    simp only [hdens, ↓reduceIte]
  -- the comparison functions
  set n : ℝ → ℝ := fun ℓ => ((Λ ∩ cube ℓ).ncard : ℝ) with hn
  set q : ℝ → ℝ := fun ℓ => (ℓ + 8) ^ 2 / ℓ ^ 2 with hq
  set h : ℝ → ℝ := fun ℓ => (2 * Real.pi)⁻¹ *
    (M₁ + |M₁| * (q ℓ - 1) + C * ((n (ℓ + 8) - n ℓ) / ℓ ^ 2)) with hhdef
  have hq1 : Tendsto q atTop (𝓝 1) := by
    have h1 : Tendsto (fun ℓ : ℝ => (1 + 8 * ℓ⁻¹) ^ 2) atTop (𝓝 ((1 + 8 * 0) ^ 2)) :=
      ((tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 8)).pow 2)
    rw [show ((1 : ℝ) + 8 * 0) ^ 2 = 1 by norm_num] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    simp only [hq]
    field_simp
  have hn8 : Tendsto (fun ℓ => n (ℓ + 8) / ℓ ^ 2) atTop (𝓝 1) := by
    have h1 : Tendsto (fun ℓ : ℝ => n (ℓ + 8) / (ℓ + 8) ^ 2) atTop (𝓝 1) :=
      hdens.comp (tendsto_atTop_add_const_right _ 8 tendsto_id)
    have h2 := h1.mul hq1
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    simp only [hq]
    have : (ℓ + 8) ^ 2 ≠ 0 := by positivity
    field_simp
  have hh : Tendsto h atTop (𝓝 (M₁ / (2 * Real.pi))) := by
    have h1 : Tendsto (fun ℓ => (n (ℓ + 8) - n ℓ) / ℓ ^ 2) atTop (𝓝 (1 - 1)) := by
      refine (hn8.sub hdens).congr' (Eventually.of_forall fun ℓ => ?_)
      simp only [hn]; ring
    have h2 := (((tendsto_const_nhds (x := M₁)).add ((hq1.sub_const 1).const_mul |M₁|)).add
      (h1.const_mul C)).const_mul (2 * Real.pi)⁻¹
    simp only [sub_self, mul_zero, add_zero] at h2
    rw [show M₁ / (2 * Real.pi) = (2 * Real.pi)⁻¹ * M₁ by ring]
    exact h2
  have hbd : ∀ᶠ ℓ : ℝ in atTop,
      (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy Λ Et ℓ ≤ ((h ℓ : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop ℓ₀] with ℓ hℓ
    have hℓ8 : 8 ≤ ℓ := (le_max_left _ _).trans hℓ
    have hℓR : 2 * max R₀ 2 ≤ ℓ := (le_max_right _ _).trans hℓ
    have hℓ0 : 0 < ℓ := by linarith
    set R : ℝ := ℓ / 2 + 4 with hRdef
    have hR1 : 1 < R := by linarith
    have h2R : 2 * R = ℓ + 8 := by rw [hRdef]; ring
    have hWR := hR₀ R (by linarith [le_max_left R₀ 2])
    rw [h2R] at hWR
    have hmc := hMC ℓ R hR1 le_rfl
    rw [h2R] at hmc
    have hF := le_coe_div_of_coe_mul_le (by positivity) hmc
    refine (coe_mul_le_coe_mul (by positivity) hF).trans (EReal.coe_le_coe_iff.2 ?_)
    -- the real inequality
    have hsd : ((Λ ∩ (cube (ℓ + 8) \ cube ℓ)).ncard : ℝ) = n (ℓ + 8) - n ℓ := by
      have hsub : Λ ∩ cube ℓ ⊆ Λ ∩ cube (ℓ + 8) :=
        inter_subset_inter_right _ (cube_mono (by linarith))
      have hset : Λ ∩ (cube (ℓ + 8) \ cube ℓ) = (Λ ∩ cube (ℓ + 8)) \ (Λ ∩ cube ℓ) := by
        ext x; simp only [mem_inter_iff, Set.mem_sdiff]; tauto
      have := ncard_sdiff_add_ncard_of_subset hsub (finite_inter_cube hC (ℓ + 8))
      rw [hset, hn]
      simp only
      rw [← this]
      push_cast
      ring
    rw [hsd]
    have hℓsq : 0 < ℓ ^ 2 := by positivity
    have hq_ge : 1 ≤ q ℓ := by
      simp only [hq]; rw [le_div_iff₀ hℓsq]; nlinarith
    have hWq : (ℓ ^ 2)⁻¹ * W R ≤ M₁ + |M₁| * (q ℓ - 1) := by
      have h1 : (ℓ ^ 2)⁻¹ * W R ≤ (ℓ ^ 2)⁻¹ * (M₁ * (ℓ + 8) ^ 2) :=
        mul_le_mul_of_nonneg_left hWR.le (by positivity)
      have h2 : (ℓ ^ 2)⁻¹ * (M₁ * (ℓ + 8) ^ 2) = M₁ * q ℓ := by simp only [hq]; field_simp
      have h3 : M₁ * (q ℓ - 1) ≤ |M₁| * (q ℓ - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self M₁) (by linarith)
      linarith
    simp only [hhdef]
    have h2pi : 0 < 2 * Real.pi := by positivity
    rw [show (ℓ ^ 2)⁻¹ * ((W R + C * (n (ℓ + 8) - n ℓ)) / (2 * Real.pi)) =
      (2 * Real.pi)⁻¹ * ((ℓ ^ 2)⁻¹ * W R + C * ((n (ℓ + 8) - n ℓ) / ℓ ^ 2)) by field_simp]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  rw [hNE]
  calc limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy Λ Et ℓ) atTop
      ≤ limsup (fun ℓ : ℝ => ((h ℓ : ℝ) : EReal)) atTop := limsup_le_limsup hbd
    _ = ((M₁ / (2 * Real.pi) : ℝ) : EReal) :=
        ((continuous_coe_real_ereal.tendsto _).comp hh).limsup_eq

/-- **The comparison inequality CMP** (comparison note, Theorem `thm:CMP`): `2π W^neu(-E, 1) ≤ W(E)` in
`[-∞, +∞]`, for every cutoff family and every `E ∈ 𝒜₁`. -/
theorem twoPi_mul_neutralEnergy_neg_le_wholeEnergy {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ)
    {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E) :
    ((2 * Real.pi : ℝ) : EReal) * neutralEnergy Λ (fun x => -E x) ≤ wholeEnergy χ Λ E := by
  refine EReal.le_of_forall_lt_iff_le.1 fun M₁ hM => ?_
  have h := coe_mul_le_coe_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    (neutralEnergy_neg_le_of_wholeEnergy_lt hχ hE hM)
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

end Whole

end SandierSerfaty

end
