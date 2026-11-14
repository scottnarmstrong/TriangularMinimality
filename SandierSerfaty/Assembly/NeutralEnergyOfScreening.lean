/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Assembly.ScreenedBound

/-!
# The neutral-energy bound from the screening theorem and the square-torus bound (screening note, Proposition 6.2 and Theorem 6.3)

`neutralEnergyBound_of_screening_torusBound : ScreeningStatement → TorusBoundStatement → NeutralEnergyBoundStatement` has *exactly* the conclusion of
`div_two_pi_triangularEnergy_le_neutralEnergy` (the jellium form of the bound in Serfaty's Chapter 11). Its
hypotheses are the screening theorem I4 and the square-torus bound (paper Theorem 1.2), each stated as a `Prop`
in `Assembly.Statements`.

## Route (screening note, §6)

1. `eventually_le_cubeEnergy_of_screening_torusBound` (I6): if `W^neu(E) ≠ +∞` and `ε > 0`, then for all large `N`,
   `N (W_△/2π − ε) ≤ F^{□_{√N}}(E)` (a real number). Along `ℓ = √N = s⁴`, with `s = √√√N`, apply
   `screened_bound` (the screening theorem with `ℓc = s²`, `ℓt = s³`, the projection I5 and the square-torus bound); the error terms
   `C_S((A+1) s⁷ + n_∂)` are `o(N)` by `Assembly.tendsto_boundary_count` and `s → ∞`.
2. `neutralEnergyBound_of_screening_torusBound`: the inequality of 1. holds frequently along the real `ℓ → ∞` (every `ℓ*` is exceeded
   by some `√N`), so the `EReal` limsup defining `neutralEnergy` is `≥ W_△/2π − ε` for every `ε`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal Real

public section

namespace SandierSerfaty

namespace Assembly

/-- `s_N = √√√N`, so that `√N = s_N ^ 4` and `N = s_N ^ 8`. -/
noncomputable def sRoot (N : ℕ) : ℝ := √(√(√(N : ℝ)))

theorem sRoot_pow_four (N : ℕ) : sRoot N ^ 4 = √(N : ℝ) := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : (0 : ℝ) ≤ √(N : ℝ) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ √(√(N : ℝ)) := Real.sqrt_nonneg _
  unfold sRoot
  calc (√(√(√(N : ℝ)))) ^ 4 = ((√(√(√(N : ℝ)))) ^ 2) ^ 2 := by ring
    _ = √(N : ℝ) := by rw [Real.sq_sqrt h2, Real.sq_sqrt h1]

theorem tendsto_sRoot : Tendsto sRoot atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))

/-- **I6** (screening note, Proposition `prop:I6`), conditional on the screening theorem and the square-torus bound. -/
theorem eventually_le_cubeEnergy_of_screening_torusBound (hS : ScreeningStatement) (hR1 : TorusBoundStatement)
    {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) (hne : neutralEnergy C E ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ f : ℝ, cubeEnergy C E (√(N : ℝ)) = (f : EReal) ∧
      (N : ℝ) * (triangularEnergy / (2 * π) - ε) ≤ f := by
  obtain ⟨ℓ₀, C_scr, C_S, hℓ₀, hCscr, hCS, hdata⟩ := @hS 1 1 one_pos le_rfl
  obtain ⟨A₀, ℓ₂, hA⟩ := exists_lintegral_quarter_le_of_neutralEnergy_ne_top hE hne
  set A := max A₀ 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hdens := (neutral_density hne).1
  -- the boundary count along `ℓ = √N`
  have hbd := tendsto_boundary_count hE.1 hdens (fun ℓ => 4 * (√(√ℓ)) ^ 3)
    (fun ℓ => by positivity) (by
      have hs : Tendsto (fun ℓ : ℝ => √(√ℓ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
      have h4 : Tendsto (fun ℓ : ℝ => 4 / √(√ℓ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hs
      refine h4.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with ℓ hℓ
      have h0 : 0 < √(√ℓ) := by positivity
      have : (√(√ℓ)) ^ 4 = ℓ := by
        have h1 : (0 : ℝ) ≤ √ℓ := Real.sqrt_nonneg _
        calc (√(√ℓ)) ^ 4 = ((√(√ℓ)) ^ 2) ^ 2 := by ring
          _ = ℓ := by rw [Real.sq_sqrt h1, Real.sq_sqrt hℓ.le]
      field_simp
      linarith [this])
  have hbdN : Tendsto (fun N : ℕ => ((C ∩ (cube (√(N : ℝ)) \
      cube (√(N : ℝ) - 4 * (sRoot N) ^ 3))).ncard : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    have := hbd.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    simp only [Function.comp, sRoot, Real.sq_sqrt h0]
  -- the eventual conditions
  have e1 := eventually_ge_atTop 2
  have e2 := tendsto_sRoot.eventually_ge_atTop 8
  have e3 := tendsto_sRoot.eventually_ge_atTop (|ℓ₀| + 1)
  have e4 := tendsto_sRoot.eventually_ge_atTop (A * C_scr)
  have e5 := tendsto_sRoot.eventually_ge_atTop (C_S * (A + 1) / (π * ε))
  have e6 : ∀ᶠ N : ℕ in atTop, ℓ₂ ≤ √(N : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop ℓ₂
  have e7 : ∀ᶠ N : ℕ in atTop, C_S * ((C ∩ (cube (√(N : ℝ)) \
      cube (√(N : ℝ) - 4 * (sRoot N) ^ 3))).ncard : ℝ) ≤ π * ε * N := by
    have h := hbdN.eventually (gt_mem_nhds (by positivity : 0 < π * ε / C_S))
    filter_upwards [h, eventually_gt_atTop 0] with N hN hN0
    have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [div_lt_iff₀ hN0', div_mul_eq_mul_div, lt_div_iff₀ hCS] at hN
    linarith
  filter_upwards [e1, e2, e3, e4, e5, e6, e7] with N hN h8 h3 h4 h5 h6 h7
  set s := sRoot N with hs
  have hℓ : √(N : ℝ) = s ^ 4 := (sRoot_pow_four N).symm
  have hspos : 0 < s := by linarith
  have hℓpos : 0 < √(N : ℝ) := by rw [hℓ]; positivity
  have hℓ₀s : ℓ₀ ≤ s ^ 2 := by
    have : |ℓ₀| + 1 ≤ s := h3
    nlinarith [le_abs_self ℓ₀, abs_nonneg ℓ₀]
  obtain ⟨hℓ0, hFtop, hI⟩ := hA (√(N : ℝ)) h6
  have hI' : ∫⁻ x in cube (√(N : ℝ)), ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤
      ENNReal.ofReal (A * (√(N : ℝ)) ^ 2) :=
    hI.trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  obtain ⟨f, hf, hbound⟩ := screened_bound hE hR1 hCscr hCS hdata hA0 hN hℓ h8 hℓ₀s h4 hFtop hI'
  refine ⟨f, hf, ?_⟩
  have hN8 : (N : ℝ) = s ^ 8 := by
    have : (√(N : ℝ)) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    rw [← this, hℓ]; ring
  have hNpos : (0 : ℝ) < N := by rw [hN8]; positivity
  have h5' : C_S * (A + 1) * s ^ 7 ≤ π * ε * N := by
    have : C_S * (A + 1) / (π * ε) ≤ s := h5
    rw [div_le_iff₀ (by positivity)] at this
    rw [hN8]
    calc C_S * (A + 1) * s ^ 7 ≤ (s * (π * ε)) * s ^ 7 := by gcongr
      _ = π * ε * s ^ 8 := by ring
  have hmain : (N : ℝ) * triangularEnergy ≤ 2 * π * f + 2 * π * ε * N := by
    have : C_S * ((A + 1) * s ^ 7 +
        ((C ∩ (cube (√(N : ℝ)) \ cube (√(N : ℝ) - 4 * s ^ 3))).ncard : ℝ)) ≤ 2 * π * ε * N := by
      rw [mul_add, ← mul_assoc]
      linarith
    linarith
  have h2π : 0 < 2 * π := by positivity
  have : (N : ℝ) * (triangularEnergy / (2 * π) - ε) = ((N : ℝ) * triangularEnergy -
      2 * π * ε * N) / (2 * π) := by field_simp
  rw [this, div_le_iff₀ h2π]
  linarith

/-- **The neutral-energy bound from the screening theorem and the square-torus bound** (screening note, Theorem 6.3;
exactly the statement of `div_two_pi_triangularEnergy_le_neutralEnergy`). -/
theorem neutralEnergyBound_of_screening_torusBound : ScreeningStatement → TorusBoundStatement → NeutralEnergyBoundStatement := by
  intro hS hR1 C E hE
  by_cases htop : neutralEnergy C E = ⊤
  · rw [htop]; exact le_top
  obtain ⟨hdens, -⟩ := neutral_density htop
  have hL : neutralEnergy C E =
      limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ) atTop := by
    unfold neutralEnergy
    split_ifs
    rfl
  rw [hL]
  set y : ℝ := triangularEnergy / (2 * π) with hy
  -- for every `ε > 0`, `y - ε ≤ limsup`
  have key : ∀ ε : ℝ, 0 < ε →
      (((y - ε : ℝ)) : EReal) ≤ limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) *
        cubeEnergy C E ℓ) atTop := by
    intro ε hε
    have hev := eventually_le_cubeEnergy_of_screening_torusBound hS hR1 hE htop hε
    have hfreq : ∃ᶠ ℓ : ℝ in atTop, (((y - ε : ℝ)) : EReal) ≤
        (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ := by
      refine (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).frequently ?_
      refine (hev.and (eventually_ge_atTop 1)).frequently.mono ?_
      rintro N ⟨⟨f, hf, hfle⟩, hN⟩
      simp only [Function.comp]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hsq : (√(N : ℝ)) ^ 2 = N := Real.sq_sqrt hN0.le
      rw [hf, hsq, ← EReal.coe_mul, EReal.coe_le_coe_iff, inv_mul_eq_div, le_div_iff₀ hN0]
      linarith
    exact le_limsup_of_frequently_le' hfreq
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hr2' : r < y := by exact_mod_cast hr2
  have := key (y - r) (by linarith)
  rw [show y - (y - r) = r by ring] at this
  exact absurd (this.trans_lt hr1) (lt_irrefl _)

end Assembly

end SandierSerfaty

end
