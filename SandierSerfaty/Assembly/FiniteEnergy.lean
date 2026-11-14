/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.CubeEnergyBound
public import SandierSerfaty.Screening.NeutralBridge
public import SandierSerfaty.Screening.SquareCell
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy

/-!
# Finite neutral energy (screening note, Lemma 6.1, `lem:finiteW`)

Let `E ∈ elec C` with `W^neu(E) ≠ +∞`. Then
* `neutral_density`: `#(C ∩ □_ℓ)/ℓ² → 1`, and the `limsup` is finite (definition of `neutralEnergy`);
* `exists_cubeEnergy_le`: `F^{□_ℓ}(E) ≤ M ℓ²` for all large real `ℓ` (and `F^{□_ℓ} ≠ ⊥, ⊤`);
* `exists_lintegral_quarter_le_of_neutralEnergy_ne_top`: `∫_{□_ℓ} |E_{1/4}|² ≤ A ℓ²` for large `ℓ`
  (energy bound `half_lintegral_quarter_le` and `#(C ∩ □_ℓ) ≤ 2ℓ²` eventually);
* `tendsto_boundary_count`: for `d ≥ 0` with `d(ℓ)/ℓ → 0`, `#(C ∩ □_ℓ ∖ □_{ℓ-d(ℓ)})/ℓ² → 0`
  (`n_∂(ℓ) = o(ℓ²)`).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Assembly

/-- Unfolding `neutralEnergy ≠ ⊤`. -/
theorem neutral_density {C : Set ℂ} {E : ℂ → ℂ} (h : neutralEnergy C E ≠ ⊤) :
    Tendsto (fun ℓ : ℝ ↦ ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) ∧
      limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ) atTop ≠ ⊤ := by
  unfold neutralEnergy at h
  split_ifs at h with hd
  · exact ⟨hd, h⟩
  · exact absurd rfl h

/-- `F^{□_ℓ}(E) ≤ M ℓ²` for all large `ℓ`, as a real number. -/
theorem exists_cubeEnergy_le {C : Set ℂ} {E : ℂ → ℂ} (h : neutralEnergy C E ≠ ⊤) :
    ∃ M ℓ₁ : ℝ, ∀ ℓ ≥ ℓ₁, 0 < ℓ ∧ ∃ f : ℝ, cubeEnergy C E ℓ = (f : EReal) ∧ f ≤ M * ℓ ^ 2 := by
  obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1
    (lt_top_iff_ne_top.2 (neutral_density h).2)
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.1 ((eventually_lt_of_limsup_lt hM).and
    (eventually_gt_atTop (0 : ℝ)))
  refine ⟨M, ℓ₁, fun ℓ hℓ => ?_⟩
  obtain ⟨hlt, hpos⟩ := hℓ₁ ℓ hℓ
  have hFtop : cubeEnergy C E ℓ ≠ ⊤ := by
    intro h'
    rw [h', EReal.coe_mul_top_of_pos (by positivity)] at hlt
    exact not_top_lt hlt
  obtain ⟨f, hf⟩ : ∃ f : ℝ, cubeEnergy C E ℓ = f :=
    ⟨_, (EReal.coe_toReal hFtop (Screening.cubeEnergy_ne_bot C E ℓ)).symm⟩
  refine ⟨hpos, f, hf, ?_⟩
  rw [hf, ← EReal.coe_mul, EReal.coe_lt_coe_iff, inv_mul_lt_iff₀ (by positivity)] at hlt
  linarith

/-- A finite neutral energy bounds `∫_{□_ℓ} |E_{1/4}|²` by `A ℓ²` for large `ℓ` (and `F^{□_ℓ} ≠ ⊤`). -/
theorem exists_lintegral_quarter_le_of_neutralEnergy_ne_top {C : Set ℂ} {E : ℂ → ℂ}
    (hE : E ∈ elec C) (h : neutralEnergy C E ≠ ⊤) :
    ∃ A ℓ₂ : ℝ, ∀ ℓ ≥ ℓ₂, 0 < ℓ ∧ cubeEnergy C E ℓ ≠ ⊤ ∧
      ∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤
        ENNReal.ofReal (A * ℓ ^ 2) := by
  obtain ⟨M, ℓ₁, h1⟩ := exists_cubeEnergy_le h
  have hn : ∀ᶠ ℓ : ℝ in atTop, ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2 < 2 :=
    (neutral_density h).1.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨ℓ₃, hℓ₃⟩ := eventually_atTop.1 (hn.and (eventually_gt_atTop (0 : ℝ)))
  have hc0 : 0 ≤ cQuarter 1 := by
    rw [cQuarter_eq]
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨4 * π * M + 4 * cQuarter 1, max ℓ₁ ℓ₃, fun ℓ hℓ => ?_⟩
  obtain ⟨hpos, f, hf, hfM⟩ := h1 ℓ (le_trans (le_max_left _ _) hℓ)
  obtain ⟨hn2, -⟩ := hℓ₃ ℓ (le_trans (le_max_right _ _) hℓ)
  have hFtop : cubeEnergy C E ℓ ≠ ⊤ := by rw [hf]; exact EReal.coe_ne_top _
  refine ⟨hpos, hFtop, ?_⟩
  have hS1 := half_lintegral_quarter_le hE hpos
  set I := ∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)
  set n : ℝ := ((C ∩ cube ℓ).ncard : ℝ)
  have hItop : I ≠ ⊤ := by
    intro h'
    rw [h', hf, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num), ← EReal.coe_mul,
      ← EReal.coe_add] at hS1
    exact EReal.coe_ne_top _ (top_le_iff.1 hS1)
  have hIR : 1 / 2 * I.toReal ≤ 2 * π * f + cQuarter 1 * n := by
    rw [hf, ← EReal.coe_ennreal_toReal hItop, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hS1
    exact hS1
  have hn2' : n ≤ 2 * ℓ ^ 2 := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ℓ ^ 2)).1 hn2
    linarith
  have hI0 : 0 ≤ I.toReal := ENNReal.toReal_nonneg
  have hfin : I.toReal ≤ (4 * π * M + 4 * cQuarter 1) * ℓ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hfM Real.two_pi_pos.le,
      mul_le_mul_of_nonneg_left hn2' hc0]
  exact (ENNReal.le_ofReal_iff_toReal_le hItop (by linarith)).2 hfin

/-- Finiteness of the field integral of the `r̃`-truncation from `F^{□_ℓ} ≠ ⊤`. -/
theorem lintegral_cubeRadius_ne_top {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    (E : ℂ → ℂ) {ℓ : ℝ} (h : cubeEnergy C E ℓ ≠ ⊤) :
    ∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (cubeRadius C ℓ) E x‖ ^ 2) ≠ ⊤ := by
  intro hI
  apply h
  have := two_pi_mul_cubeEnergy hC E ℓ
  unfold locEnergy at this
  rw [hI, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num), EReal.top_add_coe] at this
  have h2 : ((2 * Real.pi : ℝ) : EReal) * cubeEnergy C E ℓ = ⊤ := this
  rcases eq_or_ne (cubeEnergy C E ℓ) ⊤ with h3 | h3
  · exact h3
  · exfalso
    obtain ⟨f, hf⟩ : ∃ f : ℝ, cubeEnergy C E ℓ = f :=
      ⟨_, (EReal.coe_toReal h3 (Screening.cubeEnergy_ne_bot C E ℓ)).symm⟩
    rw [hf, ← EReal.coe_mul] at h2
    exact EReal.coe_ne_top _ h2

/-! ### The boundary count `n_∂ = o(ℓ²)` -/

theorem cube_mono {a b : ℝ} (h : a ≤ b) : cube a ⊆ cube b := by
  intro z hz
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩

theorem ncard_boundary_add {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {a b : ℝ}
    (h : a ≤ b) :
    (((C ∩ (cube b \ cube a)).ncard : ℕ) : ℝ) + ((C ∩ cube a).ncard : ℝ) =
      ((C ∩ cube b).ncard : ℝ) := by
  have hsub : C ∩ cube a ⊆ C ∩ cube b := inter_subset_inter_right _ (cube_mono h)
  have hfin := Screening.finite_inter_cube hC b
  have heq : C ∩ (cube b \ cube a) = (C ∩ cube b) \ (C ∩ cube a) := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_sdiff]; tauto
  rw [heq]
  exact_mod_cast Set.ncard_sdiff_add_ncard_of_subset hsub hfin

/-- `n_∂(ℓ) = #(C ∩ □_ℓ ∖ □_{ℓ - d(ℓ)}) = o(ℓ²)` when `d ≥ 0`, `d(ℓ)/ℓ → 0` and the density tends to `1`. -/
theorem tendsto_boundary_count {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    (hd : Tendsto (fun ℓ : ℝ ↦ ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1))
    (d : ℝ → ℝ) (hd0 : ∀ ℓ, 0 ≤ d ℓ) (hdℓ : Tendsto (fun ℓ => d ℓ / ℓ) atTop (𝓝 0)) :
    Tendsto (fun ℓ : ℝ ↦ ((C ∩ (cube ℓ \ cube (ℓ - d ℓ))).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 0) := by
  set n : ℝ → ℝ := fun ℓ => ((C ∩ cube ℓ).ncard : ℝ) with hn
  -- `ℓ' = ℓ - d ℓ` tends to infinity and `ℓ'/ℓ → 1`
  have hr : Tendsto (fun ℓ : ℝ => 1 - d ℓ / ℓ) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdℓ
  have hev : ∀ᶠ ℓ : ℝ in atTop, 0 < ℓ ∧ 1 / 2 < 1 - d ℓ / ℓ :=
    (eventually_gt_atTop 0).and (hr.eventually (lt_mem_nhds (by norm_num)))
  have hℓ'eq : ∀ ℓ : ℝ, 0 < ℓ → ℓ - d ℓ = ℓ * (1 - d ℓ / ℓ) := by
    intro ℓ hℓ; field_simp
  have hℓ' : Tendsto (fun ℓ : ℝ => ℓ - d ℓ) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_id.atTop_mul_const' (r := 1 / 2) (by norm_num))
    filter_upwards [hev] with ℓ ⟨hℓ, hℓ2⟩
    rw [hℓ'eq ℓ hℓ]
    simp only [id]
    nlinarith
  have hq : Tendsto (fun ℓ : ℝ => n (ℓ - d ℓ) / (ℓ - d ℓ) ^ 2) atTop (𝓝 1) := hd.comp hℓ'
  have hprod : Tendsto (fun ℓ : ℝ => n (ℓ - d ℓ) / (ℓ - d ℓ) ^ 2 * (1 - d ℓ / ℓ) ^ 2) atTop
      (𝓝 1) := by simpa using hq.mul (hr.pow 2)
  have hdiff : Tendsto (fun ℓ : ℝ => n ℓ / ℓ ^ 2 - n (ℓ - d ℓ) / (ℓ - d ℓ) ^ 2 *
      (1 - d ℓ / ℓ) ^ 2) atTop (𝓝 0) := by simpa using hd.sub hprod
  refine hdiff.congr' ?_
  filter_upwards [hev] with ℓ ⟨hℓ, hℓ2⟩
  have hle : ℓ - d ℓ ≤ ℓ := by linarith [hd0 ℓ]
  have hadd := ncard_boundary_add hC hle
  have hne : ℓ - d ℓ ≠ 0 := by rw [hℓ'eq ℓ hℓ]; positivity
  have hne' : (ℓ - d ℓ) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have h1 : n (ℓ - d ℓ) / (ℓ - d ℓ) ^ 2 * (1 - d ℓ / ℓ) ^ 2 = n (ℓ - d ℓ) / ℓ ^ 2 := by
    have : (1 - d ℓ / ℓ) = (ℓ - d ℓ) / ℓ := by field_simp
    rw [this, div_pow]
    field_simp
  rw [h1, ← sub_div]
  congr 1
  simp only [hn] at hadd ⊢
  linarith

end Assembly

end SandierSerfaty

end
