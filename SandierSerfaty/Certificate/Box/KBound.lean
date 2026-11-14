/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.KRowDef
public import SandierSerfaty.Certificate.Box.Outer
public import SandierSerfaty.Certificate.Box.Hessian

/-!
# An upper bound for `K = 2 g_p(x₀)` from the `K` row (`comp:K-quadrature`)

`sumLoop_sound`: a passing sum row has the exact integer accumulator `acc + ∑ (σ_{j+1} - σ_j) v_j ≤ thr`.

`K_le_of_row`: if the row at the dyadic `dK = dm/2^128` over the partition `sg sm` of `[0, X]`, `x₀ ≤ X`, passes, then
`K ≤ 2 (thr/2^256 + δ X + L₄ S_h² X/24 + E)`, `E = L₂ρ'²/2 + L₁ρρ' + L₃ρ²·xHi/2`, where `|dK - p| ≤ ρ`,
`X - x₀ ≤ ρ'`. The proof: the exact value of the row is within `δ X` of the midpoint sum and `L₄ S_h² X/24` of `g_{dK}(X)`
(the budget of one value, `deltaMax`); `g_p(x₀) ≤ g_{dK}(X) + E` by `g_step` at the stationary point `(p, x₀)`.
`abs_sub_p_le`, `x₀_le_of`, `sub_x₀_le` turn literal fourth-power inequalities into the closeness hypotheses (the exact
`p⁴ = 1/12`, `x₀⁴ = 1/108`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query SandierSerfaty.Calibration SandierSerfaty.Tails

/-- **Soundness of the sum row.** -/
theorem sumLoop_sound (E : EvalData) (idx : ℕ → ℕ) (dm : ℕ) (sm : ℕ → ℕ) (thr : SInt) :
    ∀ n k acc, sumLoop E idx dm sm thr n k acc = true →
    ∃ v : ℕ → Fx 128, (∀ j < n, midVal E idx dm sm (k + j) = some (v j) ∧ sm (k + j) ≤ sm (k + j + 1)) ∧
      acc.toInt + ∑ j ∈ Finset.range n, ((sm (k + j + 1) : ℤ) - sm (k + j)) * (v j).v.toInt ≤ thr.toInt := by
  intro n
  induction n with
  | zero =>
    intro k acc h
    refine ⟨fun _ => default, fun j hj => absurd hj (by omega), ?_⟩
    simp only [sumLoop] at h
    simpa using (SInt.ble_iff _ _).1 h
  | succ n ih =>
    intro k acc h
    simp only [sumLoop, Bool.and_eq_true] at h
    obtain ⟨hm, hrest⟩ := h
    have hm' : sm k ≤ sm (k + 1) := Nat.le_of_ble_eq_true hm
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at hrest
    | some w =>
      simp only [hv] at hrest
      obtain ⟨v', hv', hsum⟩ := ih (k + 1) _ hrest
      refine ⟨fun j => match j with | 0 => w | j' + 1 => v' j', ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact ⟨by simpa using hv, by simpa using hm'⟩
        | succ j' =>
          have := hv' j' (by omega)
          have e : k + (j' + 1) = k + 1 + j' := by omega
          simp only [e]
          exact this
      · rw [toInt_step, widthM_cast hm'] at hsum
        rw [Finset.sum_range_succ']
        have : ∑ j ∈ Finset.range n, ((sm (k + 1 + j + 1) : ℤ) - sm (k + 1 + j)) * (v' j).v.toInt =
            ∑ j ∈ Finset.range n, ((sm (k + (j + 1) + 1) : ℤ) - sm (k + (j + 1))) * (v' j).v.toInt := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show k + (j + 1) = k + 1 + j by omega]
        rw [this] at hsum
        simp only [Nat.add_zero]
        linarith

theorem abs_sub_p_le {dK ρ : ℝ} (hρ : 0 ≤ ρ) (h0 : 0 ≤ dK - ρ) (h1 : (dK - ρ) ^ 4 ≤ 1 / 12)
    (h2 : (1 : ℝ) / 12 ≤ (dK + ρ) ^ 4) : |dK - p| ≤ ρ := by
  have hp := p_pow_four
  have hp0 := p_pos.le
  rw [abs_le]
  constructor
  · by_contra h
    push Not at h
    have : dK + ρ < p := by linarith
    have := pow_lt_pow_left₀ this (by linarith) (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  · by_contra h
    push Not at h
    have : p < dK - ρ := by linarith
    have := pow_lt_pow_left₀ this hp0 (by norm_num : (4 : ℕ) ≠ 0)
    linarith

theorem x₀_pow_four : x₀ ^ 4 = 1 / 108 := by
  have : x₀ = R₀ / 2 := rfl
  rw [this, div_pow, R₀_pow_four]
  norm_num

theorem x₀_le_of {X : ℝ} (hX : 0 ≤ X) (h : (1 : ℝ) / 108 ≤ X ^ 4) : x₀ ≤ X := by
  by_contra hc
  push Not at hc
  have := pow_lt_pow_left₀ hc hX (by norm_num : (4 : ℕ) ≠ 0)
  linarith [x₀_pow_four]

theorem sub_x₀_le {X ρ : ℝ} (_h0 : 0 ≤ X - ρ) (h : (X - ρ) ^ 4 ≤ 1 / 108) : X - ρ ≤ x₀ := by
  by_contra hc
  push Not at hc
  have := pow_lt_pow_left₀ hc x₀_pos.le (by norm_num : (4 : ℕ) ≠ 0)
  linarith [x₀_pow_four]

/-- **The upper bound of `K` from the `K` row.** -/
theorem K_le_of_row (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) {L1 L2 L3 L4 Sh δ ρ ρ' : ℝ} (Gr : KGrid)
    (hB : DerivBounds Calibration.b (697 / 1000) (65 / 100) L1 L2 L3 L4)
    (hrow : Gr.row E = true) (hdK : (Gr.dm : ℝ) / 2 ^ 128 ∈ Icc Calibration.b (697 / 1000 : ℝ))
    (hs0 : Gr.sm 0 = 0) (hstop : sg Gr.sm Gr.nx ≤ 65 / 100)
    (hstep : ∀ k < Gr.nx, sg Gr.sm (k + 1) - sg Gr.sm k ≤ Sh) (hδ : deltaMax rf re rlam rmu rκ rc ≤ δ)
    (hρ : |(Gr.dm : ℝ) / 2 ^ 128 - p| ≤ ρ) (hx0 : x₀ ≤ sg Gr.sm Gr.nx) (hρ' : sg Gr.sm Gr.nx - x₀ ≤ ρ') :
    K ≤ 2 * ((Gr.thr.toInt : ℝ) / 2 ^ 256 + δ * sg Gr.sm Gr.nx + L4 * Sh ^ 2 * sg Gr.sm Gr.nx / 24 +
      (L2 * ρ' ^ 2 / 2 + L1 * ρ * ρ' + 65 / 100 * L3 * ρ ^ 2 / 2)) := by
  have hbpos : (0 : ℝ) < Calibration.b := Calibration.b_pos
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hB.nonneg
  obtain ⟨v, hv, hsum⟩ := sumLoop_sound E Gr.idx Gr.dm Gr.sm Gr.thr Gr.nx 0 SInt.zero hrow
  have hmono : ∀ j < Gr.nx, Gr.sm j ≤ Gr.sm (j + 1) := fun j hj => by simpa using (hv j hj).2
  have hP : Partition (sg Gr.sm) Gr.nx (65 / 100) Sh :=
    ⟨fun j hj => by
      unfold sg
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmono j hj) (by positivity),
     by simp [sg, hs0], hstop, hstep⟩
  have hd1 : (Gr.dm : ℝ) / 2 ^ 128 ≤ 1 := hdK.2.trans (by norm_num)
  have hvR : ∀ j < Gr.nx, |(v j).val - G ((Gr.dm : ℝ) / 2 ^ 128)
      ((sg Gr.sm j + sg Gr.sm (j + 1)) / 2)| ≤ δ := by
    intro j hj
    have := (midVal_sound hc H hdK.1 hd1 (by simpa using (hv j hj).1)).2
    exact this.trans hδ
  have h1 := abs_sum_sub_midSum (F := G ((Gr.dm : ℝ) / 2 ^ 128)) hP (v := fun j => (v j).val) hvR
  have h2 := hB.g_sub_midSum hdK hP
  have hZ : (((∑ j ∈ Finset.range Gr.nx, ((Gr.sm (j + 1) : ℤ) - Gr.sm j) * (v j).v.toInt : ℤ)) : ℝ) =
      2 ^ 256 * ∑ j ∈ Finset.range Gr.nx, (sg Gr.sm (j + 1) - sg Gr.sm j) * (v j).val := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [sg, Fx.val_def]
    field_simp
  simp only [zero_add, SInt.toInt_zero] at hsum
  have hsumR : 2 ^ 256 * ∑ j ∈ Finset.range Gr.nx, (sg Gr.sm (j + 1) - sg Gr.sm j) * (v j).val ≤
      (Gr.thr.toInt : ℝ) := by
    rw [← hZ]; exact_mod_cast hsum
  have hQ : ∑ j ∈ Finset.range Gr.nx, (sg Gr.sm (j + 1) - sg Gr.sm j) * (v j).val ≤
      (Gr.thr.toInt : ℝ) / 2 ^ 256 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have a1 := (abs_le.1 (h1 Gr.nx le_rfl)).1
  have a2 := (abs_le.1 (h2 Gr.nx le_rfl)).2
  have hgK : g ((Gr.dm : ℝ) / 2 ^ 128) (sg Gr.sm Gr.nx) ≤
      (Gr.thr.toInt : ℝ) / 2 ^ 256 + δ * sg Gr.sm Gr.nx + L4 * Sh ^ 2 * sg Gr.sm Gr.nx / 24 := by linarith
  -- from `g_p(x₀)` to `g_{dK}(X)` at the stationary point
  have hpI : p ∈ Icc Calibration.b (697 / 1000 : ℝ) :=
    ⟨by have := p_gt; unfold Calibration.b; linarith, by have := p_lt; linarith⟩
  have hx0I : x₀ ∈ Icc (0 : ℝ) (65 / 100) := ⟨x₀_pos.le, by have := x₀_lt; linarith⟩
  have hXI : sg Gr.sm Gr.nx ∈ Icc (0 : ℝ) (65 / 100) := ⟨hx0.trans' x₀_pos.le, hstop⟩
  have hst := g_step hB hpI hdK hx0I hXI
  have hgd : gd p x₀ = 0 := integral_Gd_eq_zero
  have hG : G p x₀ = 0 := G_p_x₀_eq_zero
  rw [hgd, hG] at hst
  set dK := (Gr.dm : ℝ) / 2 ^ 128 with hdKdef
  set X := sg Gr.sm Gr.nx with hX
  have hXx : 0 ≤ X - x₀ := by linarith
  have hE : L2 * (X - x₀) ^ 2 / 2 + L1 * |dK - p| * |X - x₀| + 65 / 100 * L3 * (dK - p) ^ 2 / 2 ≤
      L2 * ρ' ^ 2 / 2 + L1 * ρ * ρ' + 65 / 100 * L3 * ρ ^ 2 / 2 := by
    have e1 : (X - x₀) ^ 2 ≤ ρ' ^ 2 := pow_le_pow_left₀ hXx hρ' 2
    have e2 : (dK - p) ^ 2 ≤ ρ ^ 2 := by
      rw [← sq_abs (dK - p)]; exact pow_le_pow_left₀ (abs_nonneg _) hρ 2
    have e3 : |dK - p| * |X - x₀| ≤ ρ * ρ' := by
      rw [abs_of_nonneg hXx]
      exact mul_le_mul hρ hρ' hXx ((abs_nonneg _).trans hρ)
    have := mul_le_mul_of_nonneg_left e3 hL1
    nlinarith [mul_le_mul_of_nonneg_left e1 hL2, mul_le_mul_of_nonneg_left e2 hL3]
  have hKdef : K = 2 * g p x₀ := rfl
  rw [hKdef]
  have : g p x₀ ≤ g dK X + (L2 * ρ' ^ 2 / 2 + L1 * ρ * ρ' + 65 / 100 * L3 * ρ ^ 2 / 2) := by
    rw [abs_of_nonneg hXx] at hst
    rw [abs_of_nonneg hXx] at hE
    linarith
  linarith

end SandierSerfaty.Certificate.Box
