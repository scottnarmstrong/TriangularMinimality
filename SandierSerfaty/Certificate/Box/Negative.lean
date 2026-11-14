/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Outer

/-!
# The negative part from the rows (A9, theorem T3)

paper `comp:negative-part`, `comp:negative-assertion`. `negRow_bound` turns a passing
negative-part row (`Box.Eval.negLoop`) into
`∫₀^{σ_n} max 0 (-G(d, s)) ds ≤ thr/2^256 + (δ + L₂ S_h/4) σ_n` (the evaluated sum, the evaluation error `δ σ_n` and the
midpoint error `L₂ S_h σ_n/4`); `negative_of_rows` is the conclusion
`∀ d ∈ [b, .697], ∫₀^{.65} max 0 (-G(d, s)) ds ≤ -K` (nearest node, `.65 D_h L₁/2`), **conditional on the derivative
bounds A7** (`DerivBounds`) and on the finite data.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query SandierSerfaty.Calibration SandierSerfaty.Tails

theorem abs_negPart_sub_le (x y : ℝ) : |max 0 (-x) - max 0 (-y)| ≤ |x - y| := by
  calc _ = |max (-x) 0 - max (-y) 0| := by rw [max_comm 0 (-x), max_comm 0 (-y)]
    _ ≤ |-x - -y| := abs_max_sub_max_le_abs _ _ _
    _ = _ := by rw [← abs_neg]; congr 1; ring

/-- **A passing negative-part row** bounds the integral. -/
theorem negRow_bound (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) {dLo dHi xHi L1 L2 L3 L4 Sh δ : ℝ}
    (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {idx : ℕ → ℕ} {dm : ℕ} {sm : ℕ → ℕ} {thr : SInt} {n : ℕ}
    (hrow : negLoop E idx dm sm thr n 0 SInt.zero = true)
    (hdI : (dm : ℝ) / 2 ^ 128 ∈ Icc dLo dHi) (hdb : Calibration.b ≤ (dm : ℝ) / 2 ^ 128)
    (hd1 : (dm : ℝ) / 2 ^ 128 ≤ 1) (hs0 : sm 0 = 0) (hstop : sg sm n ≤ xHi)
    (hstep : ∀ j < n, sg sm (j + 1) - sg sm j ≤ Sh) (hδ : deltaMax rf re rlam rmu rκ rc ≤ δ) :
    ∫ s in (0 : ℝ)..sg sm n, max 0 (-G ((dm : ℝ) / 2 ^ 128) s) ≤
      (thr.toInt : ℝ) / 2 ^ 256 + (δ + L2 * Sh / 4) * sg sm n := by
  obtain ⟨v, hv, hsum⟩ := negLoop_sound E idx dm sm thr n 0 SInt.zero hrow
  have hmono : ∀ j < n, sm j ≤ sm (j + 1) := fun j hj => by simpa using (hv j hj).2
  have hP : Partition (sg sm) n xHi Sh :=
    ⟨fun j hj => by
      unfold sg
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmono j hj) (by positivity),
     by simp [sg, hs0], hstop, hstep⟩
  have hvR : ∀ j < n, |max 0 (-(v j).val) - max 0 (-G ((dm : ℝ) / 2 ^ 128) ((sg sm j + sg sm (j + 1)) / 2))| ≤ δ := by
    intro j hj
    have := (midVal_sound hc H hdb hd1 (by simpa using (hv j hj).1)).2
    exact (abs_negPart_sub_le _ _).trans (this.trans hδ)
  have h1 := abs_sum_sub_midSum (F := fun s => max 0 (-G ((dm : ℝ) / 2 ^ 128) s)) hP
    (v := fun j => max 0 (-(v j).val)) hvR
  have h2 := hB.integral_max_sub_midSum hdI hP
  have hZ : (((∑ j ∈ Finset.range n, ((sm (j + 1) : ℤ) - sm j) * max 0 (-(v j).v.toInt) : ℤ)) : ℝ) =
      2 ^ 256 * ∑ j ∈ Finset.range n, (sg sm (j + 1) - sg sm j) * max 0 (-(v j).val) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc0 : (0 : ℝ) ≤ 2 ^ 128 := by positivity
    have : max 0 (-((v j).v.toInt : ℝ)) = 2 ^ 128 * max 0 (-(v j).val) := by
      rw [mul_max_of_nonneg _ _ hc0, mul_zero, Fx.val_def]
      congr 1
      field_simp
    rw [this]
    simp only [sg]
    field_simp
  simp only [zero_add, SInt.toInt_zero] at hsum
  have hsumR : 2 ^ 256 * ∑ j ∈ Finset.range n, (sg sm (j + 1) - sg sm j) * max 0 (-(v j).val) ≤ (thr.toInt : ℝ) := by
    rw [← hZ]; exact_mod_cast hsum
  have hQ : ∑ j ∈ Finset.range n, (sg sm (j + 1) - sg sm j) * max 0 (-(v j).val) ≤ (thr.toInt : ℝ) / 2 ^ 256 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have a1 := (abs_le.1 (h1 n le_rfl)).1
  have a2 := (abs_le.1 (h2 n le_rfl)).2
  have : (∫ s in (0 : ℝ)..sg sm n, max 0 (-G ((dm : ℝ) / 2 ^ 128) s)) ≤
      (thr.toInt : ℝ) / 2 ^ 256 + δ * sg sm n + L2 * Sh * sg sm n / 4 := by linarith
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **The negative part from the rows** (A9, T3), conditional on the derivative bounds A7. -/
theorem negative_of_rows (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) (Gr : NegGrid) {L1 L2 L3 L4 Sh Dh δ Kc : ℝ}
    (hB : DerivBounds Calibration.b (sg Gr.dm Gr.nd) (sg Gr.sm Gr.nx) L1 L2 L3 L4)
    -- the `d` grid
    (hdm : ∀ j < Gr.nd, Gr.dm j ≤ Gr.dm (j + 1)) (hdlo : Calibration.b ≤ sg Gr.dm 0)
    (hdnear : sg Gr.dm 0 ≤ Calibration.b + Dh / 2) (hdstep : ∀ j < Gr.nd, sg Gr.dm (j + 1) - sg Gr.dm j ≤ Dh)
    (hdtop : (697 : ℝ) / 1000 ≤ sg Gr.dm Gr.nd) (hd1 : sg Gr.dm Gr.nd ≤ 1)
    -- the `s` grid
    (hs0 : Gr.sm 0 = 0) (hsm : ∀ k < Gr.nx, Gr.sm k ≤ Gr.sm (k + 1))
    (hxstep : ∀ k < Gr.nx, sg Gr.sm (k + 1) - sg Gr.sm k ≤ Sh) (hxtop : (65 : ℝ) / 100 ≤ sg Gr.sm Gr.nx)
    -- the rows
    (hrows : ∀ j ≤ Gr.nd, Gr.row E j = true)
    -- the constants
    (hK : Calibration.K ≤ Kc) (hδ : deltaMax rf re rlam rmu rκ rc ≤ δ)
    (hthr : (Gr.thr.toInt : ℝ) / 2 ^ 256 + (δ + L2 * Sh / 4) * sg Gr.sm Gr.nx + sg Gr.sm Gr.nx * L1 * Dh / 2 + Kc ≤ 0) :
    ∀ d ∈ Icc Calibration.b (697 / 1000 : ℝ), ∫ s in (0 : ℝ)..(65 / 100 : ℝ), max 0 (-G d s) ≤ -Calibration.K := by
  have hbpos : (0 : ℝ) < Calibration.b := Calibration.b_pos
  have hdmo := sg_mono hdm
  have hxmo := sg_mono hsm
  have hxN0 : sg Gr.sm 0 = 0 := by simp [sg, hs0]
  have hxH : 0 ≤ sg Gr.sm Gr.nx := by
    have := hxmo (by simp : 0 ∈ Set.Iic Gr.nx) (by simp : Gr.nx ∈ Set.Iic Gr.nx) (Nat.zero_le _)
    linarith
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hB.nonneg
  have hdle : ∀ j, j ≤ Gr.nd → sg Gr.dm 0 ≤ sg Gr.dm j := fun j hj =>
    hdmo (by simp : 0 ∈ Set.Iic Gr.nd) (by simpa using hj) (Nat.zero_le _)
  have hdle' : ∀ j, j ≤ Gr.nd → sg Gr.dm j ≤ sg Gr.dm Gr.nd := fun j hj =>
    hdmo (by simpa using hj) (by simp : Gr.nd ∈ Set.Iic Gr.nd) hj
  have hrow : ∀ j ≤ Gr.nd, ∫ s in (0 : ℝ)..sg Gr.sm Gr.nx, max 0 (-G (sg Gr.dm j) s) ≤
      (Gr.thr.toInt : ℝ) / 2 ^ 256 + (δ + L2 * Sh / 4) * sg Gr.sm Gr.nx := by
    intro j hj
    have hdj : (Gr.dm j : ℝ) / 2 ^ 128 ∈ Icc Calibration.b (sg Gr.dm Gr.nd) :=
      ⟨hdlo.trans (hdle j hj), hdle' j hj⟩
    exact negRow_bound hc H hB (n := Gr.nx) (hrows j hj) hdj (hdlo.trans (hdle j hj)) ((hdle' j hj).trans hd1) hs0
      le_rfl hxstep hδ
  have hmain := hB.negative_of_nodes (dN := sg Gr.dm) (nd := Gr.nd) (Dh := Dh) (X := sg Gr.sm Gr.nx)
    (N := (Gr.thr.toInt : ℝ) / 2 ^ 256 + (δ + L2 * Sh / 4) * sg Gr.sm Gr.nx) hdmo hdstep hdlo hdnear le_rfl hxH le_rfl
    hrow
  intro d hd
  have h1 := hmain d ⟨hd.1, hd.2.trans hdtop⟩
  have hmono : (∫ s in (0 : ℝ)..(65 / 100 : ℝ), max 0 (-G d s)) ≤ ∫ s in (0 : ℝ)..sg Gr.sm Gr.nx, max 0 (-G d s) := by
    have hd0 : 0 < d := lt_of_lt_of_le hbpos hd.1
    have hc1 : Continuous fun s => max 0 (-G d s) := by have := continuous_G hd0; fun_prop
    exact intervalIntegral.integral_mono_interval le_rfl (by norm_num) hxtop
      (Filter.Eventually.of_forall fun s => le_max_left _ _) (hc1.intervalIntegrable _ _)
  linarith

end SandierSerfaty.Certificate.Box
