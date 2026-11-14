/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.LoopSound
public import SandierSerfaty.Certificate.Box.Grid

/-!
# The outer assertion `K ≤ 2g` on `𝒟 ∖ int 𝒟₀` from the rows (A8, theorem T2)

`row_node_bound` turns a passing outer row (`Box.Eval.outerLoop`) into the node bounds
`thr/2^256 - (L₄ S_h²/12 + 2δ) xHi ≤ 2 g_d(σ_i)`: the exact accumulator is the midpoint sum of the evaluated
values, which is within `δ σ_i` of the midpoint sum of `G` (the static budget `deltaMax`) and within
`L₄ S_h² σ_i/24` of the exact primitive (`g_sub_midSum`, the term `E₀` of `comp:outer-errors`).

`outer_of_rows` is the conclusion `∀ q ∈ boxD ∖ int boxD₀, K ≤ 2 g q.1 q.2`, **conditional on the derivative bounds
A7** (`DerivBounds`) and on the finite data: the rows, the grid facts, a literal upper bound `Kc ≥ K` and the
threshold inequality `hthr` (a literal numerical inequality). The derivative bounds are derived from interval checks in
`Box.Deriv`/`Box.Cert`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The `s` node `k` of a partition with mantissas `sm`. -/
@[expose] noncomputable def sg (sm : ℕ → ℕ) (k : ℕ) : ℝ := (sm k : ℝ) / 2 ^ 128

theorem sg_mono {sm : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, sm j ≤ sm (j + 1)) : MonotoneOn (sg sm) (Set.Iic n) := by
  intro a ha b hb hab
  have key : ∀ k, a ≤ k → k ≤ n → sg sm a ≤ sg sm k := by
    intro k hak
    induction k, hak using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hak ih =>
      intro hk
      refine (ih (by omega)).trans ?_
      unfold sg
      exact div_le_div_of_nonneg_right (by exact_mod_cast h k (by omega)) (by positivity)
  exact key b hab hb

/-- **A passing outer row** gives the node bounds for `g`. -/
theorem row_node_bound (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) {dLo dHi xHi L1 L2 L3 L4 Sh δ : ℝ}
    (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {idx : ℕ → ℕ} {dm : ℕ} {sm : ℕ → ℕ} {thr : SInt}
    {inRow : Bool} {kl kr n : ℕ} (hrow : outerLoop E idx dm sm thr inRow kl kr n 0 SInt.zero = true)
    (hdI : (dm : ℝ) / 2 ^ 128 ∈ Icc dLo dHi) (hdb : Calibration.b ≤ (dm : ℝ) / 2 ^ 128)
    (hd1 : (dm : ℝ) / 2 ^ 128 ≤ 1) (hs0 : sm 0 = 0) (hstop : sg sm n ≤ xHi)
    (hstep : ∀ j < n, sg sm (j + 1) - sg sm j ≤ Sh) (hδ0 : 0 ≤ δ)
    (hδ : deltaMax rf re rlam rmu rκ rc ≤ δ) :
    ∀ i ≤ n, skipB inRow kl kr i = true ∨
      (thr.toInt : ℝ) / 2 ^ 256 - (L4 * Sh ^ 2 / 12 + 2 * δ) * xHi ≤ 2 * g ((dm : ℝ) / 2 ^ 128) (sg sm i) := by
  obtain ⟨v, hv, hnodes⟩ := outerLoop_sound E idx dm sm thr inRow kl kr n 0 SInt.zero hrow
  have hmono : ∀ j < n, sm j ≤ sm (j + 1) := fun j hj => by simpa using (hv j hj).2
  have hP : Partition (sg sm) n xHi Sh :=
    ⟨fun j hj => by
      unfold sg
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmono j hj) (by positivity),
     by simp [sg, hs0], hstop, hstep⟩
  have hvR : ∀ j < n, |(v j).val - G ((dm : ℝ) / 2 ^ 128) ((sg sm j + sg sm (j + 1)) / 2)| ≤ δ := by
    intro j hj
    have := (midVal_sound hc H hdb hd1 (by simpa using (hv j hj).1)).2
    exact (le_trans this hδ : _)
  have h1 := abs_sum_sub_midSum (F := G ((dm : ℝ) / 2 ^ 128)) hP (v := fun j => (v j).val) hvR
  have h2 := hB.g_sub_midSum hdI hP
  intro i hi
  rcases hnodes i hi with hskip | hthr
  · exact Or.inl (by simpa using hskip)
  · refine Or.inr ?_
    simp only [zero_add, SInt.toInt_zero] at hthr
    have hZ : (((∑ j ∈ Finset.range i, ((sm (j + 1) : ℤ) - sm j) * (v j).v.toInt : ℤ)) : ℝ) =
        2 ^ 256 * ∑ j ∈ Finset.range i, (sg sm (j + 1) - sg sm j) * (v j).val := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [sg, Fx.val_def]
      field_simp
    have hthrR : (thr.toInt : ℝ) ≤ 2 * (2 ^ 256 * ∑ j ∈ Finset.range i, (sg sm (j + 1) - sg sm j) * (v j).val) := by
      rw [← hZ]
      exact_mod_cast hthr
    have hQ : (thr.toInt : ℝ) / 2 ^ 256 ≤ 2 * ∑ j ∈ Finset.range i, (sg sm (j + 1) - sg sm j) * (v j).val := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hσ := hP.mem_Icc hi
    have a1 := (abs_le.1 (h1 i hi)).2
    have a2 := (abs_le.1 (h2 i hi)).1
    have hL4 := hB.nonneg.2.2.2
    have hbd : (L4 * Sh ^ 2 / 12 + 2 * δ) * sg sm i ≤ (L4 * Sh ^ 2 / 12 + 2 * δ) * xHi :=
      mul_le_mul_of_nonneg_left hσ.2 (by positivity)
    nlinarith [hσ.1]

/-- **The outer assertion from the rows** (A8, T2), conditional on the derivative bounds A7. -/
theorem outer_of_rows (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) (G : OuterGrid) {L1 L2 L3 L4 Sh Dh δ Kc ρ : ℝ}
    (hB : DerivBounds Calibration.b (sg G.dm G.nd) (sg G.sm G.nx) L1 L2 L3 L4)
    -- the `d` grid
    (hdm : ∀ j < G.nd, G.dm j ≤ G.dm (j + 1)) (hdlo : Calibration.b ≤ sg G.dm 0)
    (hdρ : sg G.dm 0 - Calibration.b ≤ ρ) (hdstep : ∀ j < G.nd, sg G.dm (j + 1) - sg G.dm j ≤ Dh)
    (hdtop : (697 : ℝ) / 1000 ≤ sg G.dm G.nd) (hd1 : sg G.dm G.nd ≤ 1)
    -- the `s` grid
    (hs0 : G.sm 0 = 0) (hsm : ∀ k < G.nx, G.sm k ≤ G.sm (k + 1))
    (hxstep : ∀ k < G.nx, sg G.sm (k + 1) - sg G.sm k ≤ Sh) (hxtop : (65 : ℝ) / 100 ≤ sg G.sm G.nx)
    -- the hole, inside `𝒟₀`
    (hjl : 0 < G.jl) (hjlr : G.jl ≤ G.nd) (hjr : G.jr < G.nd) (hkl : 0 < G.kl) (hklr : G.kl ≤ G.nx)
    (hkr : G.kr < G.nx) (hD1 : (52528 : ℝ) / 100000 ≤ sg G.dm G.jl) (hD2 : sg G.dm G.jr ≤ 54930 / 100000)
    (hX1 : (29420 : ℝ) / 100000 ≤ sg G.sm G.kl) (hX2 : sg G.sm G.kr ≤ 32621 / 100000)
    -- the rows
    (hrows : ∀ j ≤ G.nd, G.row E j = true)
    -- the constants
    (hK : Calibration.K ≤ Kc) (hδ0 : 0 ≤ δ) (hδ : deltaMax rf re rlam rmu rκ rc ≤ δ)
    (hthr : Kc + 2 * L2 * Sh ^ 2 / 8 + 2 * sg G.sm G.nx * L3 * Dh ^ 2 / 8 + 2 * sg G.sm G.nx * L1 * ρ +
      (L4 * Sh ^ 2 / 12 + 2 * δ) * sg G.sm G.nx ≤ (G.thr.toInt : ℝ) / 2 ^ 256) :
    ∀ q ∈ boxD \ interior boxD₀, Calibration.K ≤ 2 * g q.1 q.2 := by
  have hbpos : (0 : ℝ) < Calibration.b := Calibration.b_pos
  have hdmo := sg_mono hdm
  have hxmo := sg_mono hsm
  have hxN0 : sg G.sm 0 = 0 := by simp [sg, hs0]
  have hxH : 0 ≤ sg G.sm G.nx := by
    have := hxmo (by simp : 0 ∈ Set.Iic G.nx) (by simp : G.nx ∈ Set.Iic G.nx) (Nat.zero_le _)
    linarith
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hB.nonneg
  set Ex : ℝ := 2 * L2 * Sh ^ 2 / 8 with hEx
  set Ed : ℝ := 2 * sg G.sm G.nx * L3 * Dh ^ 2 / 8 with hEd
  have hdle : ∀ j, j ≤ G.nd → sg G.dm 0 ≤ sg G.dm j := fun j hj =>
    hdmo (by simp : 0 ∈ Set.Iic G.nd) (by simpa using hj) (Nat.zero_le _)
  have hdle' : ∀ j, j ≤ G.nd → sg G.dm j ≤ sg G.dm G.nd := fun j hj =>
    hdmo (by simpa using hj) (by simp : G.nd ∈ Set.Iic G.nd) hj
  have hnode : ∀ j ≤ G.nd, ∀ k ≤ G.nx, (j ≤ G.jl ∨ G.jr ≤ j ∨ k ≤ G.kl ∨ G.kr ≤ k) →
      Kc + Ex + Ed + 2 * sg G.sm G.nx * L1 * ρ ≤ 2 * g (sg G.dm j) (sg G.sm k) := by
    intro j hj k hk hpre
    have hrow := hrows j hj
    have hdj : (G.dm j : ℝ) / 2 ^ 128 ∈ Icc Calibration.b (sg G.dm G.nd) := ⟨hdlo.trans (hdle j hj), hdle' j hj⟩
    have := row_node_bound hc H hB (n := G.nx) hrow hdj (hdlo.trans (hdle j hj)) ((hdle' j hj).trans hd1) hs0 le_rfl
      hxstep hδ0 hδ k hk
    rcases this with hskip | hb
    · exfalso
      simp [skipB, inRowB, Nat.blt_eq] at hskip
      omega
    · have : (G.dm j : ℝ) / 2 ^ 128 = sg G.dm j := rfl
      rw [this] at hb
      linarith
  have hext := hB.outer_of_nodes_ext (dN := sg G.dm) (xN := sg G.sm) (nd := G.nd) (nx := G.nx) hdmo hxmo hdlo
    le_rfl (by rw [hxN0]) le_rfl hjl hjlr hjr hkl hklr hkr (c := Kc + Ex + Ed + 2 * sg G.sm G.nx * L1 * ρ)
    (Ed := Ed) (Ex := Ex)
    (fun k hk => by
      have h0 : 0 ≤ sg G.sm (k + 1) - sg G.sm k := by
        have := hxmo (by simpa using hk.le : k ∈ Set.Iic G.nx) (by simpa using hk : k + 1 ∈ Set.Iic G.nx)
          (Nat.le_succ k)
        linarith
      have h1 := pow_le_pow_left₀ h0 (hxstep k hk) 2
      have : 0 ≤ 2 * L2 / 8 := by positivity
      rw [hEx]
      nlinarith)
    (fun j hj => by
      have h0 : 0 ≤ sg G.dm (j + 1) - sg G.dm j := by
        have := hdmo (by simpa using hj.le : j ∈ Set.Iic G.nd) (by simpa using hj : j + 1 ∈ Set.Iic G.nd)
          (Nat.le_succ j)
        linarith
      have h1 := pow_le_pow_left₀ h0 (hdstep j hj) 2
      have : 0 ≤ 2 * sg G.sm G.nx * L3 / 8 := by positivity
      rw [hEd]
      nlinarith)
    hnode
  intro q hq
  obtain ⟨hqD, hqI⟩ := hq
  have hq1 : q.1 ∈ Icc Calibration.b (697 / 1000 : ℝ) := hqD.1
  have hq2 : q.2 ∈ Icc (0 : ℝ) (65 / 100) := hqD.2
  have hhole : q.1 ≤ sg G.dm G.jl ∨ sg G.dm G.jr ≤ q.1 ∨ q.2 ≤ sg G.sm G.kl ∨ sg G.sm G.kr ≤ q.2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, c4⟩ := hcon
    apply hqI
    unfold boxD₀
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have := hext q.1 ⟨hq1.1, hq1.2.trans hdtop⟩ q.2 ⟨by rw [hxN0]; exact hq2.1, hq2.2.trans hxtop⟩ hhole
  have h3 : 2 * sg G.sm G.nx * L1 * (sg G.dm 0 - Calibration.b) ≤ 2 * sg G.sm G.nx * L1 * ρ :=
    mul_le_mul_of_nonneg_left hdρ (by positivity)
  linarith

end SandierSerfaty.Certificate.Box
