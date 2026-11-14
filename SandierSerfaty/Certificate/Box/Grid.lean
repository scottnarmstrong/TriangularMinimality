/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Rows

/-!
# The grid arguments of the outer and negative-part assertions

Certificate-free statements of `comp:outer-grid` and `comp:negative-part` (paper `comp:outer-grid`, `comp:inner-domain`, `comp:outer-errors`),
for abstract node sequences `dN`, `xN` and abstract node bounds:

* `outer_of_nodes`: if `2g ≥ c` at every node `(dN j, xN k)` outside the open hole
  `(dN jl, dN jr) × (xN kl, xN kr)` (cells aligned with the hole's sides), then `2g ≥ c - E_x - E_d` at every
  point of the grid box outside the hole (`E_x`, `E_d` bound the 1-D interpolation errors of
  `comp:outer-errors`, `DerivBounds.cell_lower`);
* `outer_of_nodes_ext`: the same on `[dLo, dN nd]`, with the extra Lipschitz allowance `2 xHi L₁ (dN 0 - dLo)` for
  `d ∈ [dLo, dN 0)` (the first node is a dyadic point just above `b`);
* `negative_of_nodes`: if `∫₀ˣ max 0 (-G(dN j, ·)) ≤ N` at every node and the nodes are `D_h`-dense, then the integral
  is at most `N + X L₁ D_h/2` at every `d ∈ [dLo, dN nd]`.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Calibration

variable {dLo dHi xHi L1 L2 L3 L4 : ℝ}

/-- `g(·, x)` is `x L₁`-Lipschitz on `[dLo, dHi]`. -/
theorem DerivBounds.g_lip_d (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {x : ℝ} (hx : x ∈ Icc 0 xHi) :
    ∀ d ∈ Icc dLo dHi, ∀ d' ∈ Icc dLo dHi, |g d x - g d' x| ≤ x * L1 * |d - d'| := by
  intro d hd d' hd'
  have hd0 : 0 < d := lt_of_lt_of_le hB.pos hd.1
  have hd0' : 0 < d' := lt_of_lt_of_le hB.pos hd'.1
  unfold g
  rw [← intervalIntegral.integral_sub ((continuous_G hd0).intervalIntegrable 0 x)
    ((continuous_G hd0').intervalIntegrable 0 x)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := L1 * |d - d'|)
    (f := fun s => G d s - G d' s) (fun s hs => by
      rw [Set.uIoc_of_le hx.1] at hs
      rw [Real.norm_eq_abs]
      exact hB.G_lip_d ⟨hs.1.le, hs.2.trans hx.2⟩ d hd d' hd')
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **The outer grid** (`comp:outer-grid`, `comp:outer-errors`). -/
theorem DerivBounds.outer_of_nodes (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {nd nx : ℕ} {dN xN : ℕ → ℝ}
    (hdm : MonotoneOn dN (Set.Iic nd)) (hxm : MonotoneOn xN (Set.Iic nx))
    (hd0 : dLo ≤ dN 0) (hdn : dN nd ≤ dHi) (hx0 : 0 ≤ xN 0) (hxn : xN nx ≤ xHi)
    {jl jr kl kr : ℕ} (hjl : 0 < jl) (hjlr : jl ≤ nd) (hjr : jr < nd) (hkl : 0 < kl) (hklr : kl ≤ nx)
    (hkr : kr < nx) {c Ed Ex : ℝ} (hEx : ∀ k < nx, 2 * L2 * (xN (k + 1) - xN k) ^ 2 / 8 ≤ Ex)
    (hEd : ∀ j < nd, 2 * xHi * L3 * (dN (j + 1) - dN j) ^ 2 / 8 ≤ Ed)
    (hnode : ∀ j ≤ nd, ∀ k ≤ nx,
      (j ≤ jl ∨ jr ≤ j ∨ k ≤ kl ∨ kr ≤ k) → c ≤ 2 * g (dN j) (xN k)) :
    ∀ d ∈ Icc (dN 0) (dN nd), ∀ x ∈ Icc (xN 0) (xN nx),
      (d ≤ dN jl ∨ dN jr ≤ d ∨ x ≤ xN kl ∨ xN kr ≤ x) → c - Ex - Ed ≤ 2 * g d x := by
  have hnx : 0 < nx := by omega
  have hnd : 0 < nd := by omega
  have hdm' : ∀ i j, i ≤ j → j ≤ nd → dN i ≤ dN j := fun i j hij hj =>
    hdm (by simpa using hij.trans hj) hj hij
  have hxm' : ∀ i j, i ≤ j → j ≤ nx → xN i ≤ xN j := fun i j hij hj =>
    hxm (by simpa using hij.trans hj) hj hij
  -- the core: a cell with the four corner bounds
  have core : ∀ j k, j < nd → k < nx →
      (c ≤ 2 * g (dN j) (xN k) ∧ c ≤ 2 * g (dN j) (xN (k + 1)) ∧ c ≤ 2 * g (dN (j + 1)) (xN k) ∧
        c ≤ 2 * g (dN (j + 1)) (xN (k + 1))) →
      ∀ d ∈ Icc (dN j) (dN (j + 1)), ∀ x ∈ Icc (xN k) (xN (k + 1)), c - Ex - Ed ≤ 2 * g d x := by
    intro j k hj hk ⟨h11, h12, h21, h22⟩ d hd x hx
    have := hB.cell_lower (d₁ := dN j) (d₂ := dN (j + 1)) (x₁ := xN k) (x₂ := xN (k + 1)) (c := c)
      (hd0.trans (hdm' 0 j (Nat.zero_le _) hj.le)) ((hdm' (j + 1) nd hj le_rfl).trans hdn)
      (hx0.trans (hxm' 0 k (Nat.zero_le _) hk.le)) ((hxm' (k + 1) nx hk le_rfl).trans hxn) h11 h12 h21 h22 hd hx
    have e1 := hEx k hk
    have e2 := hEd j hj
    linarith
  intro d hd x hx hhole
  rcases hhole with h | h | h | h
  · obtain ⟨j, hj, hdj⟩ := exists_cell_left (a := dN) hjl hd.1 h
    obtain ⟨k, hk, hxk⟩ := exists_cell (a := xN) hnx hx.1 hx.2
    exact core j k (by omega) hk ⟨hnode j (by omega) k hk.le (Or.inl (by omega)),
      hnode j (by omega) (k + 1) hk (Or.inl (by omega)), hnode (j + 1) (by omega) k hk.le (Or.inl (by omega)),
      hnode (j + 1) (by omega) (k + 1) hk (Or.inl (by omega))⟩ d hdj x hxk
  · obtain ⟨j, hjJ, hj, hdj⟩ := exists_cell_right (a := dN) hjr h hd.2
    obtain ⟨k, hk, hxk⟩ := exists_cell (a := xN) hnx hx.1 hx.2
    exact core j k hj hk ⟨hnode j hj.le k hk.le (Or.inr (Or.inl hjJ)),
      hnode j hj.le (k + 1) hk (Or.inr (Or.inl hjJ)), hnode (j + 1) hj k hk.le (Or.inr (Or.inl (by omega))),
      hnode (j + 1) hj (k + 1) hk (Or.inr (Or.inl (by omega)))⟩ d hdj x hxk
  · obtain ⟨k, hk, hxk⟩ := exists_cell_left (a := xN) hkl hx.1 h
    obtain ⟨j, hj, hdj⟩ := exists_cell (a := dN) hnd hd.1 hd.2
    exact core j k hj (by omega) ⟨hnode j hj.le k (by omega) (Or.inr (Or.inr (Or.inl (by omega)))),
      hnode j hj.le (k + 1) (by omega) (Or.inr (Or.inr (Or.inl (by omega)))),
      hnode (j + 1) hj k (by omega) (Or.inr (Or.inr (Or.inl (by omega)))),
      hnode (j + 1) hj (k + 1) (by omega) (Or.inr (Or.inr (Or.inl (by omega))))⟩ d hdj x hxk
  · obtain ⟨k, hkJ, hk, hxk⟩ := exists_cell_right (a := xN) hkr h hx.2
    obtain ⟨j, hj, hdj⟩ := exists_cell (a := dN) hnd hd.1 hd.2
    exact core j k hj hk ⟨hnode j hj.le k hk.le (Or.inr (Or.inr (Or.inr hkJ))),
      hnode j hj.le (k + 1) hk (Or.inr (Or.inr (Or.inr (by omega)))),
      hnode (j + 1) hj k hk.le (Or.inr (Or.inr (Or.inr hkJ))),
      hnode (j + 1) hj (k + 1) hk (Or.inr (Or.inr (Or.inr (by omega))))⟩ d hdj x hxk

/-- **The outer grid on `[dLo, dN nd]`**: the extra allowance `2 xHi L₁ (dN 0 - dLo)` covers `d < dN 0`. -/
theorem DerivBounds.outer_of_nodes_ext (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {nd nx : ℕ} {dN xN : ℕ → ℝ}
    (hdm : MonotoneOn dN (Set.Iic nd)) (hxm : MonotoneOn xN (Set.Iic nx))
    (hd0 : dLo ≤ dN 0) (hdn : dN nd ≤ dHi) (hx0 : 0 ≤ xN 0) (hxn : xN nx ≤ xHi)
    {jl jr kl kr : ℕ} (hjl : 0 < jl) (hjlr : jl ≤ nd) (hjr : jr < nd) (hkl : 0 < kl) (hklr : kl ≤ nx)
    (hkr : kr < nx) {c Ed Ex : ℝ} (hEx : ∀ k < nx, 2 * L2 * (xN (k + 1) - xN k) ^ 2 / 8 ≤ Ex)
    (hEd : ∀ j < nd, 2 * xHi * L3 * (dN (j + 1) - dN j) ^ 2 / 8 ≤ Ed)
    (hnode : ∀ j ≤ nd, ∀ k ≤ nx,
      (j ≤ jl ∨ jr ≤ j ∨ k ≤ kl ∨ kr ≤ k) → c ≤ 2 * g (dN j) (xN k)) :
    ∀ d ∈ Icc dLo (dN nd), ∀ x ∈ Icc (xN 0) (xN nx),
      (d ≤ dN jl ∨ dN jr ≤ d ∨ x ≤ xN kl ∨ xN kr ≤ x) →
        c - Ex - Ed - 2 * xHi * L1 * (dN 0 - dLo) ≤ 2 * g d x := by
  intro d hd x hx hhole
  have hxm' : ∀ i j, i ≤ j → j ≤ nx → xN i ≤ xN j := fun i j hij hj =>
    hxm (by simpa using hij.trans hj) hj hij
  have hdm' : ∀ i j, i ≤ j → j ≤ nd → dN i ≤ dN j := fun i j hij hj =>
    hdm (by simpa using hij.trans hj) hj hij
  have hxI : x ∈ Icc 0 xHi := ⟨hx0.trans hx.1, hx.2.trans hxn⟩
  have hnonneg : 0 ≤ L1 := hB.nonneg.1
  rcases le_or_gt (dN 0) d with h0 | h0
  · have := hB.outer_of_nodes hdm hxm hd0 hdn hx0 hxn hjl hjlr hjr hkl hklr hkr hEx hEd hnode d ⟨h0, hd.2⟩ x hx hhole
    have : 0 ≤ 2 * xHi * L1 * (dN 0 - dLo) := by
      have := hxI.2
      have hx' : 0 ≤ xHi := hxI.1.trans hxI.2
      nlinarith [mul_nonneg (mul_nonneg hx' hnonneg) (sub_nonneg.2 hd0)]
    linarith
  · have hnd : 0 < nd := by omega
    have hhole' : dN 0 ≤ dN jl ∨ dN jr ≤ dN 0 ∨ x ≤ xN kl ∨ xN kr ≤ x := by
      rcases hhole with h | h | h | h
      · exact Or.inl (hdm' 0 jl (Nat.zero_le _) hjlr)
      · exact Or.inl (hdm' 0 jl (Nat.zero_le _) hjlr)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    have h1 := hB.outer_of_nodes hdm hxm hd0 hdn hx0 hxn hjl hjlr hjr hkl hklr hkr hEx hEd hnode (dN 0)
      ⟨le_rfl, hdm' 0 nd (Nat.zero_le _) le_rfl⟩ x hx hhole'
    have hdI : d ∈ Icc dLo dHi := ⟨hd.1, hd.2.trans hdn⟩
    have hdI0 : dN 0 ∈ Icc dLo dHi := ⟨hd0, (hdm' 0 nd (Nat.zero_le _) le_rfl).trans hdn⟩
    have h2 := hB.g_lip_d hxI (dN 0) hdI0 d hdI
    have h3 : |g (dN 0) x - g d x| ≤ x * L1 * (dN 0 - dLo) := by
      refine h2.trans ?_
      rw [abs_of_nonneg (by linarith : 0 ≤ dN 0 - d)]
      have : 0 ≤ x * L1 := mul_nonneg hxI.1 hnonneg
      nlinarith [hd.1]
    have h4 : x * L1 * (dN 0 - dLo) ≤ xHi * L1 * (dN 0 - dLo) := by
      have : 0 ≤ L1 * (dN 0 - dLo) := mul_nonneg hnonneg (sub_nonneg.2 hd0)
      nlinarith [hxI.2]
    have := (abs_le.1 h3).2
    linarith

/-- **The nearest node** (`comp:negative-part`: "every `d` lies within `D_h/2` of a node"). -/
theorem nearest_node {dN : ℕ → ℝ} {nd : ℕ} {Dh dLo : ℝ} (hdm : MonotoneOn dN (Set.Iic nd))
    (hstep : ∀ j < nd, dN (j + 1) - dN j ≤ Dh) (hdlo : dN 0 ≤ dLo + Dh / 2) :
    ∀ d ∈ Icc dLo (dN nd), ∃ j ≤ nd, |d - dN j| ≤ Dh / 2 := by
  intro d hd
  rcases le_or_gt d (dN 0) with h | h
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [abs_of_nonpos (by linarith)]
    linarith [hd.1]
  · have hnd : 0 < nd := by
      by_contra h0
      have : nd = 0 := by omega
      subst this
      have := hd.2
      linarith
    obtain ⟨j, hj, hdj⟩ := exists_cell (a := dN) hnd h.le hd.2
    have hs := hstep j hj
    rcases le_total (d - dN j) (dN (j + 1) - d) with hc | hc
    · refine ⟨j, hj.le, ?_⟩
      rw [abs_of_nonneg (by linarith [hdj.1])]
      linarith
    · refine ⟨j + 1, hj, ?_⟩
      rw [abs_of_nonpos (by linarith [hdj.2])]
      linarith

/-- **The negative part** (`comp:negative-assertion`): from the node rows to every `d ∈ [dLo, dN nd]`. -/
theorem DerivBounds.negative_of_nodes (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {nd : ℕ} {dN : ℕ → ℝ}
    {Dh X N : ℝ} (hdm : MonotoneOn dN (Set.Iic nd)) (hstep : ∀ j < nd, dN (j + 1) - dN j ≤ Dh)
    (hd0 : dLo ≤ dN 0) (hdlo : dN 0 ≤ dLo + Dh / 2) (hdn : dN nd ≤ dHi) (hX0 : 0 ≤ X) (hXx : X ≤ xHi)
    (hrow : ∀ j ≤ nd, ∫ s in (0 : ℝ)..X, max 0 (-G (dN j) s) ≤ N) :
    ∀ d ∈ Icc dLo (dN nd), ∫ s in (0 : ℝ)..X, max 0 (-G d s) ≤ N + X * L1 * Dh / 2 := by
  intro d hd
  obtain ⟨j, hj, hdist⟩ := nearest_node hdm hstep hdlo d hd
  have hdm' : ∀ i j, i ≤ j → j ≤ nd → dN i ≤ dN j := fun i j hij hj =>
    hdm (by simpa using hij.trans hj) hj hij
  have hdI : d ∈ Icc dLo dHi := ⟨hd.1, hd.2.trans hdn⟩
  have hdjI : dN j ∈ Icc dLo dHi := ⟨hd0.trans (hdm' 0 j (Nat.zero_le _) hj), (hdm' j nd hj le_rfl).trans hdn⟩
  have hd0' : 0 < d := lt_of_lt_of_le hB.pos hd.1
  have hdj0 : 0 < dN j := lt_of_lt_of_le hB.pos hdjI.1
  have hc1 : Continuous fun s => max 0 (-G d s) := by have := continuous_G hd0'; fun_prop
  have hc2 : Continuous fun s => max 0 (-G (dN j) s) := by have := continuous_G hdj0; fun_prop
  have hmono : ∫ s in (0 : ℝ)..X, max 0 (-G d s) ≤
      ∫ s in (0 : ℝ)..X, (max 0 (-G (dN j) s) + L1 * |d - dN j|) := by
    refine intervalIntegral.integral_mono_on hX0 (hc1.intervalIntegrable _ _)
      ((hc2.add continuous_const).intervalIntegrable _ _) fun s hs => ?_
    have := hB.G_lip_d (⟨hs.1, hs.2.trans hXx⟩ : s ∈ Icc 0 xHi) d hdI (dN j) hdjI
    have h2 : |max 0 (-G d s) - max 0 (-G (dN j) s)| ≤ |G d s - G (dN j) s| := by
      calc _ = |max (-G d s) 0 - max (-G (dN j) s) 0| := by rw [max_comm 0 (-G d s), max_comm 0 (-G (dN j) s)]
        _ ≤ |-G d s - -G (dN j) s| := abs_max_sub_max_le_abs _ _ _
        _ = _ := by rw [← abs_neg]; congr 1; ring
    have := (abs_le.1 (h2.trans this)).2
    linarith
  rw [intervalIntegral.integral_add (hc2.intervalIntegrable _ _) intervalIntegrable_const] at hmono
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  have h3 := hrow j hj
  have h4 : X * (L1 * |d - dN j|) ≤ X * (L1 * (Dh / 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist hB.nonneg.1) hX0
  linarith

end SandierSerfaty.Certificate.Box
