/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.HessCell
public import SandierSerfaty.Certificate.Box.Rows
public import SandierSerfaty.Certificate.Box.CtxSound

/-!
# `LocalHess` from the cells of a product partition (paper `comp:hessian`)

`exists_cell_dir`: a point `y` and a direction `w` whose forward ray stays in `[a_J, a_n]` have a cell `[a_i, a_{i+1}]`,
`J ≤ i < n`, of the node sequence `a` containing `y` and the ray for a short time (a right cell when `w > 0`, a left
cell when `w < 0`).

`localHess_of_cells`: `LocalHess S` for a set `S` inside `[dpt 0, dpt nd] × [σ jmin, σ nx]` from `CellHess` on every
product cell `[dpt i, dpt (i+1)] × [σ k, σ (k+1)]` with `jmin ≤ k` (the Hessian is tested only above the node
`σ jmin`; the cells below it only serve the accumulation of `A`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Calibration

theorem exists_cell_dir {a : ℕ → ℝ} {J n : ℕ} (hJ : J < n) {y w ε0 : ℝ} (hε0 : 0 < ε0)
    (hray : ∀ h ∈ Icc (0 : ℝ) ε0, y + h * w ∈ Icc (a J) (a n)) :
    ∃ i, J ≤ i ∧ i < n ∧ y ∈ Icc (a i) (a (i + 1)) ∧
      ∃ ε > 0, ∀ h ∈ Icc (0 : ℝ) ε, y + h * w ∈ Icc (a i) (a (i + 1)) := by
  classical
  have hy0 := hray 0 ⟨le_rfl, hε0.le⟩
  simp only [zero_mul, add_zero] at hy0
  have hye := hray ε0 ⟨hε0.le, le_rfl⟩
  rcases lt_trichotomy w 0 with hw | hw | hw
  · -- left cell
    have hyJ : a J < y := by nlinarith [hye.1]
    have hex : ∃ k, k < n - J ∧ y ≤ a (J + k + 1) :=
      ⟨n - J - 1, by omega, by rw [show J + (n - J - 1) + 1 = n by omega]; exact hy0.2⟩
    set k := Nat.find hex with hk
    obtain ⟨hkn, hky⟩ := Nat.find_spec hex
    have hlt : a (J + k) < y := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]; simpa using hyJ
      · have := Nat.find_min hex (show k - 1 < k by omega)
        have h2 : ¬ (k - 1 < n - J ∧ y ≤ a (J + (k - 1) + 1)) := this
        rw [show J + (k - 1) + 1 = J + k by omega] at h2
        exact not_le.1 fun h4 => h2 ⟨by omega, h4⟩
    refine ⟨J + k, by omega, by omega, ⟨hlt.le, hky⟩, (y - a (J + k)) / (-w), div_pos (by linarith) (by linarith),
      fun h hh => ⟨?_, ?_⟩⟩
    · have : h * (-w) ≤ y - a (J + k) := by
        have := hh.2
        rwa [le_div_iff₀ (by linarith)] at this
      nlinarith
    · nlinarith [hh.1]
  · subst hw
    obtain ⟨i, hJi, hin, hyi⟩ := exists_cell_right hJ hy0.1 hy0.2
    exact ⟨i, hJi, hin, hyi, 1, one_pos, fun h _ => by simpa using hyi⟩
  · -- right cell
    have hyn : y < a n := by nlinarith [hye.2]
    obtain ⟨j, hj, h1, h2⟩ := exists_cell_right_strict (a := fun k => a (J + k)) (n := n - J) (by omega) (y := y)
      (by simpa using hy0.1) (by simpa [show J + (n - J) = n by omega] using hyn)
    have h2' : y < a (J + j + 1) := h2
    refine ⟨J + j, by omega, by omega, ⟨h1, h2'.le⟩, (a (J + j + 1) - y) / w, div_pos (by linarith) hw,
      fun h hh => ⟨?_, ?_⟩⟩
    · nlinarith [hh.1]
    · have : h * w ≤ a (J + j + 1) - y := by
        have := hh.2
        rwa [le_div_iff₀ hw] at this
      linarith

/-- **`LocalHess` from the cells.** -/
theorem localHess_of_cells {S : Set (ℝ × ℝ)} {nd nx jmin : ℕ} {dpt σ : ℕ → ℝ} {A B C : ℕ → ℕ → IV 128}
    (hnd : 0 < nd) (hnx : jmin < nx)
    (hS : ∀ q ∈ S, q.1 ∈ Icc (dpt 0) (dpt nd) ∧ q.2 ∈ Icc (σ jmin) (σ nx))
    (hcell : ∀ i < nd, ∀ k, jmin ≤ k → k < nx →
      CellHess (Icc (dpt i) (dpt (i + 1))) (Icc (σ k) (σ (k + 1))) (A i k) (B i k) (C i k)) :
    LocalHess S := by
  intro d x u v hq ⟨ε0, hε0, hray⟩
  obtain ⟨i, -, hi, hdi, ε1, hε1, hr1⟩ := exists_cell_dir (a := dpt) (J := 0) hnd (y := d) (w := u) hε0
    (fun h hh => (hS _ (hray h hh)).1)
  obtain ⟨k, hjk, hk, hxk, ε2, hε2, hr2⟩ := exists_cell_dir (a := σ) (J := jmin) hnx (y := x) (w := v) hε0
    (fun h hh => (hS _ (hray h hh)).2)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun h hh => ?_⟩
  rcases hh.1.eq_or_lt with h0 | hpos
  · subst h0; simp
  · exact (hcell i hi k hjk hk).step hdi (hr1 h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩) hxk
      (hr2 h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩) hpos rfl rfl

end SandierSerfaty.Certificate.Box
