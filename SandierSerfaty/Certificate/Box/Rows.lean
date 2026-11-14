/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Prim

/-!
# Midpoint rows of the box assertions (paper `comp:outer-grid`, `comp:negative-part`)

For a fixed `d` and a partition `0 = σ₀ ≤ σ₁ ≤ … ≤ σₙ` of the `s` axis:

* `midSum F σ k = ∑_{j<k} (σ_{j+1} - σ_j) F((σ_j + σ_{j+1})/2)` is the midpoint sum;
* `g_sub_midSum`: `|g_d(σ_k) - midSum (G d) σ k| ≤ L₄ S_h² σ_k/24` (`E₀` of `comp:outer-errors`);
* `integral_max_sub_midSum`: `|∫₀^{σ_k} max 0 (-G) - midSum (max 0 (-G)) σ k| ≤ L₂ S_h σ_k/4`
  (the term `.65 S_h L₂/4` of `comp:negative-assertion`);
* `abs_sum_sub_midSum`: replacing `F(m_j)` by values within `δ` changes the sum by at most `δ σ_k`.

`outer_of_nodes` is the grid argument of `comp:outer-grid`: from `2g ≥ c` at the nodes outside the hole it
follows that `2g ≥ c - E_x - E_d` on the whole grid box outside the hole (cells aligned with the hole's sides);
`exists_cell_*` select the cell of the partition. `nearest_node` is the nearest-node step of
`comp:negative-part`.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Calibration

/-- The midpoint sum of `F` over the first `k` cells of `σ`. -/
@[expose] noncomputable def midSum (F : ℝ → ℝ) (σ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (σ (j + 1) - σ j) * F ((σ j + σ (j + 1)) / 2)

theorem midSum_succ (F : ℝ → ℝ) (σ : ℕ → ℝ) (k : ℕ) :
    midSum F σ (k + 1) = midSum F σ k + (σ (k + 1) - σ k) * F ((σ k + σ (k + 1)) / 2) := by
  unfold midSum; rw [Finset.sum_range_succ]

variable {dLo dHi xHi L1 L2 L3 L4 : ℝ}

/-- A partition of `[0, xHi]`: monotone on `{0, …, n}`, starting at `0`, with steps at most `Sh`. -/
structure Partition (σ : ℕ → ℝ) (n : ℕ) (xHi Sh : ℝ) : Prop where
  mono : ∀ j < n, σ j ≤ σ (j + 1)
  zero : σ 0 = 0
  top : σ n ≤ xHi
  step : ∀ j < n, σ (j + 1) - σ j ≤ Sh

theorem Partition.nonneg {σ : ℕ → ℝ} {n : ℕ} {Sh : ℝ} (hP : Partition σ n xHi Sh) : ∀ j ≤ n, 0 ≤ σ j := by
  intro j
  induction j with
  | zero => intro _; rw [hP.zero]
  | succ i ih => intro h; exact (ih (by omega)).trans (hP.mono i (by omega))

theorem Partition.le_top {σ : ℕ → ℝ} {n : ℕ} {Sh : ℝ} (hP : Partition σ n xHi Sh) : ∀ j ≤ n, σ j ≤ xHi := by
  have key : ∀ m i, n - i = m → i ≤ n → σ i ≤ σ n := by
    intro m
    induction m with
    | zero => intro i hi hin; have : i = n := by omega
              rw [this]
    | succ m ih =>
      intro i hi hin
      exact (hP.mono i (by omega)).trans (ih (i + 1) (by omega) (by omega))
  intro j hj
  exact (key _ j rfl hj).trans hP.top

theorem Partition.mem_Icc {σ : ℕ → ℝ} {n : ℕ} {Sh : ℝ} (hP : Partition σ n xHi Sh) {j : ℕ} (hj : j ≤ n) :
    σ j ∈ Icc 0 xHi := ⟨hP.nonneg j hj, hP.le_top j hj⟩

/-! ### The exact primitive against the midpoint sum -/

theorem DerivBounds.g_sub_midSum (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d : ℝ} (hd : d ∈ Icc dLo dHi)
    {σ : ℕ → ℝ} {n : ℕ} {Sh : ℝ} (hP : Partition σ n xHi Sh) :
    ∀ k ≤ n, |g d (σ k) - midSum (G d) σ k| ≤ L4 * Sh ^ 2 * σ k / 24 := by
  have hd0 : 0 < d := lt_of_lt_of_le hB.pos hd.1
  intro k
  induction k with
  | zero => intro _; simp [midSum, g, hP.zero]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hmk := hP.mono k (by omega)
    have hk0 := hP.mem_Icc (by omega : k ≤ n)
    have hk1 := hP.mem_Icc hk
    have hcell : |(∫ s in σ k..σ (k + 1), G d s) - (σ (k + 1) - σ k) * G d ((σ k + σ (k + 1)) / 2)| ≤
        L4 * (σ (k + 1) - σ k) ^ 3 / 24 :=
      midpoint_err hmk (fun x _ => hasDerivAt_G_s hd0 x)
        (fun x hx y hy => hB.gs_lip d hd x ⟨(hk0.1.trans hx.1), hx.2.trans hk1.2⟩ y
          ⟨(hk0.1.trans hy.1), hy.2.trans hk1.2⟩)
    have hsplit : g d (σ (k + 1)) = g d (σ k) + ∫ s in σ k..σ (k + 1), G d s := by
      unfold g
      rw [intervalIntegral.integral_add_adjacent_intervals ((continuous_G hd0).intervalIntegrable _ _)
        ((continuous_G hd0).intervalIntegrable _ _)]
    have hh : L4 * (σ (k + 1) - σ k) ^ 3 / 24 ≤ L4 * Sh ^ 2 * (σ (k + 1) - σ k) / 24 := by
      have h0 : 0 ≤ σ (k + 1) - σ k := by linarith
      have h1 := hP.step k (by omega)
      have h2 : (σ (k + 1) - σ k) ^ 2 ≤ Sh ^ 2 := pow_le_pow_left₀ h0 h1 2
      have : 0 ≤ L4 * (σ (k + 1) - σ k) := mul_nonneg hB.nonneg.2.2.2 h0
      nlinarith
    rw [midSum_succ, hsplit]
    have e : g d (σ k) + (∫ s in σ k..σ (k + 1), G d s) - (midSum (G d) σ k +
        (σ (k + 1) - σ k) * G d ((σ k + σ (k + 1)) / 2)) =
        (g d (σ k) - midSum (G d) σ k) + ((∫ s in σ k..σ (k + 1), G d s) -
        (σ (k + 1) - σ k) * G d ((σ k + σ (k + 1)) / 2)) := by ring
    rw [e]
    calc _ ≤ |g d (σ k) - midSum (G d) σ k| + |(∫ s in σ k..σ (k + 1), G d s) -
          (σ (k + 1) - σ k) * G d ((σ k + σ (k + 1)) / 2)| := abs_add_le _ _
      _ ≤ L4 * Sh ^ 2 * σ k / 24 + L4 * Sh ^ 2 * (σ (k + 1) - σ k) / 24 := add_le_add ih (hcell.trans hh)
      _ = _ := by ring

/-- The negative-part integrand `max 0 (-G(d, ·))` against its midpoint sum. -/
theorem DerivBounds.integral_max_sub_midSum (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d : ℝ}
    (hd : d ∈ Icc dLo dHi) {σ : ℕ → ℝ} {n : ℕ} {Sh : ℝ} (hP : Partition σ n xHi Sh) :
    ∀ k ≤ n, |(∫ s in (0 : ℝ)..σ k, max 0 (-G d s)) - midSum (fun s => max 0 (-G d s)) σ k| ≤
      L2 * Sh * σ k / 4 := by
  have hd0 : 0 < d := lt_of_lt_of_le hB.pos hd.1
  have hΦc : Continuous (fun s => max 0 (-G d s)) := by
    have := continuous_G hd0; fun_prop
  intro k
  induction k with
  | zero => intro _; simp [midSum, hP.zero]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hmk := hP.mono k (by omega)
    have hk0 := hP.mem_Icc (by omega : k ≤ n)
    have hk1 := hP.mem_Icc hk
    have hcell : |(∫ s in σ k..σ (k + 1), max 0 (-G d s)) -
        (σ (k + 1) - σ k) * max 0 (-G d ((σ k + σ (k + 1)) / 2))| ≤ L2 * (σ (k + 1) - σ k) ^ 2 / 4 :=
      midpoint_err_lip hmk hΦc.continuousOn (fun x hx y hy => by
        have := hB.G_lip_s hd x ⟨(hk0.1.trans hx.1), hx.2.trans hk1.2⟩ y ⟨(hk0.1.trans hy.1), hy.2.trans hk1.2⟩
        calc _ = |max (-G d x) 0 - max (-G d y) 0| := by rw [max_comm 0 (-G d x), max_comm 0 (-G d y)]
          _ ≤ |-G d x - -G d y| := abs_max_sub_max_le_abs _ _ _
          _ = |G d x - G d y| := by rw [← abs_neg]; congr 1; ring
          _ ≤ _ := this)
    have hh : L2 * (σ (k + 1) - σ k) ^ 2 / 4 ≤ L2 * Sh * (σ (k + 1) - σ k) / 4 := by
      have h0 : 0 ≤ σ (k + 1) - σ k := by linarith
      have h1 := hP.step k (by omega)
      have : 0 ≤ L2 * (σ (k + 1) - σ k) := mul_nonneg hB.nonneg.2.1 h0
      nlinarith
    have hsplit : (∫ s in (0 : ℝ)..σ (k + 1), max 0 (-G d s)) =
        (∫ s in (0 : ℝ)..σ k, max 0 (-G d s)) + ∫ s in σ k..σ (k + 1), max 0 (-G d s) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hΦc.intervalIntegrable _ _) (hΦc.intervalIntegrable _ _)]
    rw [midSum_succ, hsplit]
    have e : (∫ s in (0 : ℝ)..σ k, max 0 (-G d s)) + (∫ s in σ k..σ (k + 1), max 0 (-G d s)) -
        (midSum (fun s => max 0 (-G d s)) σ k + (σ (k + 1) - σ k) * max 0 (-G d ((σ k + σ (k + 1)) / 2))) =
        ((∫ s in (0 : ℝ)..σ k, max 0 (-G d s)) - midSum (fun s => max 0 (-G d s)) σ k) +
        ((∫ s in σ k..σ (k + 1), max 0 (-G d s)) -
          (σ (k + 1) - σ k) * max 0 (-G d ((σ k + σ (k + 1)) / 2))) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ L2 * Sh * σ k / 4 + L2 * Sh * (σ (k + 1) - σ k) / 4 := add_le_add ih (hcell.trans hh)
      _ = _ := by ring

/-- Values within `δ` of `F` at the midpoints change the midpoint sum by at most `δ σ_k`. -/
theorem abs_sum_sub_midSum {F : ℝ → ℝ} {σ : ℕ → ℝ} {n : ℕ} {Sh δ : ℝ} (hP : Partition σ n xHi Sh) {v : ℕ → ℝ}
    (hv : ∀ j < n, |v j - F ((σ j + σ (j + 1)) / 2)| ≤ δ) :
    ∀ k ≤ n, |(∑ j ∈ Finset.range k, (σ (j + 1) - σ j) * v j) - midSum F σ k| ≤ δ * σ k := by
  intro k
  induction k with
  | zero => intro _; simp [midSum, hP.zero]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hmk := hP.mono k (by omega)
    rw [Finset.sum_range_succ, midSum_succ]
    have e : (∑ j ∈ Finset.range k, (σ (j + 1) - σ j) * v j) + (σ (k + 1) - σ k) * v k -
        (midSum F σ k + (σ (k + 1) - σ k) * F ((σ k + σ (k + 1)) / 2)) =
        ((∑ j ∈ Finset.range k, (σ (j + 1) - σ j) * v j) - midSum F σ k) +
        (σ (k + 1) - σ k) * (v k - F ((σ k + σ (k + 1)) / 2)) := by ring
    rw [e]
    have h2 : |(σ (k + 1) - σ k) * (v k - F ((σ k + σ (k + 1)) / 2))| ≤ δ * (σ (k + 1) - σ k) := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      nlinarith [hv k (by omega), abs_nonneg (v k - F ((σ k + σ (k + 1)) / 2))]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ δ * σ k + δ * (σ (k + 1) - σ k) := add_le_add ih h2
      _ = _ := by ring

/-! ### Selecting a cell of a node sequence -/

theorem exists_cell_left {a : ℕ → ℝ} {J : ℕ} (hJ : 0 < J) {y : ℝ}
    (h0 : a 0 ≤ y) (hy : y ≤ a J) : ∃ j, j < J ∧ y ∈ Icc (a j) (a (j + 1)) := by
  classical
  have hex : ∃ i, i < J ∧ y ≤ a (i + 1) := ⟨J - 1, by omega, by rw [show J - 1 + 1 = J by omega]; exact hy⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; exact h0
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    have h2 : ¬ (Nat.find hex - 1 < J ∧ y ≤ a (Nat.find hex - 1 + 1)) := this
    have h3 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [h3] at h2
    have : Nat.find hex - 1 < J := by have := (Nat.find_spec hex).1; omega
    exact (not_le.1 fun h4 => h2 ⟨this, h4⟩).le

theorem exists_cell_right {a : ℕ → ℝ} {n J : ℕ} (hJ : J < n) {y : ℝ} (h0 : a J ≤ y) (hy : y ≤ a n) : ∃ j, J ≤ j ∧ j < n ∧ y ∈ Icc (a j) (a (j + 1)) := by
  classical
  set j := Nat.findGreatest (fun i => a i ≤ y) (n - 1) with hj
  have hJj : J ≤ j := Nat.le_findGreatest (by omega) h0
  have hjn : j ≤ n - 1 := Nat.findGreatest_le _
  have hsp : a j ≤ y := Nat.findGreatest_spec (P := fun i => a i ≤ y) (by omega : J ≤ n - 1) h0
  refine ⟨j, hJj, by omega, hsp, ?_⟩
  rcases Nat.lt_or_ge j (n - 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun i => a i ≤ y) (show j < j + 1 by omega) (by omega : j + 1 ≤ n - 1)
    exact (not_le.1 this).le
  · have : j + 1 = n := by omega
    rw [this]; exact hy

theorem exists_cell {a : ℕ → ℝ} {n : ℕ} (hn : 0 < n) {y : ℝ} (h0 : a 0 ≤ y)
    (hy : y ≤ a n) : ∃ j, j < n ∧ y ∈ Icc (a j) (a (j + 1)) := by
  obtain ⟨j, hj, h⟩ := exists_cell_left hn h0 hy
  exact ⟨j, hj, h⟩

end SandierSerfaty.Certificate.Box
