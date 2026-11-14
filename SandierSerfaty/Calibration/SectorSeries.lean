/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.SectorH
public import SandierSerfaty.Calibration.BdCalc

/-!
# `f₀ ∈ C²((0, ∞))` and `e ∈ C¹((0, ∞))`

paper `cal:f0-e`; the paper uses without proof the regularity (`C¹` of `f₀` and `e`, differentiation of
the series termwise). On `U = (d, T)`, `0 < d`, with `M` the majorant of `exists_D_majorant`
(`|D_i|, |D_i'|, |D_i''| ≤ M_i`, `∑ k_i^a M_i < ∞` for all `a`) and `A` of `exists_H_bound`:

* `∑' D_i/(k_i+2)`: terms `C²` with bounds `M_i`;
* `∑' (-2 D_i + 2 k_i D_i H_{k_i})`: terms `C²` with bounds `(2 + 8A)(1+k_i)³ M_i` (`bd2_F2_term`);
* `∑' k_i k_j/(k_i+k_j) D_i D_j` over `ℕ × ℕ`: terms `C²` with bounds `4 (k_iM_i)(k_jM_j)`;
* `∑' Q_i Q_j/(k_i+k_j)`: terms `C¹` with bounds `2 W_i W_j`, `W_i = (1 + T + k_i) M_i`.

`tsum_bd2`/`tsum_bd1` (termwise differentiation on `(d, T)`, `hasDerivAt_tsum_of_isPreconnected`) give the series
`C²` / `C¹`; the integral parts `S₁, S₂` are `C²` (`SectorInt.lean`). `contDiffOn_f₀`, `contDiffOn_e` follow locally
(`(d, T) = (x/2, 2x)`). Only `e''` may jump (at the spline knots, where the spline data have only one-sided third derivatives;
paper, end of `comp:radial-table`).
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

theorem tsum_bd2 {ι : Type*} {U : Set ℝ} (hU : IsOpen U) (hc : IsPreconnected U) {g : ι → ℝ → ℝ}
    {c₀ c₁ c₂ : ι → ℝ} (h₀ : Summable c₀) (h₁ : Summable c₁) (h₂ : Summable c₂)
    (hg : ∀ i, Bd2 U (g i) (c₀ i) (c₁ i) (c₂ i)) : ContDiffOn ℝ 2 (fun x => ∑' i, g i x) U :=
  (tsum_contDiffOn_two hU hc h₀ h₁ h₂ (fun i => (hg i).1) (fun i x hx => ((hg i).2 x hx).1)
    (fun i x hx => ((hg i).2 x hx).2.1) (fun i x hx => ((hg i).2 x hx).2.2)).1

theorem tsum_bd1 {ι : Type*} {U : Set ℝ} (hU : IsOpen U) (hc : IsPreconnected U) {g : ι → ℝ → ℝ}
    {c₀ c₁ : ι → ℝ} (h₀ : Summable c₀) (h₁ : Summable c₁)
    (hg : ∀ i, Bd1 U (g i) (c₀ i) (c₁ i)) : ContDiffOn ℝ 1 (fun x => ∑' i, g i x) U :=
  (tsum_contDiffOn_one hU hc h₀ h₁ (fun i => (hg i).1) (fun i x hx => ((hg i).2 x hx).1)
    (fun i x hx => ((hg i).2 x hx).2)).1

/-- `∑ (1 + k_i)^n M_i < ∞` from the polynomial-weighted summability. -/
theorem summable_one_add_pow_mul {M : ℕ → ℝ}
    (h : ∀ a : ℕ, Summable fun i => ((k i : ℕ) : ℝ) ^ a * M i) (n : ℕ) :
    Summable fun i => (1 + (k i : ℝ)) ^ n * M i := by
  have e : ∀ i, (1 + (k i : ℝ)) ^ n * M i =
      ∑ m ∈ Finset.range (n + 1), ((k i : ℝ) ^ m * M i) * (n.choose m : ℝ) := by
    intro i
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [one_pow, mul_one]
    ring
  simp_rw [e]
  exact summable_sum fun m _ => (h m).mul_right _

theorem F2_poly {m A K p : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ A) (hK : 0 ≤ K) (hp : p ≤ m * A * (2 + K) ^ 2) :
    2 * m + 2 * K * p ≤ (2 + 8 * A) * ((1 + K) ^ 3 * m) := by
  have h1 : K * (2 + K) ^ 2 ≤ 4 * (1 + K) ^ 3 := by
    have : 0 ≤ 4 + 8 * K + 8 * K ^ 2 + 3 * K ^ 3 := by positivity
    nlinarith
  have h2 : 1 ≤ (1 + K) ^ 3 := one_le_pow₀ (by linarith)
  have h3 : 2 * K * p ≤ 2 * K * (m * A * (2 + K) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have h4 : 2 * K * (m * A * (2 + K) ^ 2) = 2 * (m * A) * (K * (2 + K) ^ 2) := by ring
  have h5 : 2 * (m * A) * (K * (2 + K) ^ 2) ≤ 2 * (m * A) * (4 * (1 + K) ^ 3) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h6 : 2 * m ≤ 2 * ((1 + K) ^ 3 * m) := by nlinarith
  nlinarith [mul_nonneg hA hm, pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + K) 3]

/-! ### The data on `U = (d, T)` -/

section Data

variable {d T : ℝ} {M : ℕ → ℝ}

theorem Ioo_subset_Ioi' (hd : 0 < d) : Ioo d T ⊆ Ioi 0 := fun _ hx => lt_trans hd hx.1

theorem bd2_D (hd : 0 < d) (hMb : ∀ i, ∀ t, d ≤ t →
    |D i t| ≤ M i ∧ |deriv (D i) t| ≤ M i ∧ |deriv (deriv (D i)) t| ≤ M i) (i : ℕ) :
    Bd2 (Ioo d T) (D i) (M i) (M i) (M i) :=
  ⟨(contDiffOn_D i).mono (Ioo_subset_Ioi' hd), fun x hx => hMb i x hx.1.le⟩

theorem bd2_H (hd : 0 < d) {A : ℝ}
    (hA : ∀ n : ℕ, ∀ t ∈ Icc d T, |H n t| ≤ A ∧ |deriv (H n) t| ≤ A * (1 + n) ∧
      |deriv (deriv (H n)) t| ≤ A * (1 + n) ^ 2) (n : ℕ) :
    Bd2 (Ioo d T) (H n) A (A * (1 + n)) (A * (1 + n) ^ 2) :=
  ⟨(contDiffOn_H n).mono (Ioo_subset_Ioi' hd), fun x hx => hA n x ⟨hx.1.le, hx.2.le⟩⟩

theorem bd2_F1_term (hd : 0 < d) (hM0 : ∀ i, 0 ≤ M i)
    (hMb : ∀ i, ∀ t, d ≤ t → |D i t| ≤ M i ∧ |deriv (D i) t| ≤ M i ∧ |deriv (deriv (D i)) t| ≤ M i)
    (i : ℕ) : Bd2 (Ioo d T) (fun t => D i t / ((k i : ℝ) + 2)) (M i) (M i) (M i) := by
  have h := (bd2_D (T := T) hd hMb i).const_mul (1 / ((k i : ℝ) + 2))
  have hk : 0 < (k i : ℝ) + 2 := by positivity
  have hc : |1 / ((k i : ℝ) + 2)| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hk]
    have : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
    linarith
  refine (h.mono ?_ ?_ ?_).congr isOpen_Ioo (fun x _ => by ring)
  · simpa using mul_le_mul_of_nonneg_right hc (hM0 i)
  · simpa using mul_le_mul_of_nonneg_right hc (hM0 i)
  · simpa using mul_le_mul_of_nonneg_right hc (hM0 i)

theorem bd2_F2_term (hd : 0 < d) {A : ℝ} (hA0 : 0 ≤ A) (hM0 : ∀ i, 0 ≤ M i)
    (hMb : ∀ i, ∀ t, d ≤ t → |D i t| ≤ M i ∧ |deriv (D i) t| ≤ M i ∧ |deriv (deriv (D i)) t| ≤ M i)
    (hA : ∀ n : ℕ, ∀ t ∈ Icc d T, |H n t| ≤ A ∧ |deriv (H n) t| ≤ A * (1 + n) ∧
      |deriv (deriv (H n)) t| ≤ A * (1 + n) ^ 2) (i : ℕ) :
    Bd2 (Ioo d T) (fun t => -2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t)
      ((2 + 8 * A) * ((1 + (k i : ℝ)) ^ 3 * M i)) ((2 + 8 * A) * ((1 + (k i : ℝ)) ^ 3 * M i))
      ((2 + 8 * A) * ((1 + (k i : ℝ)) ^ 3 * M i)) := by
  have hm := hM0 i
  have hK : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
  have b1 := (bd2_D (T := T) hd hMb i).const_mul (-2)
  have b2 := (((bd2_D (T := T) hd hMb i).mul isOpen_Ioo (bd2_H hd hA (k i))).const_mul
    (2 * (k i : ℝ)))
  have b3 := b1.add isOpen_Ioo b2
  have habs : |(2 : ℝ) * (k i : ℝ)| = 2 * k i := abs_of_nonneg (by positivity)
  have habs2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [habs, habs2] at b3
  refine (b3.mono ?_ ?_ ?_).congr isOpen_Ioo (fun x _ => by ring)
  · exact F2_poly hm hA0 hK (by nlinarith [mul_nonneg hm hA0, mul_nonneg (mul_nonneg hm hA0) hK])
  · exact F2_poly hm hA0 hK (by nlinarith [mul_nonneg hm hA0, mul_nonneg (mul_nonneg hm hA0) hK])
  · exact F2_poly hm hA0 hK (by nlinarith [mul_nonneg hm hA0, mul_nonneg (mul_nonneg hm hA0) hK])

theorem bd2_F3_term (hd : 0 < d) (hM0 : ∀ i, 0 ≤ M i)
    (hMb : ∀ i, ∀ t, d ≤ t → |D i t| ≤ M i ∧ |deriv (D i) t| ≤ M i ∧ |deriv (deriv (D i)) t| ≤ M i)
    (ij : ℕ × ℕ) :
    Bd2 (Ioo d T)
      (fun t => (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) * D ij.1 t * D ij.2 t)
      (4 * ((k ij.1 : ℝ) * M ij.1 * ((k ij.2 : ℝ) * M ij.2)))
      (4 * ((k ij.1 : ℝ) * M ij.1 * ((k ij.2 : ℝ) * M ij.2)))
      (4 * ((k ij.1 : ℝ) * M ij.1 * ((k ij.2 : ℝ) * M ij.2))) := by
  obtain ⟨i, j⟩ := ij
  simp only
  have hKi : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
  have hKj : (0 : ℝ) ≤ k j := Nat.cast_nonneg _
  have h6 : (6 : ℝ) ≤ k i := by exact_mod_cast six_le_k i
  set w : ℝ := (k i : ℝ) * (k j : ℝ) / ((k i : ℝ) + (k j : ℝ)) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ (k i : ℝ) * (k j : ℝ) := by
    rw [hw, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hKi hKj]
  have hX : 0 ≤ M i * M j := mul_nonneg (hM0 i) (hM0 j)
  have h := (((bd2_D (T := T) hd hMb i).mul isOpen_Ioo (bd2_D (T := T) hd hMb j)).const_mul w)
  rw [abs_of_nonneg hw0] at h
  have hwX := mul_le_mul_of_nonneg_right hw1 hX
  have hP := mul_nonneg (mul_nonneg hKi hKj) hX
  refine (h.mono ?_ ?_ ?_).congr isOpen_Ioo (fun x _ => by simp only [hw]; ring)
  · nlinarith
  · nlinarith
  · nlinarith

theorem bd1_Q (hd : 0 < d) (hM0 : ∀ i, 0 ≤ M i)
    (hMb : ∀ i, ∀ t, d ≤ t → |D i t| ≤ M i ∧ |deriv (D i) t| ≤ M i ∧ |deriv (deriv (D i)) t| ≤ M i)
    (i : ℕ) : Bd1 (Ioo d T) (Q i) ((1 + T + (k i : ℝ)) * M i) ((1 + T + (k i : ℝ)) * M i) := by
  have hm := hM0 i
  have hK : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
  have hT : ∀ x ∈ Ioo d T, |x| ≤ T := fun x hx => by
    rw [abs_of_pos (lt_trans hd hx.1)]; exact hx.2.le
  have b1 := (Bd1.id hT).mul isOpen_Ioo ((bd2_D (T := T) hd hMb i).derivBd isOpen_Ioo)
  have b2 := ((bd2_D (T := T) hd hMb i).to_Bd1).const_mul (-(k i : ℝ))
  have b3 := b1.add isOpen_Ioo b2
  rw [abs_neg, abs_of_nonneg hK] at b3
  refine (b3.mono ?_ ?_).congr isOpen_Ioo (fun x _ => by unfold Q; ring)
  · nlinarith
  · nlinarith


end Data

/-! ### The theorems -/

theorem summable_k_mul {M : ℕ → ℝ} (hMs : ∀ a : ℕ, Summable fun i => ((k i : ℕ) : ℝ) ^ a * M i) :
    Summable fun i => (k i : ℝ) * M i := by simpa using hMs 1

theorem summable_W {M : ℕ → ℝ} (hMs : ∀ a : ℕ, Summable fun i => ((k i : ℕ) : ℝ) ^ a * M i)
    (T : ℝ) : Summable fun i => (1 + T + (k i : ℝ)) * M i := by
  have h0 : Summable M := by simpa using hMs 0
  refine ((h0.mul_left (1 + T)).add (summable_k_mul hMs)).congr fun i => ?_
  ring

/-- **`f₀ ∈ C²((0, ∞))`** (`cal:f0-e`; the paper uses this without proof). -/
theorem contDiffOn_f₀ : ContDiffOn ℝ 2 f₀ (Ioi 0) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ⟨Ioo (x / 2) (2 * x), isOpen_Ioo,
    ⟨by simp only [mem_Ioi] at hx; linarith, by simp only [mem_Ioi] at hx; linarith⟩, ?_⟩
  have hx' : 0 < x := hx
  have hd : 0 < x / 2 := by positivity
  obtain ⟨M, hM0, hMs, hMb⟩ := exists_D_majorant hd
  obtain ⟨A, hA0, hA⟩ := exists_H_bound (d := x / 2) (T := 2 * x) hd
  have hsub : Ioo (x / 2) (2 * x) ⊆ Ioi 0 := Ioo_subset_Ioi' hd
  have h0 : Summable M := by simpa using hMs 0
  have hF1 : ContDiffOn ℝ 2 (fun t => ∑' i, D i t / ((k i : ℝ) + 2)) (Ioo (x / 2) (2 * x)) :=
    tsum_bd2 isOpen_Ioo isPreconnected_Ioo h0 h0 h0 (bd2_F1_term hd hM0 hMb)
  have hs3 := (summable_one_add_pow_mul hMs 3).mul_left (2 + 8 * A)
  have hF2 : ContDiffOn ℝ 2
      (fun t => ∑' i, (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t)) (Ioo (x / 2) (2 * x)) :=
    tsum_bd2 isOpen_Ioo isPreconnected_Ioo hs3 hs3 hs3 (bd2_F2_term hd hA0 hM0 hMb hA)
  have hs4 := ((summable_k_mul hMs).mul_of_nonneg (summable_k_mul hMs)
    (fun i => mul_nonneg (Nat.cast_nonneg _) (hM0 i)) (fun i => mul_nonneg (Nat.cast_nonneg _) (hM0 i))
    ).mul_left 4
  have hF3 : ContDiffOn ℝ 2
      (fun t => ∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ)) *
        D ij.1 t * D ij.2 t) (Ioo (x / 2) (2 * x)) :=
    tsum_bd2 isOpen_Ioo isPreconnected_Ioo (c₀ := fun ij => 4 * ((k ij.1 : ℝ) * M ij.1 *
      ((k ij.2 : ℝ) * M ij.2))) (c₁ := fun ij => 4 * ((k ij.1 : ℝ) * M ij.1 *
      ((k ij.2 : ℝ) * M ij.2))) (c₂ := fun ij => 4 * ((k ij.1 : ℝ) * M ij.1 *
      ((k ij.2 : ℝ) * M ij.2))) hs4 hs4 hs4 (bd2_F3_term hd hM0 hMb)
  have hS₁ : ContDiffOn ℝ 2 S₁ (Ioo (x / 2) (2 * x)) := contDiffOn_S₁.mono hsub
  have hS₂ : ContDiffOn ℝ 2 S₂ (Ioo (x / 2) (2 * x)) := contDiffOn_S₂.mono hsub
  have hlog : ContDiffOn ℝ 2 Real.log (Ioo (x / 2) (2 * x)) :=
    Real.contDiffOn_log.mono fun t ht => ne_of_gt (hsub ht)
  have hall : ContDiffOn ℝ 2 f₀ (Ioo (x / 2) (2 * x)) := by
    unfold f₀
    exact (contDiffOn_const.mul (hS₁.add ((contDiffOn_id.pow 2).mul hF1))).sub
      (contDiffOn_const.mul (((hlog.add hS₂).add hF2).add hF3))
  exact hall.mono inter_subset_right

/-- **`e ∈ C¹((0, ∞))`** (`cal:f0-e`; the paper uses this without proof). -/
theorem contDiffOn_e : ContDiffOn ℝ 1 e (Ioi 0) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ⟨Ioo (x / 2) (2 * x), isOpen_Ioo,
    ⟨by simp only [mem_Ioi] at hx; linarith, by simp only [mem_Ioi] at hx; linarith⟩, ?_⟩
  have hx' : 0 < x := hx
  have hd : 0 < x / 2 := by positivity
  obtain ⟨M, hM0, hMs, hMb⟩ := exists_D_majorant hd
  have hW := summable_W hMs (2 * x)
  have hs : Summable fun ij : ℕ × ℕ => 2 * ((1 + 2 * x + (k ij.1 : ℝ)) * M ij.1 *
      ((1 + 2 * x + (k ij.2 : ℝ)) * M ij.2)) :=
    (hW.mul_of_nonneg hW (fun i => by have := hM0 i; positivity)
      (fun i => by have := hM0 i; positivity)).mul_left 2
  have hF : ContDiffOn ℝ 1 (fun t => ∑' ij : ℕ × ℕ, Q ij.1 t * Q ij.2 t /
      ((k ij.1 : ℝ) + (k ij.2 : ℝ))) (Ioo (x / 2) (2 * x)) := by
    refine tsum_bd1 isOpen_Ioo isPreconnected_Ioo (c₀ := fun ij => 2 * ((1 + 2 * x + (k ij.1 : ℝ)) *
      M ij.1 * ((1 + 2 * x + (k ij.2 : ℝ)) * M ij.2))) (c₁ := fun ij => 2 * ((1 + 2 * x + (k ij.1 : ℝ)) *
      M ij.1 * ((1 + 2 * x + (k ij.2 : ℝ)) * M ij.2))) hs hs fun ij => ?_
    obtain ⟨i, j⟩ := ij
    simp only
    have hKi : (0 : ℝ) ≤ k i := Nat.cast_nonneg _
    have hKj : (0 : ℝ) ≤ k j := Nat.cast_nonneg _
    have h6 : (6 : ℝ) ≤ k i := by exact_mod_cast six_le_k i
    have hq := bd1_Q (T := 2 * x) hd hM0 hMb i
    have hq' := bd1_Q (T := 2 * x) hd hM0 hMb j
    have h := ((hq.mul isOpen_Ioo hq').const_mul (1 / ((k i : ℝ) + (k j : ℝ))))
    have hk : 0 < (k i : ℝ) + (k j : ℝ) := by linarith
    have hc : |1 / ((k i : ℝ) + (k j : ℝ))| ≤ 1 := by
      rw [abs_of_pos (by positivity), div_le_one hk]; linarith
    have hWi : 0 ≤ (1 + 2 * x + (k i : ℝ)) * M i := by have := hM0 i; positivity
    have hWj : 0 ≤ (1 + 2 * x + (k j : ℝ)) * M j := by have := hM0 j; positivity
    have hP : 0 ≤ (1 + 2 * x + (k i : ℝ)) * M i * ((1 + 2 * x + (k j : ℝ)) * M j) :=
      mul_nonneg hWi hWj
    refine (h.mono ?_ ?_).congr isOpen_Ioo (fun t _ => by ring)
    · nlinarith [mul_le_mul_of_nonneg_right hc hP]
    · nlinarith [mul_le_mul_of_nonneg_right hc hP]
  have hall : ContDiffOn ℝ 1 e (Ioo (x / 2) (2 * x)) := by
    unfold e
    exact contDiffOn_const.mul hF
  exact hall.mono inter_subset_right


end Calibration

end SandierSerfaty

end
