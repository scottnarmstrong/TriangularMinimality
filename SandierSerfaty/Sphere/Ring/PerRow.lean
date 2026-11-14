/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Polar
public import SandierSerfaty.Sphere.Ring.RowSum

/-!
# Per-row bounds, crude form (sphere note, Proposition 5.12 (i))

* `Sphere.ringRows_sum_X_le`: `∑_{l ≠ k} X_{kl} ≤ C_X N_k` (Lemmas 5.2 (iii) and 5.10 with `u₀ = 0`);
* `Sphere.ringRows_neg_log_aspect_le`: `-(N_k/2) log x_k ≤ (N_k/2) log 3` (G5);
* `Sphere.ringRows_rowB_le`: **Proposition 5.12 (i)**: there is an absolute `C` with `B_k ≤ C N_k` for
  every row of `Y_n`, `n ≥ 102`.
-/

open Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `X_{kl} ≤ min(N_k, N_l) Θ(max(N_k, N_l) |t_k - t_l|)` for distinct rows of `Y_n`. -/
theorem ringRows_X_le {n k l : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hl : l < ringK n) (hkl : k ≠ l) :
    (ringRows n).X k l ≤ ((min (ringN n k) (ringN n l) : ℕ) : ℝ) *
      ringTheta (((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l|) := by
  have hne : ringHeight n k ≠ ringHeight n l := by
    have h0 : ∀ m < ringK n, (0 : ℝ) < 3 / (112 * (ringN n m : ℝ)) := fun m hm => by
      have : (3 : ℝ) ≤ ringN n m := by exact_mod_cast three_le_ringN (by omega) m hm
      positivity
    have := h0 k hk
    have := h0 l hl
    rcases lt_or_gt_of_ne hkl with h | h
    · have := ringHeight_sep hn h hl; intro he; linarith
    · have := ringHeight_sep hn h hk; intro he; linarith
  exact (le_abs_self _).trans ((ringRows n).abs_X_le k l (ringRows_N_pos hk) (ringRows_N_pos hl) hne)

/-- `∑_{l ≠ k} X_{kl} ≤ C_X N_k` (Lemma 5.10 with `u₀ = 0`). -/
theorem ringRows_sum_X_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n → ∀ k < ringK n,
    ∑ l ∈ (range (ringK n)).erase k, (ringRows n).X k l ≤ C * ringN n k := by
  obtain ⟨C, hC, h⟩ := ringRowSum_le
  refine ⟨C, hC, fun n hn k hk => ?_⟩
  have h0 := h n hn k hk 0 le_rfl
  rw [mul_zero, zero_div, neg_zero, Real.exp_zero, mul_one,
    filter_true_of_mem (fun l _ => abs_nonneg _)] at h0
  refine le_trans (sum_le_sum fun l hl => ?_) h0
  obtain ⟨hlk, hlK⟩ := mem_erase.1 hl
  exact ringRows_X_le hn hk (mem_range.1 hlK) (Ne.symm hlk)

/-- `-(N_k/2) log x_k ≤ (N_k/2) log 3` (`x_k ≥ 1/3`, G5). -/
theorem ringRows_neg_log_aspect_le {n k : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) :
    -((ringN n k : ℝ) / 2 * Real.log ((ringRows n).aspect k)) ≤ (ringN n k : ℝ) / 2 * Real.log 3 := by
  have hN3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN (by omega) k hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hasp : (ringRows n).aspect k = (ringN n k : ℝ) ^ 2 / ringDensity n (ringHeight n k) := by
    rw [RowConfig.aspect, ringRows_card]; rfl
  have hρ := ringDensity_height_le hn hk
  have hρ0 := ringDensity_pos hn' (ringHeight n k)
  have hx : 1 / 3 ≤ (ringRows n).aspect k := by
    rw [hasp, le_div_iff₀ hρ0]; nlinarith
  have hlog : -Real.log 3 ≤ Real.log ((ringRows n).aspect k) := by
    rw [← Real.log_inv, show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
    exact Real.log_le_log (by norm_num) hx
  have : 0 ≤ (ringN n k : ℝ) / 2 := by positivity
  nlinarith

/-- **Proposition 5.12 (i).** There is an absolute `C` such that `B_k ≤ C N_k` for every row `k` of
`Y_n`, `n ≥ 102`. -/
theorem ringRows_rowB_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n → ∀ k < ringK n,
    (ringRows n).rowB k ≤ C * ringN n k := by
  obtain ⟨CX, hCX, hX⟩ := ringRows_sum_X_le
  refine ⟨Real.log 3 / 2 + 153 + CX, by positivity, fun n hn k hk => ?_⟩
  have hN0 : (0 : ℝ) ≤ ringN n k := Nat.cast_nonneg _
  have hcell : (ringRows n).cell k ≤ 153 * (ringN n k : ℝ) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact ringCell_polar_le hn (Or.inl rfl)
    rcases lt_or_eq_of_le (show k + 1 ≤ ringK n by omega) with hk' | hk'
    · have := ringCell_le (by omega) hk1 hk'
      linarith
    · exact ringCell_polar_le hn (Or.inr (by omega))
  have h1 := ringRows_neg_log_aspect_le hn hk
  have h3 := hX n hn k hk
  unfold RowConfig.rowB
  have e : (ringRows n).N k = ringN n k := rfl
  have e2 : (ringRows n).K = ringK n := rfl
  rw [e, e2]
  nlinarith

end Sphere

end SandierSerfaty

end
