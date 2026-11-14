/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Depth

/-!
# Comparison of the counts with the density; separation of the rows (sphere note, Lemma 5.8 (G4)–(G5))

Rows are indexed from `0`; interior rows are `1 ≤ k`, `k + 1 < K`.

* `Sphere.ringDensity_le_mul_exp`: `ϱ(t) ≤ ϱ(s) e^{2|t - s|}` (`|(log ϱ)'| ≤ 2`);
* `Sphere.ringHeight_mem`: `A_k < Φ(t_k) < A_{k+1}`;
* `Sphere.ringDensity_interior`: on an interior slab, `ϱ ≤ 3 N_k²` and `N_k² ≤ 18 ϱ` (G5);
* `Sphere.ringDensity_height_le`: `ϱ(t_k) ≤ 3 N_k²` for every row, i.e. `x_k ≥ 1/3` (G5);
* `Sphere.ringHeight_sep`: for `k < l`, `t_l - t_k ≥ c₀/N_k + c₀/N_l` (`c₀ = 3/112`).
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

theorem cosh_le_cosh_mul_exp (s t : ℝ) : Real.cosh s ≤ Real.cosh t * Real.exp |s - t| := by
  rw [Real.cosh_eq, Real.cosh_eq]
  have h1 : Real.exp s ≤ Real.exp t * Real.exp |s - t| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [le_abs_self (s - t)])
  have h2 : Real.exp (-s) ≤ Real.exp (-t) * Real.exp |s - t| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [neg_abs_le (s - t)])
  nlinarith

/-- `ϱ(t) ≤ ϱ(s) e^{2|t - s|}`. -/
theorem ringDensity_le_mul_exp {n : ℝ} (hn : 0 ≤ n) (s t : ℝ) :
    ringDensity n t ≤ ringDensity n s * Real.exp (2 * |t - s|) := by
  have hs := Real.cosh_pos s
  have ht := Real.cosh_pos t
  have h := cosh_le_cosh_mul_exp s t
  rw [abs_sub_comm] at h
  have h2 : Real.cosh s ^ 2 ≤ Real.cosh t ^ 2 * Real.exp (2 * |t - s|) := by
    have : Real.exp (2 * |t - s|) = Real.exp |t - s| ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this, ← mul_pow]
    exact pow_le_pow_left₀ hs.le h 2
  rw [ringDensity, ringDensity, div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h2 hn]

theorem ringQuantile_le {n a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbn : b < n) :
    ringQuantile n a ≤ ringQuantile n b := by
  rcases hab.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (ringQuantile_lt ha h hbn).le

/-- `A_k < Φ(t_k) < A_{k+1}`. -/
theorem ringHeight_mem {n k : ℕ} (hk : k < ringK n) :
    ((ringState n k).1 : ℝ) < ringMass n (ringHeight n k) ∧
      ringMass n (ringHeight n k) < (ringState n (k + 1)).1 := by
  have hs := ringStep_spec_at hk
  have hle : (ringState n (k + 1)).1 ≤ n := by
    rcases ringState_fst_le n (k + 1) with h | h
    · exact h
    · have := ringState_lt_of_lt_ringK hk; omega
  have hn : (0 : ℝ) < n := by
    have := ringState_lt_of_lt_ringK hk; exact_mod_cast (show 0 < n by omega)
  rw [ringHeight_eq_slabBary hk]
  exact barycentre_mem_interior hn (Nat.cast_nonneg _)
    (by rw [hs.1]; push_cast; have := hs.2.1; exact_mod_cast (by omega : (ringState n k).1 <
      (ringState n k).1 + ringN n k)) (by exact_mod_cast hle)

/-- **(G5)**, interior rows: on the slab `I_k`, `ϱ ≤ 3 N_k²` and `N_k² ≤ 18 ϱ`. -/
theorem ringDensity_interior {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) {t : ℝ}
    (ht : t ∈ Icc (ringQuantile n (ringState n k).1) (ringQuantile n (ringState n (k + 1)).1)) :
    ringDensity n t ≤ 3 * (ringN n k : ℝ) ^ 2 ∧ (ringN n k : ℝ) ^ 2 ≤ 18 * ringDensity n t := by
  obtain ⟨hN3, hN6, h2, hb, ha0, hbn⟩ := ringInterior_facts hn hk1 hk
  obtain ⟨hlo, hhi⟩ := ringN_mem_Icc hn hk1 hk
  have hle : (ringState n k).1 ≤ n := by
    have := ringState_lt_of_lt_ringK (show k < ringK n by omega); omega
  have hsq := ringTarget_sq n (ringState n k).1 hle
  rw [hb] at hbn ht
  obtain ⟨hρ1, hρ2⟩ := ringDensity_mem_slab ha0 (by linarith) hbn ht
  have hc := two_sqrt_three_pi_lt
  have hc' := two_sqrt_three_pi_gt
  have hx0 := ringTarget_nonneg n (ringState n k).1
  set a := ((ringState n k).1 : ℝ)
  set N := (ringN n k : ℝ)
  set x := ringTarget n (ringState n k).1
  set ρ := ringDensity n t
  have hn' : (0 : ℝ) < n := by linarith
  set c := 2 * Real.sqrt 3 * Real.pi
  -- `x² = c a (n - a) / n`
  have hxa : x ^ 2 * n = c * a * (n - a) := by rw [hsq]; field_simp
  have hρ0 : 0 ≤ ρ := (ringDensity_pos hn' t).le
  have hc0 : 0 ≤ c := by linarith
  have hρ1' : a * (n - a) ≤ n * ρ := by
    have : 2 / n * a * (n - (a + N)) * n = 2 * a * (n - (a + N)) := by field_simp
    linarith [mul_le_mul_of_nonneg_right hρ1 hn'.le,
      mul_nonneg ha0.le (by linarith : (0 : ℝ) ≤ n - a - 2 * N)]
  have hρ2' : n * ρ ≤ 14 * a * (n - a) := by
    have : 2 / n * (a + N) * (n - a) * n = 2 * (a + N) * (n - a) := by field_simp
    linarith [mul_le_mul_of_nonneg_right hρ2 hn'.le,
      mul_le_mul_of_nonneg_left hN6 (by linarith : (0 : ℝ) ≤ n - a)]
  constructor
  · -- `n ρ ≤ 14 a (n - a) = 14 x² n / c ≤ 14 (16/9) N² n / c ≤ 3 N² n`
    have hx2 : x ^ 2 ≤ 16 / 9 * N ^ 2 := by
      have := pow_le_pow_left₀ hx0 (show x ≤ 4 / 3 * N by linarith) 2; linarith
    have : c * (n * ρ) ≤ 14 * (x ^ 2 * n) := by
      rw [hxa]; linarith [mul_le_mul_of_nonneg_left hρ2' hc0]
    have : c * ρ ≤ 14 * x ^ 2 :=
      le_of_mul_le_mul_right (by linarith : c * ρ * n ≤ 14 * x ^ 2 * n) hn'
    linarith [mul_le_mul_of_nonneg_right hc'.le hρ0, sq_nonneg N]
  · have hx2 : N ^ 2 ≤ 25 / 16 * x ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ N) hhi 2; linarith
    have : x ^ 2 * n ≤ c * (n * ρ) := by
      rw [hxa]; linarith [mul_le_mul_of_nonneg_left hρ1' hc0]
    have : x ^ 2 ≤ c * ρ :=
      le_of_mul_le_mul_right (by linarith : x ^ 2 * n ≤ c * ρ * n) hn'
    linarith [mul_le_mul_of_nonneg_right hc.le hρ0]

theorem ringState_cast_le {n k l : ℕ} (h : k ≤ l) :
    ((ringState n k).1 : ℝ) ≤ (ringState n l).1 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by exact_mod_cast ringState_mono n _)

/-- **(G5)** for every row: `ϱ(t_k) ≤ 3 N_k²`, i.e. `x_k ≥ 1/3`. -/
theorem ringDensity_height_le {n k : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) :
    ringDensity n (ringHeight n k) ≤ 3 * (ringN n k : ℝ) ^ 2 := by
  have hN3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN (by omega) k hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hm1, hm2⟩ := ringHeight_mem hk
  have hs := ringStep_spec_at hk
  have hΦ0 := ringMass_pos hn' (ringHeight n k)
  have hΦn := ringMass_lt hn' (ringHeight n k)
  rw [ringDensity_eq_mass hn'.ne']
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the south polar row: `ϱ ≤ 2 Φ ≤ 2 N_0`
    have h0 : ((ringState n 1).1 : ℝ) = ringN n 0 := by rw [hs.1]; simp [ringState]
    rw [h0] at hm2
    have : 2 / (n : ℝ) * ringMass n (ringHeight n 0) * (n - ringMass n (ringHeight n 0)) ≤
        2 * ringMass n (ringHeight n 0) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hn']; nlinarith
    nlinarith
  rcases lt_or_eq_of_le (show k + 1 ≤ ringK n by omega) with hk' | hk'
  · have hmem : ringHeight n k ∈ Icc (ringQuantile n (ringState n k).1)
        (ringQuantile n (ringState n (k + 1)).1) := by
      obtain ⟨-, -, -, hb, ha0, hbn⟩ := ringInterior_facts (by omega) hk1 hk'
      have hab : ((ringState n k).1 : ℝ) ≤ (ringState n (k + 1)).1 := ringState_cast_le (by omega)
      constructor
      · exact (le_ringMass_iff ha0 (by linarith) _).1 hm1.le
      · exact (ringMass_le_iff (by linarith) hbn _).1 hm2.le
    have := (ringDensity_interior (by omega) hk1 hk' hmem).1
    rwa [ringDensity_eq_mass hn'.ne'] at this
  · -- the north polar row: `ϱ ≤ 2 (n - Φ) ≤ 2 N_{K-1}`
    have hfin : (ringState n (k + 1)).1 = n := by rw [hk']; exact ringState_ringK n
    have e : ((ringState n (k + 1)).1 : ℝ) = (ringState n k).1 + ringN n k := by
      rw [hs.1]; push_cast; ring
    rw [hfin] at e
    have : 2 / (n : ℝ) * ringMass n (ringHeight n k) * (n - ringMass n (ringHeight n k)) ≤
        2 * (n - ringMass n (ringHeight n k)) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hn']; nlinarith
    nlinarith

theorem two_le_ringK {n : ℕ} (hn : 10 ≤ n) : 2 ≤ ringK n := by
  by_contra h
  push Not at h
  have h0 : 0 < ringK n := by
    by_contra h'
    push Not at h'
    have hK0 : ringK n = 0 := by omega
    have h' := le_ringState_ringK n
    rw [hK0] at h'
    simp [ringState] at h'
    omega
  have hK1 : ringK n = 1 := by omega
  have hfin : (ringState n 1).1 = n := by rw [← hK1]; exact ringState_ringK n
  have hst : ringState n 1 = ringStep n (0, 0, 0) := rfl
  have hround : ringRound n 0 = 3 := by
    have : ⌊ringTarget n 0 + 1 / 2⌋₊ = 0 := Nat.floor_eq_zero.2 (by norm_num [ringTarget])
    unfold ringRound; rw [this]; rfl
  have h1 : ¬ n ≤ 0 := by omega
  have h9 : ¬ n - 0 ≤ 2 * ringRound n 0 + 3 := by rw [hround]; omega
  rw [hst] at hfin
  unfold ringStep at hfin
  rw [ite_eq_right h1, ite_eq_right h9] at hfin
  split_ifs at hfin with hC
  · simp at hC
  · simp at hfin; omega

/-! ### Separation -/

theorem ringState_pos {n k : ℕ} (_hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k ≤ ringK n) :
    (0 : ℝ) < (ringState n k).1 := by
  have h1 : (0 : ℝ) < (ringState n 1).1 := by
    have hs := ringStep_spec_at (n := n) (k := 0) (by omega)
    have := hs.2.1
    rw [hs.1]; simp [ringState]; exact_mod_cast this
  exact h1.trans_le (ringState_cast_le hk1)

/-- **Separation**: for `k < l`, `t_k + c₀/N_k + c₀/N_l ≤ t_l` (`c₀ = 3/112`). -/
theorem ringHeight_sep {n k l : ℕ} (hn : 102 ≤ n) (hkl : k < l) (hl : l < ringK n) :
    ringHeight n k + 3 / (112 * ringN n k) + 3 / (112 * ringN n l) ≤ ringHeight n l := by
  have h1 := ringHeight_depth_right hn (show k + 1 < ringK n by omega)
  have h2 := ringHeight_depth_left hn (show 1 ≤ l by omega) hl
  have h3 : ringQuantile n (ringState n (k + 1)).1 ≤ ringQuantile n (ringState n l).1 :=
    ringQuantile_le (ringState_pos (by omega) (by omega) (by omega)) (ringState_cast_le hkl)
      (by exact_mod_cast ringState_lt_of_lt_ringK hl)
  linarith

end Sphere

end SandierSerfaty

end
