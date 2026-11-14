/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Cell
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bands and the bulk aspect (sphere note Construction 5.7, Lemma 5.8 (G5))

* `Sphere.RingBulk n k`: step `k` is bulk, `N*(A_k) ≥ N_cap`; `Sphere.RingCRow n j`: row `j` is made
  by rule (C) (a non-final step continuing the band of row `j - 1`);
* `Sphere.ringBulk_interior`: bulk rows are interior; `Sphere.ringCRow_N`, `Sphere.ringCRow_J`,
  `Sphere.ringCRow_bulk`: a (C)-row repeats the count of the previous row, increments its band index,
  and both rows are bulk; `Sphere.ringBand_N`, `Sphere.ringBand_J`: along a band;
* `Sphere.slabBary_bounds_exp`: on a bounded slab, `(N/(2ρ)) e^{-6L} ≤ t - α, β - t ≤ (N/(2ρ)) e^{6L}`
  (`ρ = ϱ(t)` at the barycentre `t`);
* `Sphere.ringAspect_sub_le`: **(G5), bulk rows**: `|x_k - √3π| ≤ C_a (T + 1)/N_k`.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

/-- Step `k` of Construction 5.7 is **bulk**: `N*(A_k) ≥ N_cap`. -/
@[expose] def RingBulk (n k : ℕ) : Prop := (ringCap n : ℝ) ≤ ringTarget n (ringState n k).1

/-- Row `j` is made by rule (C): a non-final step `j ≥ 1` satisfying the continuation condition. -/
@[expose] def RingCRow (n j : ℕ) : Prop := 1 ≤ j ∧ j + 1 < ringK n ∧ RingCont n (ringState n j)

theorem forty_le_ringCap (n : ℕ) : (40 : ℝ) ≤ ringCap n := by
  have : 40 ≤ ringCap n := le_max_left _ _
  exact_mod_cast this

/-- Bulk rows are interior rows. -/
theorem ringBulk_interior {n k : ℕ} (hk : k < ringK n) (hb : RingBulk n k) :
    1 ≤ k ∧ k + 1 < ringK n := by
  constructor
  · rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      have h0 : ringTarget n (ringState n 0).1 = 0 := by simp [ringTarget, ringState]
      unfold RingBulk at hb
      rw [h0] at hb
      linarith [forty_le_ringCap n]
    · exact h
  · by_contra h
    have hk' : k = ringK n - 1 := by omega
    have := not_bulk_last (n := n) (by omega)
    rw [← hk'] at this
    exact absurd hb (not_le.2 this)

theorem ringStep_of_cont {n j : ℕ} (hj : j + 1 < ringK n) (hC : RingCont n (ringState n j)) :
    ringState n (j + 1) = ((ringState n j).1 + (ringState n j).2.1, (ringState n j).2.1,
      (ringState n j).2.2 + 1) := by
  have hlt0 : (ringState n j).1 < n := ringState_lt_of_lt_ringK (by omega)
  have hlt : (ringStep n (ringState n j)).1 < n := by
    rw [← ringState_succ]; exact ringState_lt_of_lt_ringK hj
  rw [ringState_succ]
  rcases (ringStep_cases hlt0 hlt).2 with ⟨_, he⟩ | ⟨hC', _⟩
  · exact he
  · exact absurd hC hC'

theorem ringCRow_N {n j : ℕ} (h : RingCRow n j) : ringN n j = ringN n (j - 1) := by
  obtain ⟨hj1, hj, hC⟩ := h
  have e := ringStep_of_cont hj hC
  unfold ringN
  rw [e, Nat.sub_add_cancel hj1]

theorem ringCRow_J {n j : ℕ} (h : RingCRow n j) : ringJ n j = ringJ n (j - 1) + 1 := by
  obtain ⟨hj1, hj, hC⟩ := h
  have e := ringStep_of_cont hj hC
  unfold ringJ
  rw [e, Nat.sub_add_cancel hj1]

theorem ringCRow_bulk {n j : ℕ} (h : RingCRow n j) : RingBulk n j ∧ RingBulk n (j - 1) := by
  obtain ⟨hj1, hj, hC⟩ := h
  refine ⟨hC.2.1, ?_⟩
  have hs := ringStep_spec_at (n := n) (k := j - 1) (by omega)
  rw [Nat.sub_add_cancel hj1] at hs
  have e : (ringState n j).1 - (ringState n j).2.1 = (ringState n (j - 1)).1 := by
    have : (ringState n j).2.1 = ringN n (j - 1) := by unfold ringN; rw [Nat.sub_add_cancel hj1]
    rw [this, hs.1]; omega
  have := hC.2.2.1
  rw [e] at this
  exact this

/-- Along a band `[lo, hi]` (every row in `(lo, hi]` is a (C)-row) the count is constant. -/
theorem ringBand_N {n lo hi : ℕ} (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) :
    ∀ j, lo ≤ j → j ≤ hi → ringN n j = ringN n lo := by
  intro j hlo hhi
  induction j with
  | zero => have : lo = 0 := by omega
            rw [this]
  | succ j ih =>
    rcases hlo.eq_or_lt with h | h
    · rw [h]
    · rw [ringCRow_N (hband (j + 1) h hhi), Nat.add_sub_cancel]
      exact ih (by omega) (by omega)

/-- Along a band the band index increases by one per row. -/
theorem ringBand_J {n lo hi : ℕ} (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) :
    ∀ j, lo ≤ j → j ≤ hi → ringJ n j = ringJ n lo + (j - lo) := by
  intro j hlo hhi
  induction j with
  | zero => have : lo = 0 := by omega
            subst this; simp
  | succ j ih =>
    rcases hlo.eq_or_lt with h | h
    · rw [h]; simp
    · rw [ringCRow_J (hband (j + 1) h hhi), Nat.add_sub_cancel, ih (by omega) (by omega)]
      omega

/-- Every row of a band whose first row is bulk is bulk. -/
theorem ringBand_bulk {n lo hi : ℕ} (hlo : RingBulk n lo)
    (hband : ∀ j, lo < j → j ≤ hi → RingCRow n j) : ∀ j, lo ≤ j → j ≤ hi → RingBulk n j := by
  intro j h1 h2
  rcases h1.eq_or_lt with h | h
  · rw [← h]; exact hlo
  · exact (ringCRow_bulk (hband j h h2)).1

/-! ### Two-sided barycentre bounds -/

/-- On a bounded slab `[α, β] = [τ(c), τ(d)]` with barycentre `t`, `ρ = ϱ(t)`, `N = d - c`,
`L = β - α`: `(N/(2ρ)) e^{-6L} ≤ t - α ≤ (N/(2ρ)) e^{6L}`, and the same for `β - t`. -/
theorem slabBary_bounds_exp {n c d : ℝ} (hc : 0 < c) (hcd : c < d) (hdn : d < n)
    (hs1 : ringQuantile n c ≤ slabBary n c d) (hs2 : slabBary n c d ≤ ringQuantile n d) :
    (d - c) / (2 * ringDensity n (slabBary n c d)) *
        Real.exp (-(6 * (ringQuantile n d - ringQuantile n c))) ≤
        slabBary n c d - ringQuantile n c ∧
      slabBary n c d - ringQuantile n c ≤ (d - c) / (2 * ringDensity n (slabBary n c d)) *
        Real.exp (6 * (ringQuantile n d - ringQuantile n c)) ∧
      (d - c) / (2 * ringDensity n (slabBary n c d)) *
        Real.exp (-(6 * (ringQuantile n d - ringQuantile n c))) ≤
        ringQuantile n d - slabBary n c d ∧
      ringQuantile n d - slabBary n c d ≤ (d - c) / (2 * ringDensity n (slabBary n c d)) *
        Real.exp (6 * (ringQuantile n d - ringQuantile n c)) := by
  have hn : 0 < n := by linarith
  have hρ : 0 < ringDensity n (slabBary n c d) := ringDensity_pos hn _
  have hdist : ∀ u ∈ Icc (ringQuantile n c) (ringQuantile n d),
      |u - slabBary n c d| ≤ ringQuantile n d - ringQuantile n c := fun u hu => by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have hM : ∀ u ∈ Icc (ringQuantile n c) (ringQuantile n d), ringDensity n u ≤
      ringDensity n (slabBary n c d) * Real.exp (2 * (ringQuantile n d - ringQuantile n c)) :=
    fun u hu => by
      have h := ringDensity_le_mul_exp hn.le (slabBary n c d) u
      have : Real.exp (2 * |u - slabBary n c d|) ≤
          Real.exp (2 * (ringQuantile n d - ringQuantile n c)) :=
        Real.exp_le_exp.2 (by linarith [hdist u hu])
      exact h.trans (mul_le_mul_of_nonneg_left this hρ.le)
  have hm : ∀ u ∈ Icc (ringQuantile n c) (ringQuantile n d),
      ringDensity n (slabBary n c d) * Real.exp (-(2 * (ringQuantile n d - ringQuantile n c))) ≤
        ringDensity n u := fun u hu => by
    have h := ringDensity_le_mul_exp hn.le u (slabBary n c d)
    rw [abs_sub_comm] at h
    have hE : Real.exp (2 * |u - slabBary n c d|) ≤
        Real.exp (2 * (ringQuantile n d - ringQuantile n c)) :=
      Real.exp_le_exp.2 (by linarith [hdist u hu])
    have hu0 := ringDensity_pos hn u
    have hE0 := Real.exp_pos (2 * (ringQuantile n d - ringQuantile n c))
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE0]
    calc ringDensity n (slabBary n c d) ≤ ringDensity n u * Real.exp (2 * |u - slabBary n c d|) := h
      _ ≤ ringDensity n u * Real.exp (2 * (ringQuantile n d - ringQuantile n c)) :=
          mul_le_mul_of_nonneg_left hE hu0.le
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := slab_moment_bounds hc hcd hdn hm hM
  have hL0 : 0 ≤ ringQuantile n d - ringQuantile n c := by linarith
  set α := ringQuantile n c
  set β := ringQuantile n d
  set s := slabBary n c d
  set N := d - c
  set ρ := ringDensity n s
  set L := β - α
  have hN0 : 0 < N := by simp only [N]; linarith
  set E := Real.exp (2 * L)
  have hE0 : 0 < E := Real.exp_pos _
  have hEi : Real.exp (-(2 * L)) = E⁻¹ := Real.exp_neg _
  have h6L : Real.exp (6 * L) = E ^ 3 := by simp only [E]; rw [← Real.exp_nat_mul]; ring_nf
  have h6Li : Real.exp (-(6 * L)) = (E ^ 3)⁻¹ := by rw [Real.exp_neg, h6L]
  rw [hEi] at h1 h3 h5
  rw [h6L, h6Li]
  -- `N / (ρ E) ≤ L ≤ N E / ρ`
  have hL1 : N / (ρ * E) ≤ L := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hL2 : L ≤ N * E / ρ := by
    rw [le_div_iff₀ hρ]
    have : ρ * E⁻¹ * L * E = ρ * L := by field_simp
    have h' : ρ * E⁻¹ * L ≤ N := h5
    have := mul_le_mul_of_nonneg_right h' hE0.le
    linarith
  have hLl : (N / (ρ * E)) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL1 2
  have hLu : L ^ 2 ≤ (N * E / ρ) ^ 2 := pow_le_pow_left₀ hL0 hL2 2
  -- lower: `N x ≥ ρ E⁻¹ L²/2 ≥ ρ E⁻¹ (N/(ρE))²/2 = N² /(2 ρ E³)`
  have low : ∀ x : ℝ, ρ * E⁻¹ * L ^ 2 / 2 ≤ N * x → N / (2 * ρ) * (E ^ 3)⁻¹ ≤ x := by
    intro x hx
    have : ρ * E⁻¹ * (N / (ρ * E)) ^ 2 / 2 ≤ N * x := by
      have := mul_le_mul_of_nonneg_left hLl (show 0 ≤ ρ * E⁻¹ / 2 by positivity)
      linarith
    have e : ρ * E⁻¹ * (N / (ρ * E)) ^ 2 / 2 = N * (N / (2 * ρ) * (E ^ 3)⁻¹) := by field_simp
    rw [e] at this
    exact le_of_mul_le_mul_left this hN0
  have up : ∀ x : ℝ, N * x ≤ ρ * E * L ^ 2 / 2 → x ≤ N / (2 * ρ) * E ^ 3 := by
    intro x hx
    have : N * x ≤ ρ * E * (N * E / ρ) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hLu (show 0 ≤ ρ * E / 2 by positivity)
      linarith
    have e : ρ * E * (N * E / ρ) ^ 2 / 2 = N * (N / (2 * ρ) * E ^ 3) := by field_simp
    rw [e] at this
    exact le_of_mul_le_mul_left this hN0
  exact ⟨low _ h1, up _ h2, low _ h3, up _ h4⟩

/-! ### The bulk aspect -/

/-- `N*(a)² = √3π ϱ(τ(a))` for `0 < a < n`. -/
theorem ringTarget_sq_eq_density {n a : ℕ} (ha : 0 < a) (han : a < n) :
    ringTarget n a ^ 2 = Real.sqrt 3 * Real.pi * ringDensity n (ringQuantile n a) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [ringTarget_sq n a han.le, ringDensity_eq_mass hn.ne',
    ringMass_quantile (by exact_mod_cast ha) (by exact_mod_cast han)]
  field_simp

theorem exp_le_one_add_mul_exp {y : ℝ} (_hy : 0 ≤ y) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have e : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos y]

/-- **(G5), bulk rows**: `|x_k - √3π| ≤ C_a (T + 1)/N_k` with `C_a = 42 + 324 e^{18}`. -/
theorem ringAspect_sub_le {n k : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hb : RingBulk n k) :
    |(ringRows n).aspect k - Real.sqrt 3 * Real.pi| ≤
      (42 + 324 * Real.exp 18) * ((ringTol n : ℝ) + 1) / ringN n k := by
  obtain ⟨hk1, hk'⟩ := ringBulk_interior hk hb
  obtain ⟨hN3, -, -, hb', ha0, hbn⟩ := ringInterior_facts (by omega) hk1 hk'
  obtain ⟨hlo, hhi⟩ := ringN_mem_Icc (by omega) hk1 hk'
  obtain ⟨-, hL⟩ := ringSlab_length_mem (by omega) hk1 hk'
  have hT := abs_ringN_sub_le_tol (by omega) hk' hb
  obtain ⟨hs1, hs2⟩ := ringHeight_mem_Icc (by omega) hk1 hk'
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 < (ringState n k).1 := by exact_mod_cast ha0
  have hAn : (ringState n k).1 < n := ringState_lt_of_lt_ringK (by omega)
  have hsq := ringTarget_sq_eq_density hA hAn
  have hasp : (ringRows n).aspect k = (ringN n k : ℝ) ^ 2 / ringDensity n (ringHeight n k) := by
    rw [RowConfig.aspect, ringRows_card]; rfl
  have hρt := (ringDensity_interior (by omega) hk1 hk' ⟨hs1, hs2⟩).2
  -- comparison of `ϱ` at `τ(A_k)` and at `t_k`
  set α := ringQuantile n (ringState n k).1
  set β := ringQuantile n (ringState n (k + 1)).1
  set L := β - α
  set tk := ringHeight n k
  set N := (ringN n k : ℝ)
  set x := ringTarget n (ringState n k).1
  set ρ := ringDensity n tk
  set ρa := ringDensity n α
  set T := (ringTol n : ℝ)
  set c := Real.sqrt 3 * Real.pi
  have hc6 : c < 6 := by have := two_sqrt_three_pi_lt; simp only [c]; linarith
  have hc0 : 0 < c := by simp only [c]; positivity
  have hρ0 : 0 < ρ := ringDensity_pos hn' _
  have hN0 : 0 < N := by linarith
  have hdist : |tk - α| ≤ L := by rw [abs_le]; constructor <;> linarith
  have hL0 : 0 ≤ L := by linarith
  have h2L : 2 * L ≤ 18 := by
    have : 27 / N ≤ 9 := by rw [div_le_iff₀ hN0]; linarith
    linarith
  have hρa1 : ρa ≤ ρ * Real.exp (2 * L) := by
    have := ringDensity_le_mul_exp hn'.le tk α
    rw [abs_sub_comm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hρ0.le)
  have hρa2 : ρ ≤ ρa * Real.exp (2 * L) := by
    have := ringDensity_le_mul_exp hn'.le α tk
    exact this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
      (ringDensity_pos hn' _).le)
  -- `|ρa/ρ - 1| ≤ e^{2L} - 1 ≤ 2L e^{18}`
  have hE : Real.exp (2 * L) - 1 ≤ 2 * L * Real.exp 18 := by
    have := exp_le_one_add_mul_exp (show 0 ≤ 2 * L by linarith)
    have h2 : Real.exp (2 * L) ≤ Real.exp 18 := Real.exp_le_exp.2 h2L
    linarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * L)]
  have hq : |ρa / ρ - 1| ≤ 2 * L * Real.exp 18 := by
    have hE1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
    rw [abs_le]; constructor
    · -- `ρa/ρ ≥ e^{-2L} ≥ 1 - 2L`
      have : ρ / Real.exp (2 * L) ≤ ρa := by rw [div_le_iff₀ (Real.exp_pos _)]; exact hρa2
      have h1 : 1 - 2 * L ≤ ρa / ρ := by
        have hinv : 1 - 2 * L ≤ 1 / Real.exp (2 * L) := by
          rw [one_div, ← Real.exp_neg]; linarith [Real.add_one_le_exp (-(2 * L))]
        calc 1 - 2 * L ≤ 1 / Real.exp (2 * L) := hinv
          _ = (ρ / Real.exp (2 * L)) / ρ := by field_simp
          _ ≤ ρa / ρ := by gcongr
      have : 2 * L ≤ 2 * L * Real.exp 18 :=
        le_mul_of_one_le_right (by linarith) (Real.one_le_exp (by norm_num))
      linarith
    · have : ρa / ρ ≤ Real.exp (2 * L) := by rw [div_le_iff₀ hρ0]; linarith
      linarith
  -- `|N² - x²| ≤ (7/3) T N`
  have hNx : |N ^ 2 - x ^ 2| ≤ 7 / 3 * T * N := by
    have hNx0 : 0 < N + x := by
      have := ringTarget_nonneg n (ringState n k).1; simp only [x] at this ⊢; linarith
    rw [show N ^ 2 - x ^ 2 = (N - x) * (N + x) by ring, abs_mul, abs_of_pos hNx0]
    have hx : x ≤ 4 / 3 * N := by linarith
    have hT0 : 0 ≤ T := Nat.cast_nonneg _
    calc |N - x| * (N + x) ≤ T * (N + x) := mul_le_mul_of_nonneg_right hT (by
          have := ringTarget_nonneg n (ringState n k).1; simp only [x] at this ⊢; linarith)
      _ ≤ T * (N + 4 / 3 * N) := by gcongr
      _ = 7 / 3 * T * N := by ring
  -- `x_k - √3π = (N² - x²)/ρ + c (ρa/ρ - 1)`
  have hdecomp : N ^ 2 / ρ - c = (N ^ 2 - x ^ 2) / ρ + c * (ρa / ρ - 1) := by
    rw [hsq]; field_simp; ring
  rw [hasp, hdecomp]
  have h1 : |(N ^ 2 - x ^ 2) / ρ| ≤ 42 * T / N := by
    rw [abs_div, abs_of_pos hρ0, div_le_div_iff₀ hρ0 hN0]
    have hT0 : 0 ≤ T := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hNx hN0.le
    linarith [mul_le_mul_of_nonneg_left hρt hT0]
  have h2 : |c * (ρa / ρ - 1)| ≤ 324 * Real.exp 18 / N := by
    rw [abs_mul, abs_of_pos hc0]
    have hLN : L ≤ 27 / N := hL
    have hE18 := Real.exp_pos 18
    calc c * |ρa / ρ - 1| ≤ 6 * (2 * (27 / N) * Real.exp 18) := by
          apply mul_le_mul hc6.le (hq.trans (by gcongr)) (abs_nonneg _) (by norm_num)
      _ = 324 * Real.exp 18 / N := by ring
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  calc |(N ^ 2 - x ^ 2) / ρ + c * (ρa / ρ - 1)| ≤ |(N ^ 2 - x ^ 2) / ρ| + |c * (ρa / ρ - 1)| :=
        abs_add_le _ _
    _ ≤ 42 * T / N + 324 * Real.exp 18 / N := add_le_add h1 h2
    _ ≤ (42 + 324 * Real.exp 18) * (T + 1) / N := by
        rw [← add_div, div_le_div_iff_of_pos_right hN0]
        linarith [mul_nonneg (Real.exp_pos 18).le hT0]

end Sphere

end SandierSerfaty

end
