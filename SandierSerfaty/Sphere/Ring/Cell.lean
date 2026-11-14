/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Aspect

/-!
# The cell term on interior rows (sphere note, Lemma 5.9)

For a bounded slab `[α, β] = [τ(c), τ(d)]` and a point `s ∈ [α, β]`, the cell integral
`∫_{c ≤ Φ ≤ d} ((d - c) 1_{t ≥ s} - (Φ - c))²` splits as `∫_α^s (Φ - c)² + ∫_s^β (Φ - d)²`
(`Sphere.cell_split`). If `ϱ ≤ M` on `[α, β]`, then `0 ≤ Φ - c ≤ M (t - α)` and
`0 ≤ d - Φ ≤ M (β - t)`, so the cell integral is at most `(M²/3)((s - α)³ + (β - s)³)`
(`Sphere.cell_le_cube`); it is also at most `(d - c)² (β - α)` (`Sphere.cell_le_sq_mul`).

For the rows of `Y_n` (interior rows, `n ≥ 102`):

* `Sphere.ringCell_le`: `Cell_k ≤ N_k² |I_k| ≤ 27 N_k` (Lemma 5.9, crude bound);
* `Sphere.ringCell_le_aspect`: `Cell_k ≤ (N_k x_k / 12) e^{22 |I_k|}` (Lemma 5.9 in the form used in
  the bulk). This replaces the sphere note's `Λ_k (1 + 3(Λ_k - 1)²)` factor: in `t`, with
  `ρ = ϱ(t_k)` and `L = |I_k|`, one has `ρ e^{-2L} ≤ ϱ ≤ ρ e^{2L}` on `I_k`, hence
  `t_k - α, β - t_k ≤ N_k e^{6L}/(2ρ)` by the moment bounds.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

/-- **The cell split.** For `0 < c < d < n` and `s ∈ [τ(c), τ(d)]`,
`∫_{c ≤ Φ ≤ d} ((d - c) 1_{t ≥ s} - (Φ - c))² = ∫_{τ(c)}^s (Φ - c)² + ∫_s^{τ(d)} (Φ - d)²`. -/
theorem cell_split {n c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hdn : d < n)
    (hs1 : ringQuantile n c ≤ s) (hs2 : s ≤ ringQuantile n d) :
    ∫ t in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        ((if s ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2 =
      (∫ t in ringQuantile n c..s, (ringMass n t - c) ^ 2) +
        ∫ t in s..ringQuantile n d, (ringMass n t - d) ^ 2 := by
  have hn : 0 < n := by linarith
  have hΦ1 : c ≤ ringMass n s := (le_ringMass_iff hc (by linarith) s).2 hs1
  have hΦ2 : ringMass n s ≤ d := (ringMass_le_iff (by linarith) hdn s).2 hs2
  rw [integral_slab hn hc.le hcd hdn.le hΦ1 hΦ2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cellPrimitive n c x)
      ((continuous_cellIntegrand n c).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cellPrimitive n d x)
      ((continuous_cellIntegrand n d).intervalIntegrable _ _)]
  rw [cellBoundary, cellBoundary, ite_eq_right hc.ne', ite_eq_right (by linarith : c ≠ n),
    ite_eq_right (by linarith : d ≠ 0), ite_eq_right hdn.ne]
  ring

/-- If `ϱ ≤ M` on `[α, β]` (`α = τ(c)`), then `Φ(t) - c ≤ M (t - α)` for `t ∈ [α, β]`. -/
theorem ringMass_sub_le {n c β M t : ℝ} (hc : 0 < c) (hcn : c < n)
    (hM : ∀ u ∈ Icc (ringQuantile n c) β, ringDensity n u ≤ M) (ht : t ∈ Icc (ringQuantile n c) β) :
    ringMass n t - c ≤ M * (t - ringQuantile n c) := by
  have h := intervalIntegral.integral_mono_on ht.1 ((continuous_ringDensity n).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume)) (fun u hu => hM u ⟨hu.1, hu.2.trans ht.2⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_ringMass n x)
    ((continuous_ringDensity n).intervalIntegrable _ _), intervalIntegral.integral_const,
    smul_eq_mul, ringMass_quantile hc hcn] at h
  linarith

/-- If `ϱ ≤ M` on `[α, β]` (`β = τ(d)`), then `d - Φ(t) ≤ M (β - t)` for `t ∈ [α, β]`. -/
theorem sub_ringMass_le {n d α M t : ℝ} (hd : 0 < d) (hdn : d < n)
    (hM : ∀ u ∈ Icc α (ringQuantile n d), ringDensity n u ≤ M) (ht : t ∈ Icc α (ringQuantile n d)) :
    d - ringMass n t ≤ M * (ringQuantile n d - t) := by
  have h := intervalIntegral.integral_mono_on ht.2 ((continuous_ringDensity n).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume)) (fun u hu => hM u ⟨ht.1.trans hu.1, hu.2⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_ringMass n x)
    ((continuous_ringDensity n).intervalIntegrable _ _), intervalIntegral.integral_const,
    smul_eq_mul, ringMass_quantile hd hdn] at h
  linarith

theorem integral_sub_sq (α s : ℝ) : ∫ t in α..s, (t - α) ^ 2 = (s - α) ^ 3 / 3 := by
  have h : ∀ x ∈ uIcc α s, HasDerivAt (fun t => (t - α) ^ 3 / 3) ((x - α) ^ 2) x := fun x _ => by
    have := (((hasDerivAt_id' x).sub_const α).pow 3).div_const 3
    convert this using 1; push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (((continuous_id.sub continuous_const).pow 2).intervalIntegrable _ _)]
  ring

theorem integral_sub_sq' (s β : ℝ) : ∫ t in s..β, (β - t) ^ 2 = (β - s) ^ 3 / 3 := by
  have h : ∀ x ∈ uIcc s β, HasDerivAt (fun t => -((β - t) ^ 3 / 3)) ((β - x) ^ 2) x := fun x _ => by
    have := ((((hasDerivAt_id' x).const_sub β).pow 3).div_const 3).neg
    convert this using 1; push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (((continuous_const.sub continuous_id).pow 2).intervalIntegrable _ _)]
  ring

/-- **Cell bound, cubic form.** If `ϱ ≤ M` on `[α, β] = [τ(c), τ(d)]` and `s ∈ [α, β]`, the cell
integral is at most `(M²/3)((s - α)³ + (β - s)³)`. -/
theorem cell_le_cube {n c d s M : ℝ} (hc : 0 < c) (hcd : c < d) (hdn : d < n)
    (hs1 : ringQuantile n c ≤ s) (hs2 : s ≤ ringQuantile n d)
    (hM : ∀ u ∈ Icc (ringQuantile n c) (ringQuantile n d), ringDensity n u ≤ M) :
    ∫ t in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        ((if s ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2 ≤
      M ^ 2 / 3 * ((s - ringQuantile n c) ^ 3 + (ringQuantile n d - s) ^ 3) := by
  have hn : 0 < n := by linarith
  rw [cell_split hc hcd hdn hs1 hs2]
  set α := ringQuantile n c
  set β := ringQuantile n d
  have hmono := ringMass_strictMono hn
  have h1 : ∫ t in α..s, (ringMass n t - c) ^ 2 ≤ ∫ t in α..s, M ^ 2 * (t - α) ^ 2 :=
    intervalIntegral.integral_mono_on hs1 ((continuous_cellIntegrand n c).intervalIntegrable _ _)
      ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _)
      fun t ht => by
        have h0 : 0 ≤ ringMass n t - c := by
          have := (le_ringMass_iff hc (by linarith) t).2 ht.1; linarith
        have hle := ringMass_sub_le hc (by linarith) (β := β) (fun u hu => hM u hu) ⟨ht.1, ht.2.trans hs2⟩
        rw [← mul_pow]; exact pow_le_pow_left₀ h0 hle 2
  have h2 : ∫ t in s..β, (ringMass n t - d) ^ 2 ≤ ∫ t in s..β, M ^ 2 * (β - t) ^ 2 :=
    intervalIntegral.integral_mono_on hs2 ((continuous_cellIntegrand n d).intervalIntegrable _ _)
      ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).intervalIntegrable _ _)
      fun t ht => by
        have h0 : 0 ≤ d - ringMass n t := by
          have := (ringMass_le_iff (by linarith) hdn t).2 ht.2; linarith
        have hle := sub_ringMass_le (α := α) (by linarith) hdn (fun u hu => hM u hu) ⟨hs1.trans ht.1, ht.2⟩
        rw [← mul_pow, show (ringMass n t - d) ^ 2 = (d - ringMass n t) ^ 2 by ring]
        exact pow_le_pow_left₀ h0 hle 2
  rw [intervalIntegral.integral_const_mul, integral_sub_sq] at h1
  rw [intervalIntegral.integral_const_mul, integral_sub_sq'] at h2
  linarith

/-- **Cell bound, crude form.** The cell integral is at most `(d - c)² (β - α)`. -/
theorem cell_le_sq_mul {n c d s : ℝ} (hc : 0 < c) (hcd : c < d) (hdn : d < n)
    (hs1 : ringQuantile n c ≤ s) (hs2 : s ≤ ringQuantile n d) :
    ∫ t in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        ((if s ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2 ≤
      (d - c) ^ 2 * (ringQuantile n d - ringQuantile n c) := by
  rw [cell_split hc hcd hdn hs1 hs2]
  set α := ringQuantile n c
  set β := ringQuantile n d
  have hb : ∀ t ∈ Icc α β, c ≤ ringMass n t ∧ ringMass n t ≤ d := fun t ht =>
    ⟨(le_ringMass_iff hc (by linarith) t).2 ht.1, (ringMass_le_iff (by linarith) hdn t).2 ht.2⟩
  have h1 : ∫ t in α..s, (ringMass n t - c) ^ 2 ≤ ∫ _ in α..s, (d - c) ^ 2 :=
    intervalIntegral.integral_mono_on hs1 ((continuous_cellIntegrand n c).intervalIntegrable _ _)
      intervalIntegrable_const fun t ht => by
        obtain ⟨h1, h2⟩ := hb t ⟨ht.1, ht.2.trans hs2⟩
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : ∫ t in s..β, (ringMass n t - d) ^ 2 ≤ ∫ _ in s..β, (d - c) ^ 2 :=
    intervalIntegral.integral_mono_on hs2 ((continuous_cellIntegrand n d).intervalIntegrable _ _)
      intervalIntegrable_const fun t ht => by
        obtain ⟨h1, h2⟩ := hb t ⟨hs1.trans ht.1, ht.2⟩
        rw [show (ringMass n t - d) ^ 2 = (d - ringMass n t) ^ 2 by ring]
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
  nlinarith

/-! ### The rows of `Y_n` -/

/-- The cell term of row `k` of `Y_n` as a slab integral. -/
theorem ringRows_cell_eq {n k : ℕ} (hk : k < ringK n) :
    (ringRows n).cell k = ∫ t in {t | ((ringState n k).1 : ℝ) ≤ ringMass n t ∧
        ringMass n t ≤ (ringState n (k + 1)).1},
      ((if ringHeight n k ≤ t then ((ringState n (k + 1)).1 : ℝ) - (ringState n k).1 else 0) -
        (ringMass n t - (ringState n k).1)) ^ 2 := by
  have h : ((ringState n (k + 1)).1 : ℝ) - (ringState n k).1 = ringN n k := by
    rw [(ringStep_spec_at hk).1]; push_cast; ring
  rw [RowConfig.cell, RowConfig.slab, ringRows_card, ringRows_mass n k hk.le,
    ringRows_mass n (k + 1) hk, h]
  rfl

/-- `t_k ∈ I_k` for interior rows. -/
theorem ringHeight_mem_Icc {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    ringHeight n k ∈ Icc (ringQuantile n (ringState n k).1) (ringQuantile n (ringState n (k + 1)).1) := by
  obtain ⟨hm1, hm2⟩ := ringHeight_mem (show k < ringK n by omega)
  obtain ⟨-, -, -, hb, ha0, hbn⟩ := ringInterior_facts hn hk1 hk
  have hab : ((ringState n k).1 : ℝ) ≤ (ringState n (k + 1)).1 := ringState_cast_le (by omega)
  exact ⟨(le_ringMass_iff ha0 (by linarith) _).1 hm1.le, (ringMass_le_iff (by linarith) hbn _).1 hm2.le⟩

/-- **Lemma 5.9, crude bound**: on interior rows, `Cell_k ≤ N_k² |I_k| ≤ 27 N_k`. -/
theorem ringCell_le {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    (ringRows n).cell k ≤ 27 * (ringN n k : ℝ) := by
  obtain ⟨hN3, -, -, hb, ha0, hbn⟩ := ringInterior_facts hn hk1 hk
  obtain ⟨-, hL⟩ := ringSlab_length_mem hn hk1 hk
  obtain ⟨hs1, hs2⟩ := ringHeight_mem_Icc hn hk1 hk
  have hNdiff : ((ringState n (k + 1)).1 : ℝ) - (ringState n k).1 = ringN n k := by rw [hb]; ring
  rw [ringRows_cell_eq (by omega)]
  refine (cell_le_sq_mul ha0 (by linarith) hbn hs1 hs2).trans ?_
  rw [hNdiff]
  have hN0 : (0 : ℝ) < ringN n k := by linarith
  calc (ringN n k : ℝ) ^ 2 * (ringQuantile n (ringState n (k + 1)).1 - ringQuantile n (ringState n k).1)
      ≤ (ringN n k : ℝ) ^ 2 * (27 / ringN n k) := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = 27 * (ringN n k : ℝ) := by field_simp

/-- **Cell bound, aspect form**, for a bounded slab with its barycentre `s`:
the cell integral is at most `(N · N²/ϱ(s))/12 · e^{22 (β - α)}` (`N = d - c`). -/
theorem cell_le_aspect_general {n c d : ℝ} (hc : 0 < c) (hcd : c < d) (hdn : d < n)
    (hs1 : ringQuantile n c ≤ slabBary n c d) (hs2 : slabBary n c d ≤ ringQuantile n d) :
    ∫ t in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        ((if slabBary n c d ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2 ≤
      (d - c) * ((d - c) ^ 2 / ringDensity n (slabBary n c d)) / 12 *
        Real.exp (22 * (ringQuantile n d - ringQuantile n c)) := by
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
  have hcube := cell_le_cube hc hcd hdn hs1 hs2 hM
  obtain ⟨-, h2, -, h4, h5, -⟩ := slab_moment_bounds hc hcd hdn hm hM
  have hL0 : 0 ≤ ringQuantile n d - ringQuantile n c := by linarith
  set α := ringQuantile n c
  set β := ringQuantile n d
  set s := slabBary n c d
  set N := d - c
  set ρ := ringDensity n s
  set L := β - α
  set M := ρ * Real.exp (2 * L)
  set m := ρ * Real.exp (-(2 * L))
  have hN0 : 0 < N := by simp only [N]; linarith
  have hm0 : 0 < m := by positivity
  have hkey : ∀ x : ℝ, 0 ≤ x → N * x ≤ M * L ^ 2 / 2 → x ≤ N * Real.exp (6 * L) / (2 * ρ) := by
    intro x hx hNx
    have hLN : L ≤ N / m := by rw [le_div_iff₀ hm0]; linarith
    have hL2 : L ^ 2 ≤ (N / m) ^ 2 := pow_le_pow_left₀ hL0 hLN 2
    have e : M * (N / m) ^ 2 / 2 = N * (N * Real.exp (6 * L) / (2 * ρ)) := by
      simp only [M, m]
      rw [show Real.exp (6 * L) = Real.exp (2 * L) ^ 3 by rw [← Real.exp_nat_mul]; ring_nf,
        Real.exp_neg]
      field_simp
    have h' : M * L ^ 2 / 2 ≤ M * (N / m) ^ 2 / 2 := by
      have : 0 ≤ M := by positivity
      have := mul_le_mul_of_nonneg_left hL2 this
      linarith
    have : N * x ≤ N * (N * Real.exp (6 * L) / (2 * ρ)) := by rw [← e]; linarith
    exact le_of_mul_le_mul_left this hN0
  have ht1 := hkey _ (by linarith) h2
  have ht2 := hkey _ (by linarith) h4
  set B := N * Real.exp (6 * L) / (2 * ρ)
  have hc1 : (s - α) ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (by linarith) ht1 3
  have hc2 : (β - s) ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (by linarith) ht2 3
  refine hcube.trans ?_
  have hM2 : 0 ≤ M ^ 2 / 3 := by positivity
  calc M ^ 2 / 3 * ((s - α) ^ 3 + (β - s) ^ 3) ≤ M ^ 2 / 3 * (B ^ 3 + B ^ 3) :=
        mul_le_mul_of_nonneg_left (by linarith) hM2
    _ = N * (N ^ 2 / ρ) / 12 * Real.exp (22 * L) := by
        simp only [M, B]
        rw [show Real.exp (22 * L) = Real.exp (2 * L) ^ 2 * Real.exp (6 * L) ^ 3 by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf]
        field_simp
        ring

/-- **Lemma 5.9, bulk form**: on interior rows, `Cell_k ≤ (N_k x_k/12) e^{22 |I_k|}`. -/
theorem ringCell_le_aspect {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    (ringRows n).cell k ≤ (ringN n k : ℝ) * (ringRows n).aspect k / 12 *
      Real.exp (22 * (ringQuantile n (ringState n (k + 1)).1 - ringQuantile n (ringState n k).1)) := by
  obtain ⟨hN3, -, -, hb, ha0, hbn⟩ := ringInterior_facts hn hk1 hk
  obtain ⟨hs1, hs2⟩ := ringHeight_mem_Icc hn hk1 hk
  have hNdiff : ((ringState n (k + 1)).1 : ℝ) - (ringState n k).1 = ringN n k := by rw [hb]; ring
  have hasp : (ringRows n).aspect k = (ringN n k : ℝ) ^ 2 / ringDensity n (ringHeight n k) := by
    rw [RowConfig.aspect, ringRows_card]; rfl
  have hhk := ringHeight_eq_slabBary (show k < ringK n by omega)
  rw [ringRows_cell_eq (by omega), hasp, hhk]
  rw [hhk] at hs1 hs2
  have h := cell_le_aspect_general ha0 (by linarith) hbn hs1 hs2
  rw [hNdiff] at h ⊢; exact h

end Sphere

end SandierSerfaty

end
