/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Majorant

/-!
# `B = ∑ u_i` is `C²` on `(0, ∞)` and `cal:radial-endpoints`

* `B_eq_fin_add_tail`: `B t = ∑_{i<39} u_i t + ∑'_m u_{m+39} t` for `t > 0` (the mode `0` carries the
  logarithm, which is unbounded near `0`, so it stays out of the termwise-differentiated series, whose term
  bounds hold uniformly on `(0, ∞)`);
* `contDiffOn_B`: `B ∈ C²((0, ∞))`, by `tsum_contDiffOn_two` for the tail on `(0, ∞)` (the bounds
  `u_bounds` hold for every `t > 0`);
* `radial_origin`: `B(r) = -log r + O(r²)` and `B'(r) = -1/r + O(r)` on `(0, 1/2)` (paper §5.3,
  the first line of `cal:radial-endpoints`); here `u_0 = γ = -log r + π r²/2` and `u_m = (-1)^m c_m r^{6m}`
  on `(0, R₀]`, and the coefficient series is summable at every `x < a` (`abs_coeff_mul_pow_le`);
* `radial_endpoints`: `cal:radial-endpoints` in full (`D_i = 0` and `B = B(l)` beyond `l`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

/-! ### The finite part and the tail -/

/-- The retained modes `i < 39` of `B`. -/
@[expose] noncomputable def Bfin (t : ℝ) : ℝ := ∑ i ∈ Finset.range 39, u i t

/-- The omitted modes `i ≥ 39` of `B`. -/
@[expose] noncomputable def Btail (t : ℝ) : ℝ := ∑' m : ℕ, u (m + 39) t

theorem summable_wk_tail : Summable fun m : ℕ => Tails.wk (6 * (m + 39)) := by
  have := (summable_nat_add_iff 39).2 (summable_pow_wk 0)
  simpa using this

theorem summable_u_tail {t : ℝ} (ht : 0 < t) : Summable fun m : ℕ => u (m + 39) t :=
  Summable.of_norm_bounded summable_wk_tail fun m => by
    rw [Real.norm_eq_abs]; exact (u_bounds (by omega) ht).1

theorem summable_u {t : ℝ} (ht : 0 < t) : Summable fun i : ℕ => u i t :=
  (summable_nat_add_iff 39).1 (summable_u_tail ht)

theorem B_eq_fin_add_tail {t : ℝ} (ht : 0 < t) : B t = Bfin t + Btail t := by
  unfold B Bfin Btail
  exact ((summable_u ht).sum_add_tsum_nat_add 39).symm

theorem contDiffOn_Btail : ContDiffOn ℝ 2 Btail (Ioi 0) :=
  (tsum_contDiffOn_two (g := fun m => u (m + 39)) (M₀ := fun m => Tails.wk (6 * (m + 39)))
    (M₁ := fun m => Tails.wk (6 * (m + 39))) (M₂ := fun m => Tails.wk (6 * (m + 39)))
    isOpen_Ioi isPreconnected_Ioi summable_wk_tail summable_wk_tail summable_wk_tail
    (fun m => contDiffOn_u (m + 39))
    (fun m x hx => (u_bounds (by omega) hx).1)
    (fun m x hx => (u_bounds (by omega) hx).2.1)
    (fun m x hx => (u_bounds (by omega) hx).2.2)).1

theorem contDiffOn_Bfin : ContDiffOn ℝ 2 Bfin (Ioi 0) := by
  unfold Bfin
  exact ContDiffOn.sum fun i _ => contDiffOn_u i

/-- `B ∈ C²((0, ∞))` (termwise differentiation of the omitted modes). -/
theorem contDiffOn_B : ContDiffOn ℝ 2 B (Ioi 0) :=
  (contDiffOn_Bfin.add contDiffOn_Btail).congr fun _ ht => B_eq_fin_add_tail ht

/-! ### The coefficient series -/

theorem half_lt_a : 1 / 2 < a := by linarith [Tails.a_gt]

theorem half_lt_R₀ : 1 / 2 < R₀ := by linarith [R₀_gt]

/-- `∑_m (6m)^j |c_m| x^{6m} < ∞` for `j ∈ {0, 1}` and `0 ≤ x < a`. -/
theorem summable_abs_coeff_pow {x : ℝ} (hx : 0 ≤ x) (hxa : x < a) {j : ℕ} (hj : j ≤ 1) :
    Summable fun m : ℕ => ((6 * m : ℕ) : ℝ) ^ j * (|coeff m| * x ^ (6 * m)) := by
  have ha := a_pos
  have hq : 0 ≤ x / a := div_nonneg hx ha.le
  have hr : (x / a) ^ 6 < 1 := pow_lt_one₀ hq ((div_lt_one ha).2 hxa) (by norm_num)
  have hg : Summable fun m : ℕ => 7 * ((x / a) ^ 6) ^ m :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left 7
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((summable_nat_add_iff 2).2 hg)
  have h := Tails.abs_coeff_mul_pow_le (m := m + 2) (by omega) hx
  rw [k_of_pos (by omega)] at h
  have hk : (1 : ℝ) ≤ ((6 * (m + 2) : ℕ) : ℝ) := by
    have : 1 ≤ 6 * (m + 2) := by omega
    exact_mod_cast this
  have hxx : (x / a) ^ (6 * (m + 2)) = ((x / a) ^ 6) ^ (m + 2) := by rw [← pow_mul]
  have hpos : 0 ≤ (x / a) ^ (6 * (m + 2)) := by positivity
  rw [hxx] at h hpos
  interval_cases j
  · simp only [pow_zero, one_mul]
    calc |coeff (m + 2)| * x ^ (6 * (m + 2))
        ≤ 7 / ((6 * (m + 2) : ℕ) : ℝ) * ((x / a) ^ 6) ^ (m + 2) := h
      _ ≤ 7 * ((x / a) ^ 6) ^ (m + 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos
          rw [div_le_iff₀ (by linarith)]; nlinarith
  · simp only [pow_one]
    calc ((6 * (m + 2) : ℕ) : ℝ) * (|coeff (m + 2)| * x ^ (6 * (m + 2)))
        ≤ ((6 * (m + 2) : ℕ) : ℝ) * (7 / ((6 * (m + 2) : ℕ) : ℝ) * ((x / a) ^ 6) ^ (m + 2)) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = 7 * ((x / a) ^ 6) ^ (m + 2) := by field_simp

/-! ### The expansion at the origin -/

/-- The term `(-1)^{m+1} c_{m+1} r^{6(m+1)}` of the coefficient series. -/
@[expose] noncomputable def ptm (m : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) * coeff (m + 1) * r ^ (6 * (m + 1))

/-- Its derivative. -/
@[expose] noncomputable def dptm (m : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) * coeff (m + 1) * (((6 * (m + 1) : ℕ) : ℝ) * r ^ (6 * (m + 1) - 1))

theorem hasDerivAt_ptm (m : ℕ) (r : ℝ) : HasDerivAt (ptm m) (dptm m r) r :=
  (hasDerivAt_pow (6 * (m + 1)) r).const_mul ((-1 : ℝ) ^ (m + 1) * coeff (m + 1))

theorem u_succ_eq_ptm {m : ℕ} {r : ℝ} (hr : r ≤ R₀) : u (m + 1) r = ptm m r := by
  rw [u_of_le_R₀ (Nat.succ_pos m) hr, k_of_pos (Nat.succ_pos m)]; rfl

/-- The series `P = ∑_{m ≥ 1} (-1)^m c_m r^{6m}`. -/
@[expose] noncomputable def Pser (r : ℝ) : ℝ := ∑' m : ℕ, ptm m r

/-- `N₀ m = 64 · |c_{m+1}| (1/2)^{6(m+1)}`: the majorant of `r^{-6} |ptm m r|` on `(0, 1/2]`. -/
noncomputable def N₀ (m : ℕ) : ℝ := |coeff (m + 1)| * (1 / 2 : ℝ) ^ (6 * m)

/-- The majorant of `r^{-5} |dptm m r|` on `(0, 1/2]`. -/
noncomputable def N₁ (m : ℕ) : ℝ := ((6 * (m + 1) : ℕ) : ℝ) * (|coeff (m + 1)| * (1 / 2 : ℝ) ^ (6 * m))

theorem summable_N₀ : Summable N₀ := by
  have h := (summable_nat_add_iff 1).2 (summable_abs_coeff_pow (x := 1 / 2) (by norm_num)
    half_lt_a (j := 0) (by norm_num))
  refine (h.mul_left 64).congr fun m => ?_
  unfold N₀
  simp only [pow_zero, one_mul]
  rw [show 6 * (m + 1) = 6 * m + 6 by ring, pow_add]
  norm_num; ring

theorem summable_N₁ : Summable N₁ := by
  have h := (summable_nat_add_iff 1).2 (summable_abs_coeff_pow (x := 1 / 2) (by norm_num)
    half_lt_a (j := 1) le_rfl)
  refine (h.mul_left 64).congr fun m => ?_
  unfold N₁
  simp only [pow_one]
  rw [show 6 * (m + 1) = 6 * m + 6 by ring, pow_add]
  norm_num; ring

theorem abs_ptm_le {m : ℕ} {r : ℝ} (hr : r ∈ Ioc 0 (1 / 2)) : |ptm m r| ≤ r ^ 6 * N₀ m := by
  unfold ptm N₀
  have h1 : r ^ (6 * m) ≤ (1 / 2 : ℝ) ^ (6 * m) := pow_le_pow_left₀ hr.1.le hr.2 _
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hr.1.le _), show 6 * (m + 1) = 6 + 6 * m by ring, pow_add]
  have := abs_nonneg (coeff (m + 1))
  have h6 : 0 ≤ r ^ 6 := by positivity
  calc |coeff (m + 1)| * (r ^ 6 * r ^ (6 * m)) = r ^ 6 * (|coeff (m + 1)| * r ^ (6 * m)) := by ring
    _ ≤ r ^ 6 * (|coeff (m + 1)| * (1 / 2 : ℝ) ^ (6 * m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 this) h6

theorem abs_dptm_le {m : ℕ} {r : ℝ} (hr : r ∈ Ioc 0 (1 / 2)) : |dptm m r| ≤ r ^ 5 * N₁ m := by
  unfold dptm N₁
  have h1 : r ^ (6 * m) ≤ (1 / 2 : ℝ) ^ (6 * m) := pow_le_pow_left₀ hr.1.le hr.2 _
  have hk : (0 : ℝ) ≤ ((6 * (m + 1) : ℕ) : ℝ) := by positivity
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
    abs_of_nonneg hk, abs_of_nonneg (pow_nonneg hr.1.le _),
    show 6 * (m + 1) - 1 = 5 + 6 * m by omega, pow_add]
  have := abs_nonneg (coeff (m + 1))
  have h5 : 0 ≤ r ^ 5 := pow_nonneg hr.1.le 5
  calc |coeff (m + 1)| * (((6 * (m + 1) : ℕ) : ℝ) * (r ^ 5 * r ^ (6 * m)))
      = r ^ 5 * (((6 * (m + 1) : ℕ) : ℝ) * (|coeff (m + 1)| * r ^ (6 * m))) := by ring
    _ ≤ r ^ 5 * (((6 * (m + 1) : ℕ) : ℝ) * (|coeff (m + 1)| * (1 / 2 : ℝ) ^ (6 * m))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h1 this) hk) h5

theorem abs_Pser_le {r : ℝ} (hr : r ∈ Ioc 0 (1 / 2)) : |Pser r| ≤ r ^ 6 * ∑' m, N₀ m := by
  have h := tsum_of_norm_bounded (summable_N₀.mul_left (r ^ 6)).hasSum
    (f := fun m => ptm m r) fun m => by rw [Real.norm_eq_abs]; exact abs_ptm_le hr
  rwa [tsum_mul_left, Real.norm_eq_abs] at h

theorem hasDerivAt_Pser {r : ℝ} (hr : r ∈ Ioo 0 (1 / 2)) :
    HasDerivAt Pser (∑' m, dptm m r) r := by
  have hu : Summable fun m => (1 / 2 : ℝ) ^ 5 * N₁ m := summable_N₁.mul_left _
  refine hasDerivAt_tsum_of_isPreconnected (u := fun m => (1 / 2 : ℝ) ^ 5 * N₁ m) hu isOpen_Ioo
    isPreconnected_Ioo (fun m y _ => hasDerivAt_ptm m y) (fun m y hy => ?_) hr
    (Summable.of_norm_bounded (summable_N₀.mul_left ((1 / 2 : ℝ) ^ 6)) fun m => ?_) hr
  · rw [Real.norm_eq_abs]
    refine (abs_dptm_le ⟨hy.1, hy.2.le⟩).trans ?_
    have : 0 ≤ N₁ m := by unfold N₁; positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.1.le hy.2.le 5) this
  · rw [Real.norm_eq_abs]
    refine (abs_ptm_le ⟨hr.1, hr.2.le⟩).trans ?_
    have : 0 ≤ N₀ m := by unfold N₀; positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.1.le hr.2.le 6) this

theorem abs_deriv_Pser_le {r : ℝ} (hr : r ∈ Ioo 0 (1 / 2)) :
    |deriv Pser r| ≤ r ^ 5 * ∑' m, N₁ m := by
  rw [(hasDerivAt_Pser hr).deriv]
  have h := tsum_of_norm_bounded (summable_N₁.mul_left (r ^ 5)).hasSum
    (f := fun m => dptm m r) fun m => by
      rw [Real.norm_eq_abs]; exact abs_dptm_le ⟨hr.1, hr.2.le⟩
  rwa [tsum_mul_left, Real.norm_eq_abs] at h

theorem B_eq_gamma_add_Pser {r : ℝ} (hr : r ∈ Ioc 0 (1 / 2)) : B r = gamma r + Pser r := by
  have hs := summable_u hr.1
  have h := hs.tsum_eq_zero_add
  unfold B
  rw [h, u_zero_of_le_R₀ (hr.2.trans half_lt_R₀.le)]
  congr 1
  exact tsum_congr fun m => u_succ_eq_ptm (hr.2.trans half_lt_R₀.le)

theorem hasDerivAt_gamma {r : ℝ} (hr : 0 < r) : HasDerivAt gamma (-(1 / r) + Real.pi * r) r := by
  have h1 := (Real.hasDerivAt_log hr.ne').neg
  have h2 := ((hasDerivAt_pow 2 r).const_mul Real.pi).div_const 2
  refine (h1.add h2).congr_deriv ?_ |>.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  · simp; ring
  · simp [gamma]

theorem deriv_B_eq {r : ℝ} (hr : r ∈ Ioo 0 (1 / 2)) :
    deriv B r = -(1 / r) + Real.pi * r + deriv Pser r := by
  have hP := hasDerivAt_Pser hr
  have hg := hasDerivAt_gamma hr.1
  have e : B =ᶠ[nhds r] fun y => gamma y + Pser y := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with y hy using B_eq_gamma_add_Pser ⟨hy.1, hy.2.le⟩
  rw [e.deriv_eq]
  exact ((hg.add hP).deriv).trans (by rw [hP.deriv])

/-- **`dual:radial-origin` for the calibration data** (paper §5.3): on `(0, 1/2)`,
`|B(r) + log r| ≤ C r²` and `|B'(r) + 1/r| ≤ C r`. -/
theorem radial_origin :
    ∃ C : ℝ, ∀ r ∈ Ioo (0 : ℝ) (1 / 2), |B r + Real.log r| ≤ C * r ^ 2 ∧
      |deriv B r + 1 / r| ≤ C * r := by
  refine ⟨Real.pi + (∑' m, N₀ m) + (∑' m, N₁ m), fun r hr => ?_⟩
  have hC₀ : 0 ≤ ∑' m, N₀ m := tsum_nonneg fun m => by unfold N₀; positivity
  have hC₁ : 0 ≤ ∑' m, N₁ m := tsum_nonneg fun m => by unfold N₁; positivity
  have hr0 := hr.1
  have hr1 : r ≤ 1 / 2 := hr.2.le
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · rw [B_eq_gamma_add_Pser ⟨hr0, hr1⟩]
    have e : gamma r + Pser r + Real.log r = Real.pi * r ^ 2 / 2 + Pser r := by
      unfold gamma; ring
    rw [e]
    have hP := abs_Pser_le (r := r) ⟨hr0, hr1⟩
    have h6 : r ^ 6 ≤ r ^ 2 := pow_le_pow_of_le_one hr0.le (by linarith) (by norm_num)
    calc |Real.pi * r ^ 2 / 2 + Pser r| ≤ |Real.pi * r ^ 2 / 2| + |Pser r| := abs_add_le _ _
      _ ≤ Real.pi * r ^ 2 + r ^ 2 * ∑' m, N₀ m := by
          rw [abs_of_nonneg (by positivity)]
          have : r ^ 6 * ∑' m, N₀ m ≤ r ^ 2 * ∑' m, N₀ m := mul_le_mul_of_nonneg_right h6 hC₀
          nlinarith
      _ ≤ (Real.pi + (∑' m, N₀ m) + (∑' m, N₁ m)) * r ^ 2 := by nlinarith [sq_nonneg r]
  · rw [deriv_B_eq hr]
    have hP := abs_deriv_Pser_le hr
    have e : -(1 / r) + Real.pi * r + deriv Pser r + 1 / r = Real.pi * r + deriv Pser r := by ring
    rw [e]
    have h5 : r ^ 5 ≤ r := by
      calc r ^ 5 ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le (by linarith) (by norm_num)
        _ = r := pow_one r
    calc |Real.pi * r + deriv Pser r| ≤ |Real.pi * r| + |deriv Pser r| := abs_add_le _ _
      _ ≤ Real.pi * r + r * ∑' m, N₁ m := by
          rw [abs_of_nonneg (by positivity)]
          have : r ^ 5 * ∑' m, N₁ m ≤ r * ∑' m, N₁ m := mul_le_mul_of_nonneg_right h5 hC₁
          linarith
      _ ≤ (Real.pi + (∑' m, N₀ m) + (∑' m, N₁ m)) * r := by nlinarith [hC₀]

/-- **`cal:radial-endpoints`** (paper §5.3): `B(r) = -log r + O(r²)`, `B'(r) = -1/r + O(r)` as `r ↓ 0`;
`D_i(r) = 0` and `B(r) = B(l)` for `r ≥ l`. -/
theorem radial_endpoints :
    (∃ C : ℝ, ∀ r ∈ Ioo (0 : ℝ) (1 / 2), |B r + Real.log r| ≤ C * r ^ 2 ∧
        |deriv B r + 1 / r| ≤ C * r) ∧
      (∀ i : ℕ, ∀ r : ℝ, l ≤ r → D i r = 0) ∧ ∀ r : ℝ, l ≤ r → B r = B l :=
  ⟨radial_origin, fun _ _ hr => D_of_ge hr, fun _ hr => B_eq_of_ge hr⟩

end Calibration

end SandierSerfaty

end
