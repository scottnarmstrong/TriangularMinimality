/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Bridge
public import SandierSerfaty.Certificate.Table.Init
public import SandierSerfaty.Certificate.Table.Inner
public import SandierSerfaty.Calibration.InnerExact

/-!
# The first segment and the initial checkpoint are the truncated calibration

On `seg 0 = (0, p - c]` the pieces are `u₀ = γ = -log r + π r²/2` and `u_m = a_m r^{k_m}` (`a_m = (-1)^m c_m`),
so `B̃₁ = ∑_{i ≤ 38} v_i r^{e_i - 1}` (`trunc_B₁_inner`) and the truncated sector functions are integrals of
monomials (`comp:initial-integrals`):

* `trunc_S₁_inner`, `trunc_S₂_inner`, `trunc_H_inner`: `Trunc.S₁ = S1init`, `Trunc.S₂ = S2init`,
  `Trunc.H k = Hinit k` on `seg 0`;
* `trunc_f₀_inner`, `trunc_e_inner`: the truncated form of `comp:inner-exact`, `f̃₀ = (πt² - ½) log t - 3π²t⁴/8`
  and `ẽ = 0` on `seg 0`. The cancellation is exact mode by mode, so it holds for the truncation (the full-series
  identity is `Cal.inner_exact`);
* `initCheck_sound_trunc`: an accepted initial checkpoint at a node `X ∋ t`, `t ≤ p - c`, encloses
  `Trunc.S₁, Trunc.S₂, Trunc.H (k i)` at `t`.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis
open SandierSerfaty.Calibration

/-! ### The monomials of `B̃₁` -/

/-- The exponent `e_i - 1` of the `i`-th monomial of `B̃₁` on the first segment. -/
@[expose] def dI (i : ℕ) : ℕ := if i = 0 then 1 else k i - 1

/-- The coefficient `v_0 = π`, `v_m = k_m a_m` of the `i`-th monomial of `B̃₁` on the first segment. -/
@[expose] noncomputable def vI (i : ℕ) : ℝ := if i = 0 then Real.pi else (k i : ℝ) * ((-1) ^ i * coeff i)

theorem eI_eq (i : ℕ) : eI i = dI i + 1 := by
  unfold eI dI
  split_ifs
  · rfl
  · have := k_pos i; omega

theorem wI_eq (t : ℝ) (i : ℕ) : wI t i = vI i * t ^ (dI i + 1) := by
  rw [← eI_eq]
  unfold wI vI eI
  split_ifs <;> ring

theorem range_modes : Finset.range (Trunc.modes + 1) = Finset.range 39 := rfl

theorem sum39 (f : ℕ → ℝ) : ∑ i ∈ Finset.range 39, f i = ∑ n ∈ Finset.range 38, f (n + 1) + f 0 :=
  Finset.sum_range_succ' f 38

theorem piece_u_zero (i : ℕ) :
    Piece.u i 0 = fun r => if i = 0 then gamma r else (-1) ^ i * coeff i * r ^ k i := by
  funext r
  simp only [Piece.u, Piece.tau, Piece.w, sub_zero, one_mul, zero_mul, add_zero, mul_one]

theorem hasDerivAt_piece_u_zero (i : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (Piece.u i 0) (vI i * r ^ dI i - if i = 0 then r⁻¹ else 0) r := by
  rw [piece_u_zero]
  by_cases hi : i = 0
  · subst hi
    have h := ((Real.hasDerivAt_log hr.ne').neg).add (((hasDerivAt_pow 2 r).const_mul Real.pi).div_const 2)
    convert h using 1
    · funext x; simp [gamma]
    · simp only [vI, dI, ite_true]; push_cast; ring
  · have h := (hasDerivAt_pow (k i) r).const_mul ((-1 : ℝ) ^ i * coeff i)
    convert h using 1
    · funext x; simp [hi]
    · simp only [vI, dI, hi, ite_false, sub_zero]; ring

theorem trunc_B₁_inner {r : ℝ} (hr : r ∈ seg 0) :
    Trunc.B₁ r = ∑ i ∈ Finset.range 39, vI i * r ^ dI i := by
  rw [trunc_B₁_eq_B1p (by norm_num) hr, B1p]
  have h : ∀ i, iteratedDeriv 1 (Piece.u i 0) r = vI i * r ^ dI i - if i = 0 then r⁻¹ else 0 := fun i => by
    rw [iteratedDeriv_one]; exact (hasDerivAt_piece_u_zero i hr.1).deriv
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_range]
  simp

theorem trunc_B_mul_inner {r : ℝ} (hr : r ∈ seg 0) : Trunc.B r * r =
    gamma r * r + ∑ n ∈ Finset.range 38, (-1) ^ (n + 1) * coeff (n + 1) * r ^ (k (n + 1) + 1) := by
  rw [trunc_B_eq_Bp (by norm_num) hr, Bp, sum39, add_mul, Finset.sum_mul, add_comm]
  congr 1
  · simp [piece_u_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    simp only [piece_u_zero, Nat.succ_ne_zero, ite_false]
    ring

/-! ### Integrals of monomials -/

theorem integral_monomials {ι : Type*} (s : Finset ι) (c : ι → ℝ) (d : ι → ℕ) (t : ℝ) :
    ∫ r in (0 : ℝ)..t, ∑ i ∈ s, c i * r ^ d i = ∑ i ∈ s, c i * (t ^ (d i + 1) / (d i + 1)) := by
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (by fun_prop : Continuous fun r : ℝ => c i * r ^ d i).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp

theorem integral_monomials₂ {ι κ : Type*} (s : Finset ι) (s' : Finset κ) (c : ι → κ → ℝ) (d : ι → κ → ℕ)
    (t : ℝ) : ∫ r in (0 : ℝ)..t, ∑ i ∈ s, ∑ j ∈ s', c i j * r ^ d i j =
      ∑ i ∈ s, ∑ j ∈ s', c i j * (t ^ (d i j + 1) / (d i j + 1)) := by
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_finsetSum _ fun j _ => (by fun_prop : Continuous fun r : ℝ => c i j * r ^ d i j)).intervalIntegrable
      _ _]
  exact Finset.sum_congr rfl fun i _ => integral_monomials s' (c i) (d i) t

theorem continuousOn_gamma_mul (t : ℝ) : ContinuousOn (fun r => gamma r * r) (Icc 0 t) := by
  have : (fun r : ℝ => gamma r * r) = fun r => -(r * Real.log r) + Real.pi / 2 * r ^ 3 := by
    funext r; unfold gamma; ring
  rw [this]
  refine Continuous.continuousOn ?_
  have h1 : Continuous fun r : ℝ => r * Real.log r := Real.continuous_mul_log
  fun_prop

/-! ### The closed forms on the first segment -/

/-- `S̃₁ = S1init` on `(0, p - c]`. -/
theorem trunc_S₁_inner {t : ℝ} (ht : t ∈ seg 0) : Trunc.S₁ t = S1init t := by
  have ht0 : 0 < t := ht.1
  have hc : ∫ r in (0 : ℝ)..t, Trunc.B r * r = ∫ r in (0 : ℝ)..t, (gamma r * r +
      ∑ n ∈ Finset.range 38, (-1) ^ (n + 1) * coeff (n + 1) * r ^ (k (n + 1) + 1)) :=
    integral_congr_Ioc ht0.le fun r hr => trunc_B_mul_inner ⟨hr.1, hr.2.trans ht.2⟩
  have hm := integral_monomials (Finset.range 38) (fun n => (-1) ^ (n + 1) * coeff (n + 1))
    (fun n => k (n + 1) + 1) t
  have i2 : IntervalIntegrable (fun r : ℝ => ∑ n ∈ Finset.range 38,
      (-1) ^ (n + 1) * coeff (n + 1) * r ^ (k (n + 1) + 1)) volume 0 t :=
    (continuous_finsetSum _ fun i _ => by fun_prop).intervalIntegrable _ _
  rw [Trunc.S₁, hc, intervalIntegral.integral_add ((continuousOn_gamma_mul t).intervalIntegrable_of_Icc ht0.le) i2,
    integral_gamma_mul ht0.le, hm, S1init]
  have hs : ∑ n ∈ Finset.range 38, (-1) ^ (n + 1) * coeff (n + 1) * (t ^ (k (n + 1) + 1 + 1) /
      (((k (n + 1) + 1 : ℕ) : ℝ) + 1)) = ∑ n ∈ Finset.range 38, (-1) ^ (n + 1) * coeff (n + 1) * t ^ k (n + 1) *
      t ^ 2 / ((k (n + 1) + 2 : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun n _ => by push_cast; ring
  rw [hs]
  ring

/-- `S̃₂ = S2init` on `(0, p - c]`. -/
theorem trunc_S₂_inner {t : ℝ} (ht : t ∈ seg 0) : Trunc.S₂ t = S2init t := by
  have ht0 : 0 < t := ht.1
  have hc : ∫ r in (0 : ℝ)..t, (-2 * Trunc.B₁ r + r * Trunc.B₁ r ^ 2) =
      ∫ r in (0 : ℝ)..t, (∑ i ∈ Finset.range 39, (-2 * vI i) * r ^ dI i +
        ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39, (vI i * vI j) * r ^ (dI i + dI j + 1)) := by
    refine integral_congr_Ioc ht0.le fun r hr => ?_
    rw [trunc_B₁_inner ⟨hr.1, hr.2.trans ht.2⟩, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  have i1 : IntervalIntegrable (fun r : ℝ => ∑ i ∈ Finset.range 39, (-2 * vI i) * r ^ dI i) volume 0 t :=
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39,
      (vI i * vI j) * r ^ (dI i + dI j + 1)) volume 0 t :=
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  rw [Trunc.S₂, hc, intervalIntegral.integral_add i1 i2, integral_monomials, integral_monomials₂, S2init]
  simp only [termSumR, wI_eq, eI_eq, Finset.sum_mul, Finset.mul_sum]
  have e1 : ∑ i ∈ Finset.range 39, -2 * vI i * (t ^ (dI i + 1) / ((dI i : ℝ) + 1)) =
      -∑ i ∈ Finset.range 39, vI i * t ^ (dI i + 1) / ((dI i + 1 + 0 : ℕ) : ℝ) * 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  have e2 : ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39, vI i * vI j * (t ^ (dI i + dI j + 1 + 1) /
      (((dI i + dI j + 1 : ℕ) : ℝ) + 1)) = ∑ i ∈ Finset.range 39, ∑ j ∈ Finset.range 39,
        vI i * t ^ (dI i + 1) * (vI j * t ^ (dI j + 1) / ((dI j + 1 + (dI i + 1) : ℕ) : ℝ)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by push_cast; ring
  rw [e1, e2]
  ring

/-- `H̃_c = Hinit c` on `(0, p - c]`. -/
theorem trunc_H_inner (c : ℕ) {t : ℝ} (ht : t ∈ seg 0) : Trunc.H c t = Hinit c t := by
  have ht0 : 0 < t := ht.1
  have hc : ∫ r in (0 : ℝ)..t, Trunc.B₁ r * r ^ c =
      ∫ r in (0 : ℝ)..t, ∑ i ∈ Finset.range 39, vI i * r ^ (dI i + c) := by
    refine integral_congr_Ioc ht0.le fun r hr => ?_
    rw [trunc_B₁_inner ⟨hr.1, hr.2.trans ht.2⟩, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Trunc.H, hc, integral_monomials, Hinit, termSumR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wI_eq, eI_eq]
  have htc : t ^ c ≠ 0 := pow_ne_zero c ht0.ne'
  have hd : ((dI i + c : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  have hd' : ((dI i + 1 + c : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show t ^ (dI i + c + 1) = t ^ (dI i + 1) * t ^ c by ring]
  push_cast at hd hd' ⊢
  field_simp
  ring

/-! ### The truncated inner identity -/

theorem D_succ_inner {t : ℝ} (ht : t ∈ seg 0) (n : ℕ) : D (n + 1) t = -(wI t (n + 1) / (k (n + 1) : ℝ)) := by
  have hk : (k (n + 1) : ℝ) ≠ 0 := by have := k_pos (n + 1); positivity
  rw [D_succ_of_le ht.2, ptm]
  simp only [wI, Nat.succ_ne_zero, ite_false, k_of_pos (Nat.succ_pos n)]
  rw [k_of_pos (Nat.succ_pos n)] at hk
  field_simp

/-- **The truncated `comp:inner-exact`**: `f̃₀ = (πt² - ½) log t - 3π²t⁴/8` on `(0, p - c]`. -/
theorem trunc_f₀_inner {t : ℝ} (ht : t ∈ seg 0) : Trunc.f₀ t = F0inner t := by
  have hk : ∀ n, (k (n + 1) : ℝ) ≠ 0 := fun n => by have := k_pos (n + 1); positivity
  have heI : ∀ n, eI (n + 1) = k (n + 1) := fun n => by simp [eI]
  have hx0 : wI t 0 = Real.pi * t ^ 2 := by simp [wI]
  have hD0 : D 0 t = 0 := D_zero_inner ht.2
  -- `S̃₁ + t² ∑ D_i/(k_i + 2)`
  have hS1 : S1init t + t ^ 2 * ∑ i ∈ Finset.range (Trunc.modes + 1), D i t / ((k i : ℝ) + 2) =
      t ^ 2 / 2 * (1 / 2 - Real.log t) + Real.pi * t ^ 4 / 8 := by
    simp only [range_modes, sum39, hD0, zero_div, add_zero, S1init, Finset.mul_sum]
    have : ∑ n ∈ Finset.range 38, (-1) ^ (n + 1) * coeff (n + 1) * t ^ k (n + 1) * t ^ 2 /
        ((k (n + 1) + 2 : ℕ) : ℝ) + ∑ n ∈ Finset.range 38, t ^ 2 * (D (n + 1) t / ((k (n + 1) : ℝ) + 2)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [D_succ_of_le ht.2, ptm, k_of_pos (Nat.succ_pos n)]
      simp only [Nat.succ_eq_add_one]
      push_cast; ring
    linear_combination this
  -- the abbreviations
  set x : ℕ → ℝ := fun i => wI t i with hxdef
  set T : ℕ → ℝ := fun c => termSumR c t with hTdef
  have hT : ∀ c, T c = x 0 / ((eI 0 + c : ℕ) : ℝ) + ∑ m ∈ Finset.range 38, x (m + 1) / ((eI (m + 1) + c : ℕ) : ℝ) :=
    fun c => by simp only [hTdef, termSumR, sum39]; ring
  have hS2 : S2init t = x 0 * T (eI 0) + ∑ n ∈ Finset.range 38, x (n + 1) * T (eI (n + 1)) - T 0 * 2 := by
    simp only [S2init, sum39, hxdef, hTdef]; ring
  have hSig : ∑ n ∈ Finset.range 38, x (n + 1) * T (eI (n + 1)) =
      x 0 * ∑ n ∈ Finset.range 38, x (n + 1) / ((eI 0 + eI (n + 1) : ℕ) : ℝ) +
        ∑ n ∈ Finset.range 38, x (n + 1) * ∑ m ∈ Finset.range 38, x (m + 1) / ((eI (m + 1) + eI (n + 1) : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [hT]; ring
  have hA : ∑ m ∈ Finset.range 38, x (m + 1) / ((eI (m + 1) + eI 0 : ℕ) : ℝ) =
      ∑ n ∈ Finset.range 38, x (n + 1) / ((eI 0 + eI (n + 1) : ℕ) : ℝ) :=
    Finset.sum_congr rfl fun n _ => by rw [Nat.add_comm (eI (n + 1)) (eI 0)]
  -- the linear terms
  have hLin : ∑ i ∈ Finset.range (Trunc.modes + 1), (-2 * D i t + 2 * (k i : ℝ) * D i t * Trunc.H (k i) t) =
      2 * ∑ n ∈ Finset.range 38, x (n + 1) / ((eI (n + 1) + 0 : ℕ) : ℝ) -
        2 * ∑ n ∈ Finset.range 38, x (n + 1) * T (eI (n + 1)) := by
    simp only [range_modes, sum39, hD0, mul_zero, zero_mul, add_zero, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [D_succ_inner ht, trunc_H_inner _ ht, Hinit, heI]
    simp only [hxdef, hTdef]
    field_simp [hk n]
    ring
  -- the quadratic terms
  have hQuad : ∑ i ∈ Finset.range (Trunc.modes + 1), ∑ j ∈ Finset.range (Trunc.modes + 1),
      (k i : ℝ) * (k j : ℝ) / ((k i : ℝ) + (k j : ℝ)) * D i t * D j t =
      ∑ n ∈ Finset.range 38, x (n + 1) * ∑ m ∈ Finset.range 38, x (m + 1) / ((eI (m + 1) + eI (n + 1) : ℕ) : ℝ) := by
    simp only [range_modes, sum39, hD0, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [D_succ_inner ht, D_succ_inner ht, heI, heI]
    simp only [hxdef]
    have hpos : (k (m + 1) : ℝ) + (k (n + 1) : ℝ) ≠ 0 := by
      have := k_pos (m + 1); have := k_pos (n + 1); positivity
    have hpos' : (k (n + 1) : ℝ) + (k (m + 1) : ℝ) ≠ 0 := by rwa [add_comm]
    push_cast
    field_simp [hk n, hk m, hpos, hpos']
    ring
  have hT0 := hT 0
  have hTe := hT (eI 0)
  have he0 : ((eI 0 + eI 0 : ℕ) : ℝ) = 4 := by simp [eI]
  have he00 : ((eI 0 + 0 : ℕ) : ℝ) = 2 := by simp [eI]
  rw [he0] at hTe
  rw [he00] at hT0
  have hx0' : x 0 = Real.pi * t ^ 2 := hx0
  rw [hx0'] at hS2 hTe hT0 hSig
  rw [Trunc.f₀, trunc_S₁_inner ht, trunc_S₂_inner ht, F0inner]
  linear_combination (-2 * Real.pi) * hS1 + (-1 / 2 : ℝ) * hS2 + (-1 / 2 : ℝ) * hLin + (-1 / 2 : ℝ) * hQuad +
    (-1 / 2 * (Real.pi * t ^ 2)) * hTe + hT0 + (1 / 2 : ℝ) * hSig + (-1 / 2 * (Real.pi * t ^ 2)) * hA

/-- `ẽ = 0` on `(0, p - c]`. -/
theorem trunc_e_inner {t : ℝ} (ht : t ∈ seg 0) : Trunc.e t = 0 := by
  have : ∀ i, Q i t = 0 := fun i => by
    cases i with
    | zero => exact Q_zero_of_le ht
    | succ m => exact Q_succ_of_le ht
  simp [Trunc.e, this]

/-! ### The first segment and the initial checkpoint enclose the truncated calibration -/

/-- **The initial checkpoint for the truncated calibration.** If `initCheck d X S = true`, `t ∈ X` and
`t ≤ p - c`, the state `S` encloses `Trunc.S₁ t`, `Trunc.S₂ t` and `Trunc.H (k i) t`. -/
theorem initCheck_sound_trunc {d : BasisData} (hd : d.Valid) {X : IV 128} {S : SState}
    (hc : initCheck d X S = true) {t : ℝ} (ht : IV.Mem t X) (htc : t ≤ p - c) :
    StateOn {t} Trunc.S₁ Trunc.S₂ TH S := by
  have h := initCheck_sound hd hc ht
  have hX : IV.posB X = true := by simp only [initCheck, Bool.and_eq_true] at hc; exact hc.1
  have hseg : t ∈ seg 0 := ⟨IV.posB_sound hX ht, htc⟩
  have e : (fun i => TH i t) = fun i => Hinit (k i) t := funext fun i => trunc_H_inner (k i) hseg
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, h.len⟩
  · rw [hx, trunc_S₁_inner hseg]; exact h.s1 t rfl
  · rw [hx, trunc_S₂_inner hseg]; exact h.s2 t rfl
  · rw [hx, e]; exact h.hs t rfl

end SandierSerfaty.Certificate.Table
