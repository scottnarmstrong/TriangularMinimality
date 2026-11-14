/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.EdgePoly
public import SandierSerfaty.Tails.JetCalc

/-!
# Derivatives of the edge polynomial in `w = r² - p²` (paper §6.2, near the edge)

`Vsum m w = ∑_j (-1)^j C(k,2j) p^{k-2j} w^j` is the polynomial of `Calibration/EdgePoly.lean`
(`V_m(r) = c_m Vsum m (r² - p²)`). This module proves, for `w ≥ 0` and `2 ℓ ≤ k = k_m`, the bound used at
paper §6.2:

`|d^ℓ Vsum / dw^ℓ (w)| ≤ k^{2ℓ} (p + √w)^{k-2ℓ}`.

* `VsumD ℓ m` is the termwise `ℓ`-th derivative (`hasDerivAt_VsumD`: it has derivative `VsumD (ℓ+1) m`);
* `EvenD ℓ n w` is its unsigned majorant, for a general degree `n`;
* `EvenD_succ_le`: `EvenD (ℓ+1) n ≤ (n(n-1)/2) EvenD ℓ (n-2)` termwise, from the Pascal-type identity
  `(2j+2)(2j+1) C(n, 2j+2) = n(n-1) C(n-2, 2j)` (the coefficient comparison of paper §6.2, one derivative at
  a time);
* `EvenD_zero_le`: the even-index part of the binomial sum is at most `(p + √w)^n`.
-/

open Finset

public section

namespace SandierSerfaty

namespace Tails

open Calibration

/-- The unsigned majorant `∑_{j ≤ n/2} C(n,2j) p^{n-2j} j^{(ℓ)} w^{j-ℓ}` of the `ℓ`-th `w`-derivative of the edge
polynomial of degree `n` (`j^{(ℓ)}` the falling factorial). -/
@[expose] noncomputable def EvenD (ℓ n : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ range (n / 2 + 1),
    (Nat.choose n (2 * j) : ℝ) * p ^ (n - 2 * j) * ((j.descFactorial ℓ : ℕ) : ℝ) * w ^ (j - ℓ)

/-- The `ℓ`-th derivative of `Vsum m` in `w`, termwise. -/
@[expose] noncomputable def VsumD (ℓ m : ℕ) (w : ℝ) : ℝ :=
  ∑ j ∈ range (k m / 2 + 1), (-1 : ℝ) ^ j *
    ((Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) * ((j.descFactorial ℓ : ℕ) : ℝ) * w ^ (j - ℓ))

theorem VsumD_zero (m : ℕ) : VsumD 0 m = Vsum m := by
  funext w
  unfold VsumD Vsum
  refine sum_congr rfl fun j _ => ?_
  simp [Nat.descFactorial_zero]
  ring

theorem hasDerivAt_VsumD (ℓ m : ℕ) (w : ℝ) : HasDerivAt (VsumD ℓ m) (VsumD (ℓ + 1) m w) w := by
  have h := HasDerivAt.fun_sum (u := range (k m / 2 + 1))
    (A := fun j w => (-1 : ℝ) ^ j * ((Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
      ((j.descFactorial ℓ : ℕ) : ℝ) * w ^ (j - ℓ)))
    (A' := fun j => (-1 : ℝ) ^ j * ((Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
      ((j.descFactorial ℓ : ℕ) : ℝ) * (((j - ℓ : ℕ) : ℝ) * w ^ (j - ℓ - 1)))) (x := w)
    (fun j _ => ((hasDerivAt_pow (j - ℓ) w).const_mul _).const_mul _)
  have e : VsumD ℓ m = fun w => ∑ j ∈ range (k m / 2 + 1), (-1 : ℝ) ^ j *
      ((Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) * ((j.descFactorial ℓ : ℕ) : ℝ) * w ^ (j - ℓ)) :=
    rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold VsumD
  refine sum_congr rfl fun j _ => ?_
  have e1 : j.descFactorial (ℓ + 1) = (j - ℓ) * j.descFactorial ℓ := Nat.descFactorial_succ j ℓ
  have e2 : j - ℓ - 1 = j - (ℓ + 1) := by omega
  rw [e1, e2]
  push_cast
  ring

theorem jet3_VsumD (m : ℕ) : Jet3 Set.univ (VsumD 0 m) (VsumD 1 m) (VsumD 2 m) (VsumD 3 m) :=
  ⟨fun x _ => hasDerivAt_VsumD 0 m x, fun x _ => hasDerivAt_VsumD 1 m x,
    fun x _ => hasDerivAt_VsumD 2 m x⟩

theorem EvenD_nonneg (ℓ n : ℕ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ EvenD ℓ n w := by
  unfold EvenD
  refine sum_nonneg fun j _ => ?_
  have := p_pos
  positivity

theorem abs_VsumD_le_EvenD (ℓ m : ℕ) {w : ℝ} (hw : 0 ≤ w) : |VsumD ℓ m w| ≤ EvenD ℓ (k m) w := by
  unfold VsumD EvenD
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun j _ => ?_))
  have := p_pos
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
  positivity

/-- The Pascal-type identity `(2j+2)(2j+1) C(n'+2, 2j+2) = (n'+2)(n'+1) C(n', 2j)`. -/
theorem choose_identity (n' j : ℕ) :
    ((2 * j + 2) * (2 * j + 1) : ℝ) * (Nat.choose (n' + 2) (2 * j + 2) : ℝ) =
      ((n' + 2) * (n' + 1) : ℝ) * (Nat.choose n' (2 * j) : ℝ) := by
  have h1 := Nat.add_one_mul_choose_eq (n' + 1) (2 * j + 1)
  have h2 := Nat.add_one_mul_choose_eq n' (2 * j)
  have h1' : ((n' : ℝ) + 2) * (Nat.choose (n' + 1) (2 * j + 1) : ℝ) =
      (Nat.choose (n' + 2) (2 * j + 2) : ℝ) * (2 * j + 2) := by exact_mod_cast h1
  have h2' : ((n' : ℝ) + 1) * (Nat.choose n' (2 * j) : ℝ) =
      (Nat.choose (n' + 1) (2 * j + 1) : ℝ) * (2 * j + 1) := by exact_mod_cast h2
  calc ((2 * j + 2) * (2 * j + 1) : ℝ) * (Nat.choose (n' + 2) (2 * j + 2) : ℝ)
      = ((n' : ℝ) + 2) * ((Nat.choose (n' + 1) (2 * j + 1) : ℝ) * (2 * j + 1)) := by
        linear_combination (2 * (j : ℝ) + 1) * (-h1')
    _ = _ := by rw [← h2']; ring

/-- Termwise comparison `(j+1) C(n'+2, 2j+2) ≤ ((n'+2)(n'+1)/2) C(n', 2j)`. -/
theorem choose_le (n' j : ℕ) :
    ((j : ℝ) + 1) * (Nat.choose (n' + 2) (2 * j + 2) : ℝ) ≤
      ((n' + 2) * (n' + 1) / 2 : ℝ) * (Nat.choose n' (2 * j) : ℝ) := by
  have h := choose_identity n' j
  have hC : (0 : ℝ) ≤ (Nat.choose (n' + 2) (2 * j + 2) : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hj (mul_nonneg hC hj), mul_nonneg hC hj]

/-- One derivative: `EvenD (ℓ+1) n ≤ (n(n-1)/2) EvenD ℓ (n-2)` for `w ≥ 0`, `n ≥ 2`. -/
theorem EvenD_succ_le (ℓ : ℕ) {n : ℕ} (hn : 2 ≤ n) {w : ℝ} (hw : 0 ≤ w) :
    EvenD (ℓ + 1) n w ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * EvenD ℓ (n - 2) w := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have hp := p_pos
  have hN : (n' + 2) / 2 = n' / 2 + 1 := by omega
  have hN2 : (n' + 2 - 2) / 2 + 1 = n' / 2 + 1 := by simp
  unfold EvenD
  rw [hN, sum_range_succ', Nat.add_sub_cancel, mul_sum]
  have h0 : (Nat.choose (n' + 2) (2 * 0) : ℝ) * p ^ (n' + 2 - 2 * 0) *
      (((0 : ℕ).descFactorial (ℓ + 1) : ℕ) : ℝ) * w ^ (0 - (ℓ + 1)) = 0 := by
    simp
  rw [h0, add_zero]
  refine sum_le_sum fun j hj => ?_
  have hjn : 2 * j + 2 ≤ n' + 2 := by
    have := mem_range.1 hj; omega
  have e1 : (j + 1).descFactorial (ℓ + 1) = (j + 1) * j.descFactorial ℓ :=
    Nat.succ_descFactorial_succ j ℓ
  have e2 : j + 1 - (ℓ + 1) = j - ℓ := by omega
  have e3 : n' + 2 - 2 * (j + 1) = n' - 2 * j := by omega
  have e4 : 2 * (j + 1) = 2 * j + 2 := by ring
  rw [e1, e2, e3, e4]
  have hkey := choose_le n' j
  have hd : (0 : ℝ) ≤ (j.descFactorial ℓ : ℝ) := Nat.cast_nonneg _
  have hw' : 0 ≤ w ^ (j - ℓ) := pow_nonneg hw _
  have hpp : 0 ≤ p ^ (n' - 2 * j) := pow_nonneg hp.le _
  push_cast
  have : ((j : ℝ) + 1) * (Nat.choose (n' + 2) (2 * j + 2) : ℝ) * (p ^ (n' - 2 * j) * (j.descFactorial ℓ : ℝ) *
      w ^ (j - ℓ)) ≤ ((n' + 2) * (n' + 1) / 2 : ℝ) * (Nat.choose n' (2 * j) : ℝ) *
        (p ^ (n' - 2 * j) * (j.descFactorial ℓ : ℝ) * w ^ (j - ℓ)) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  calc (Nat.choose (n' + 2) (2 * j + 2) : ℝ) * p ^ (n' - 2 * j) *
        (((j : ℝ) + 1) * (j.descFactorial ℓ : ℝ)) * w ^ (j - ℓ)
      = ((j : ℝ) + 1) * (Nat.choose (n' + 2) (2 * j + 2) : ℝ) * (p ^ (n' - 2 * j) *
        (j.descFactorial ℓ : ℝ) * w ^ (j - ℓ)) := by ring
    _ ≤ _ := this
    _ = _ := by ring

/-- `EvenD ℓ n ≤ n^{2ℓ} EvenD 0 (n - 2ℓ)` (`2 ℓ ≤ n`, `w ≥ 0`). -/
theorem EvenD_le_pow (ℓ : ℕ) {n : ℕ} (hn : 2 * ℓ ≤ n) {w : ℝ} (hw : 0 ≤ w) :
    EvenD ℓ n w ≤ (n : ℝ) ^ (2 * ℓ) * EvenD 0 (n - 2 * ℓ) w := by
  induction ℓ generalizing n with
  | zero => simp
  | succ ℓ ih =>
    have hn2 : 2 ≤ n := by omega
    refine (EvenD_succ_le ℓ hn2 hw).trans ?_
    have ih' := ih (n := n - 2) (by omega)
    have hcast : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    have h0 : (0 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have e : n - 2 - 2 * ℓ = n - 2 * (ℓ + 1) := by omega
    rw [e] at ih'
    have hE := EvenD_nonneg 0 (n - 2 * (ℓ + 1)) hw
    have h1 : ((n - 2 : ℕ) : ℝ) ^ (2 * ℓ) ≤ (n : ℝ) ^ (2 * ℓ) := pow_le_pow_left₀ h0 hcast _
    have h2 : (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc ((n : ℝ) * ((n : ℝ) - 1) / 2) * EvenD ℓ (n - 2) w
        ≤ (n : ℝ) ^ 2 * (((n - 2 : ℕ) : ℝ) ^ (2 * ℓ) * EvenD 0 (n - 2 * (ℓ + 1)) w) := by
          have h3 : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
            have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
            nlinarith
          calc _ ≤ ((n : ℝ) * ((n : ℝ) - 1) / 2) * (((n - 2 : ℕ) : ℝ) ^ (2 * ℓ) * EvenD 0 (n - 2 * (ℓ + 1)) w) :=
                mul_le_mul_of_nonneg_left ih' h3
            _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ (2 * ℓ) * EvenD 0 (n - 2 * (ℓ + 1)) w) := by
          gcongr
      _ = (n : ℝ) ^ (2 * (ℓ + 1)) * EvenD 0 (n - 2 * (ℓ + 1)) w := by ring

/-- The even-index part of the binomial expansion is at most the full power:
`∑_j C(n,2j) p^{n-2j} w^j ≤ (p + √w)^n`. -/
theorem EvenD_zero_le (n : ℕ) {w : ℝ} (hw : 0 ≤ w) : EvenD 0 n w ≤ (p + √w) ^ n := by
  have hp := p_pos
  have hs : 0 ≤ √w := Real.sqrt_nonneg w
  have hsq : (√w) ^ 2 = w := Real.sq_sqrt hw
  rw [add_comm, add_pow]
  unfold EvenD
  have e : ∀ j ∈ range (n / 2 + 1),
      (Nat.choose n (2 * j) : ℝ) * p ^ (n - 2 * j) * (((j.descFactorial 0 : ℕ)) : ℝ) * w ^ (j - 0) =
        (fun i : ℕ => (√w) ^ i * p ^ (n - i) * (Nat.choose n i : ℝ)) (2 * j) := by
    intro j _
    simp only [Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero, pow_mul, hsq]
    ring
  rw [sum_congr rfl e, ← Finset.sum_image (f := fun i : ℕ => (√w) ^ i * p ^ (n - i) * (Nat.choose n i : ℝ))
    (s := range (n / 2 + 1)) (g := fun j => 2 * j) (fun a _ b _ h => by simp only at h; omega)]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  rw [mem_range] at hj ⊢
  omega

/-- **Near-edge derivative bound** (paper §6.2): for `w ≥ 0` and `2 ℓ ≤ k_m`,
`|d^ℓ Vsum/dw^ℓ| ≤ k^{2ℓ} (p + √w)^{k-2ℓ}`. -/
theorem abs_VsumD_le (ℓ m : ℕ) (hℓ : 2 * ℓ ≤ k m) {w : ℝ} (hw : 0 ≤ w) :
    |VsumD ℓ m w| ≤ ((k m : ℕ) : ℝ) ^ (2 * ℓ) * (p + √w) ^ (k m - 2 * ℓ) :=
  (abs_VsumD_le_EvenD ℓ m hw).trans ((EvenD_le_pow ℓ hℓ hw).trans
    (mul_le_mul_of_nonneg_left (EvenD_zero_le _ hw) (by positivity)))

end Tails

end SandierSerfaty

end
