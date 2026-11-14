/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Coeff
public import SandierSerfaty.Calibration.Cutoff
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The edge polynomial `V_m` and the inner continuation data `T_{im}`

paper `cal:edge-polynomial` and paper §5.3.

* `Vsum m s = ∑_{j=0}^{k_m/2} (-1)^j C(k_m, 2j) p^{k_m-2j} s^j` and `V m r = c_m Vsum m (r² - p²)`,
  a polynomial in `r`, valid (as a function) for all `r`; the paper uses it on `[p, R₀]`.
* `T0 m, T1 m, T2 m` are `T_{0m}, T_{1m}, T_{2m}` of paper §5.3.
* `V_jet_p`: `V_m(p) = T_{0m}`, `V_m'(p) = T_{1m}`, `V_m''(p) = 2 T_{2m}` (paper §5.3) — the
  hypothesis for the `C²` gluing of `b_m` at `p`.
-/

open Set Finset

public section

namespace SandierSerfaty

namespace Calibration

/-- `∑_{j=0}^{k_m/2} (-1)^j C(k_m, 2j) p^{k_m-2j} s^j`; the edge polynomial is `c_m` times this at
`s = r² - p²`. -/
@[expose] noncomputable def Vsum (m : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ range (k m / 2 + 1), (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) * s ^ j

/-- The edge polynomial `V_m(r) = c_m ∑_{j=0}^{k_m/2} (-1)^j C(k_m, 2j) p^{k_m-2j} (r² - p²)^j`
(paper `cal:edge-polynomial`). -/
@[expose] noncomputable def V (m : ℕ) (r : ℝ) : ℝ := coeff m * Vsum m (r ^ 2 - p ^ 2)

/-- `T_{0m} = c_m p^{k_m}` (paper §5.3). -/
@[expose] noncomputable def T0 (m : ℕ) : ℝ := coeff m * p ^ k m

/-- `T_{1m} = -k_m (k_m - 1) T_{0m} / p` (paper §5.3). -/
@[expose] noncomputable def T1 (m : ℕ) : ℝ := -((k m : ℝ) * ((k m : ℝ) - 1)) / p * T0 m

/-- `T_{2m} = k_m (k_m - 1) p⁻² ((k_m - 2)(k_m - 3)/6 - 1/2) T_{0m}` (paper §5.3). -/
@[expose] noncomputable def T2 (m : ℕ) : ℝ :=
  (k m : ℝ) * ((k m : ℝ) - 1) / p ^ 2 *
    (((k m : ℝ) - 2) * ((k m : ℝ) - 3) / 6 - 1 / 2) * T0 m

theorem contDiff_Vsum (m : ℕ) : ContDiff ℝ ⊤ (Vsum m) := by
  unfold Vsum
  fun_prop

theorem contDiff_V (m : ℕ) : ContDiff ℝ ⊤ (V m) := by
  unfold V
  have := contDiff_Vsum m
  fun_prop

/-! ### The 2-jet of `Vsum` at `0` -/

/-- Termwise first derivative of `Vsum`. -/
noncomputable def Vsum1 (m : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ range (k m / 2 + 1), (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
    ((j : ℝ) * s ^ (j - 1))

/-- Termwise second derivative of `Vsum`. -/
noncomputable def Vsum2 (m : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ range (k m / 2 + 1), (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
    ((j : ℝ) * (((j - 1 : ℕ) : ℝ) * s ^ (j - 1 - 1)))

theorem hasDerivAt_Vsum (m : ℕ) (s : ℝ) : HasDerivAt (Vsum m) (Vsum1 m s) s := by
  have h := HasDerivAt.fun_sum (u := range (k m / 2 + 1))
    (A := fun j s => (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) * s ^ j)
    (A' := fun j => (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
      ((j : ℝ) * s ^ (j - 1))) (x := s) (fun j _ => (hasDerivAt_pow j s).const_mul _)
  have e : Vsum m = fun s => ∑ j ∈ range (k m / 2 + 1),
      (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) * s ^ j := rfl
  rw [e]
  exact h

theorem hasDerivAt_Vsum1 (m : ℕ) (s : ℝ) : HasDerivAt (Vsum1 m) (Vsum2 m s) s := by
  have h := HasDerivAt.fun_sum (u := range (k m / 2 + 1))
    (A := fun j s => (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
      ((j : ℝ) * s ^ (j - 1)))
    (A' := fun j => (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
      ((j : ℝ) * (((j - 1 : ℕ) : ℝ) * s ^ (j - 1 - 1)))) (x := s)
    (fun j _ => ((hasDerivAt_pow (j - 1) s).const_mul (j : ℝ)).const_mul _)
  have e : Vsum1 m = fun s => ∑ j ∈ range (k m / 2 + 1),
      (-1 : ℝ) ^ j * (Nat.choose (k m) (2 * j) : ℝ) * p ^ (k m - 2 * j) *
        ((j : ℝ) * s ^ (j - 1)) := rfl
  rw [e]
  exact h

theorem Vsum_zero (m : ℕ) : Vsum m 0 = p ^ k m := by
  unfold Vsum
  rw [sum_eq_single 0]
  · simp
  · intro j _ hj; simp [zero_pow hj]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem Vsum1_zero (m : ℕ) : Vsum1 m 0 = -((Nat.choose (k m) 2 : ℝ) * p ^ (k m - 2)) := by
  have h1 : 1 ∈ range (k m / 2 + 1) := Finset.mem_range.2 (by have := six_le_k m; omega)
  unfold Vsum1
  rw [sum_eq_single_of_mem 1 h1]
  · simp
  · intro j _ hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · have : j - 1 ≠ 0 := by omega
      simp [zero_pow this]

theorem Vsum2_zero (m : ℕ) :
    Vsum2 m 0 = 2 * ((Nat.choose (k m) 4 : ℝ) * p ^ (k m - 4)) := by
  have h2 : 2 ∈ range (k m / 2 + 1) := Finset.mem_range.2 (by have := six_le_k m; omega)
  unfold Vsum2
  rw [sum_eq_single_of_mem 2 h2]
  · norm_num; ring
  · intro j _ hj
    rcases (show j = 0 ∨ j = 1 ∨ 2 < j by omega) with rfl | rfl | hj2
    · simp
    · simp
    · have : j - 1 - 1 ≠ 0 := by omega
      simp [zero_pow this]

/-! ### Binomial coefficient identities -/

theorem cast_choose_two (n : ℕ) : (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rw [Nat.cast_choose_two ℝ]

theorem cast_choose_four (n : ℕ) :
    (Nat.choose n 4 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) / 24 := by
  rcases lt_or_ge n 4 with h | h
  · interval_cases n <;> simp [Nat.choose_eq_zero_of_lt]
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_choose ℝ (by omega : 4 ≤ 4 + t), show 4 + t - 4 = t by omega]
    have e : (4 + t).factorial = (4 + t) * (3 + t) * (2 + t) * (1 + t) * t.factorial := by
      rw [show 4 + t = (3 + t) + 1 by ring, Nat.factorial_succ, show 3 + t = (2 + t) + 1 by ring,
        Nat.factorial_succ, show 2 + t = (1 + t) + 1 by ring, Nat.factorial_succ,
        show 1 + t = t + 1 by ring, Nat.factorial_succ]
      ring
    have hf : (t.factorial : ℝ) ≠ 0 := by positivity
    rw [e]
    push_cast
    simp only [Nat.factorial]
    norm_num
    field_simp
    ring

/-! ### The 2-jet of `V m` at `p` -/

theorem hasDerivAt_V (m : ℕ) (r : ℝ) :
    HasDerivAt (V m) (coeff m * (Vsum1 m (r ^ 2 - p ^ 2) * (2 * r))) r := by
  have hs : HasDerivAt (fun r : ℝ => r ^ 2 - p ^ 2) (2 * r) r := by
    have := (hasDerivAt_pow 2 r).sub_const (p ^ 2)
    simpa using this
  have := ((hasDerivAt_Vsum m (r ^ 2 - p ^ 2)).comp r hs).const_mul (coeff m)
  exact this

theorem hasDerivAt_V1 (m : ℕ) (r : ℝ) :
    HasDerivAt (fun r => coeff m * (Vsum1 m (r ^ 2 - p ^ 2) * (2 * r)))
      (coeff m * (Vsum2 m (r ^ 2 - p ^ 2) * (2 * r) * (2 * r) + Vsum1 m (r ^ 2 - p ^ 2) * 2)) r := by
  have hs : HasDerivAt (fun r : ℝ => r ^ 2 - p ^ 2) (2 * r) r := by
    have := (hasDerivAt_pow 2 r).sub_const (p ^ 2)
    simpa using this
  have h1 := ((hasDerivAt_Vsum1 m (r ^ 2 - p ^ 2)).comp r hs)
  have h2 : HasDerivAt (fun r : ℝ => 2 * r) 2 r := by simpa using (hasDerivAt_id r).const_mul 2
  have := (h1.mul h2).const_mul (coeff m)
  refine this.congr_deriv ?_
  simp

theorem deriv_V (m : ℕ) : deriv (V m) = fun r => coeff m * (Vsum1 m (r ^ 2 - p ^ 2) * (2 * r)) :=
  funext fun r => (hasDerivAt_V m r).deriv

theorem deriv_deriv_V (m : ℕ) :
    deriv (deriv (V m)) = fun r => coeff m *
      (Vsum2 m (r ^ 2 - p ^ 2) * (2 * r) * (2 * r) + Vsum1 m (r ^ 2 - p ^ 2) * 2) := by
  rw [deriv_V]
  exact funext fun r => (hasDerivAt_V1 m r).deriv

theorem V_p (m : ℕ) : V m p = T0 m := by
  simp [V, T0, Vsum_zero]

theorem deriv_V_p (m : ℕ) : deriv (V m) p = T1 m := by
  have hp := p_pos
  have h2 : 2 ≤ k m := by have := six_le_k m; omega
  rw [deriv_V]
  simp only [sub_self, Vsum1_zero, T1, T0, cast_choose_two]
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h2
  have e : p ^ (k m - 2) * p ^ 2 = p ^ k m := by rw [← pow_add]; congr 1; omega
  have e' : (p ^ (k m - 2)) = p ^ k m / p ^ 2 := by rw [← e]; field_simp
  rw [e']
  field_simp

theorem deriv_deriv_V_p (m : ℕ) : deriv (deriv (V m)) p = 2 * T2 m := by
  have hp := p_pos
  have h4 : 4 ≤ k m := by have := six_le_k m; omega
  rw [deriv_deriv_V]
  simp only [sub_self, Vsum1_zero, Vsum2_zero, T2, T0, cast_choose_two, cast_choose_four]
  have e : p ^ (k m - 4) * p ^ 4 = p ^ k m := by rw [← pow_add]; congr 1; omega
  have e2 : p ^ (k m - 2) * p ^ 2 = p ^ k m := by rw [← pow_add]; congr 1; omega
  have e' : (p ^ (k m - 4)) = p ^ k m / p ^ 4 := by rw [← e]; field_simp
  have e2' : (p ^ (k m - 2)) = p ^ k m / p ^ 2 := by rw [← e2]; field_simp
  rw [e', e2']
  field_simp
  ring

end Calibration

end SandierSerfaty
