/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shells of `ℤ²` and the tail of the triangular lattice sums (paper `tail:coefficient-square`)

A point of the triangular lattice is `z = a (n + q/2 + i √3 q/2)` with `(n, q) ∈ ℤ²`, and
`|z/a|² = n² + n q + q²` (`hexNorm`, paper §6.1). This module is the integer part of `tail:coefficients`:

* `norm_lower`: `n² + n q + q² ≥ (3/4) max(|n|, |q|)²` (paper §6.1);
* `card_shell`: there are `8 v` integer pairs with `max(|n|, |q|) = v` (paper §6.1);
* `coefficient_square` (`tail:coefficient-square`): for `d = 6 m ≥ 6` and a positive integer `D`,
  `∑_{max(|n|,|q|) > D} (n² + n q + q²)^{-d/2} ≤ 8 (4/3)^{d/2} D^{2-d} / (d - 2)`
  (the sum before multiplication by `a^{-d}`), together with its summability;
* `sum_inv_pow_Ioc_le`: the comparison `∑_{v > D} v^{1-d} ≤ D^{2-d}/(d-2)` of paper §6.1, by telescoping
  (equivalent to the integral comparison, with the convexity step proved by Bernoulli's inequality).

The weights are written `hexTerm m x = (n² + n q + q²)^{-3 m}` (`d/2 = 3 m`); at the origin the value is `0`.
-/

open Finset

public section

namespace SandierSerfaty

namespace Tails

/-- The integer form `n² + n q + q²` (`|n + q ρ|²`, `ρ = e^{iπ/3}`; paper §6.1). -/
@[expose] def hexNorm (x : ℤ × ℤ) : ℤ := x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2

/-- `max (|n|, |q|)`, the index of the square shell of `(n, q)`. -/
@[expose] def supIdx (x : ℤ × ℤ) : ℕ := max x.1.natAbs x.2.natAbs

/-- The closed square `|n|, |q| ≤ V`. -/
@[expose] def box (V : ℕ) : Finset (ℤ × ℤ) := Icc (-(V : ℤ)) V ×ˢ Icc (-(V : ℤ)) V

/-- The shell `max (|n|, |q|) = V` (for `V ≥ 1`). -/
@[expose] def shell (V : ℕ) : Finset (ℤ × ℤ) := box V \ box (V - 1)

/-- The weight `(n² + n q + q²)^{-3 m} = |z/a|^{-6 m}` of the lattice sums (zero at the origin). -/
@[expose] noncomputable def hexTerm (m : ℕ) (x : ℤ × ℤ) : ℝ := (((hexNorm x : ℤ) : ℝ) ^ (3 * m))⁻¹

/-- The factor `(4/3)^{d/2}` for `d = 6 m`. -/
@[expose] noncomputable def shellK (m : ℕ) : ℝ := (4 / 3 : ℝ) ^ (3 * m)

theorem mem_box {V : ℕ} {x : ℤ × ℤ} : x ∈ box V ↔ supIdx x ≤ V := by
  simp only [box, mem_product, mem_Icc, supIdx, max_le_iff]
  omega

theorem mem_shell {V : ℕ} (hV : 1 ≤ V) {x : ℤ × ℤ} : x ∈ shell V ↔ supIdx x = V := by
  simp only [shell, mem_sdiff, mem_box]
  omega

theorem card_box (V : ℕ) : (box V).card = (2 * V + 1) ^ 2 := by
  simp only [box, card_product, Int.card_Icc]
  have : (↑V + 1 - -(V : ℤ)).toNat = 2 * V + 1 := by omega
  rw [this]; ring

theorem box_mono {V W : ℕ} (h : V ≤ W) : box V ⊆ box W := fun x hx => by
  rw [mem_box] at hx ⊢; omega

/-- There are `8 v` integer pairs with `max (|n|, |q|) = v` (paper §6.1). -/
theorem card_shell {V : ℕ} (hV : 1 ≤ V) : (shell V).card = 8 * V := by
  rw [shell, card_sdiff_of_subset (box_mono (Nat.sub_le V 1)), card_box, card_box]
  obtain ⟨W, rfl⟩ := Nat.exists_eq_add_of_le hV
  have : 1 + W - 1 = W := by omega
  rw [this]
  have h2 : (2 * (1 + W) + 1) ^ 2 = (2 * W + 1) ^ 2 + 8 * (1 + W) := by ring
  omega

/-- `n² + n q + q² ≥ (3/4) max(|n|, |q|)²` (paper §6.1), in integers. -/
theorem three_mul_supIdx_sq_le (x : ℤ × ℤ) : 3 * (supIdx x : ℤ) ^ 2 ≤ 4 * hexNorm x := by
  obtain ⟨n, q⟩ := x
  simp only [supIdx, hexNorm]
  rcases le_total n.natAbs q.natAbs with h | h
  · rw [max_eq_right h]
    have : ((q.natAbs : ℕ) : ℤ) ^ 2 = q ^ 2 := by simp
    rw [this]; nlinarith [sq_nonneg (2 * n + q)]
  · rw [max_eq_left h]
    have : ((n.natAbs : ℕ) : ℤ) ^ 2 = n ^ 2 := by simp
    rw [this]; nlinarith [sq_nonneg (2 * q + n)]

theorem norm_lower (x : ℤ × ℤ) : (3 / 4 : ℝ) * (supIdx x : ℝ) ^ 2 ≤ ((hexNorm x : ℤ) : ℝ) := by
  have := three_mul_supIdx_sq_le x
  have h : (3 : ℝ) * (supIdx x : ℝ) ^ 2 ≤ 4 * ((hexNorm x : ℤ) : ℝ) := by exact_mod_cast this
  linarith

theorem hexNorm_nonneg (x : ℤ × ℤ) : 0 ≤ hexNorm x := by
  have := three_mul_supIdx_sq_le x
  nlinarith [sq_nonneg (supIdx x : ℤ)]

theorem hexTerm_nonneg (m : ℕ) (x : ℤ × ℤ) : 0 ≤ hexTerm m x := by
  unfold hexTerm
  have : (0 : ℝ) ≤ ((hexNorm x : ℤ) : ℝ) := by exact_mod_cast hexNorm_nonneg x
  positivity

/-- On the shell `max = v ≥ 1` each weight is at most `(4/3)^{3m} v^{-6m}`. -/
theorem hexTerm_le_of_mem_shell {m V : ℕ} (hV : 1 ≤ V) {x : ℤ × ℤ} (hx : x ∈ shell V) :
    hexTerm m x ≤ shellK m * (((V : ℝ) ^ (6 * m)))⁻¹ := by
  rw [mem_shell hV] at hx
  have h := norm_lower x
  rw [hx] at h
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hpos : (0 : ℝ) < (3 / 4 : ℝ) * (V : ℝ) ^ 2 := by positivity
  unfold hexTerm shellK
  have h1 : ((3 / 4 : ℝ) * (V : ℝ) ^ 2) ^ (3 * m) ≤ (((hexNorm x : ℤ) : ℝ)) ^ (3 * m) :=
    pow_le_pow_left₀ hpos.le h _
  have h2 : (((hexNorm x : ℤ) : ℝ) ^ (3 * m))⁻¹ ≤ (((3 / 4 : ℝ) * (V : ℝ) ^ 2) ^ (3 * m))⁻¹ :=
    inv_anti₀ (by positivity) h1
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, show 2 * (3 * m) = 6 * m by ring, mul_inv, ← inv_pow]
  congr 1
  rw [inv_div]

/-- The sum over a shell: at most `8 (4/3)^{3m} v^{1-6m}` (paper §6.1). -/
theorem sum_shell_le {m V : ℕ} (hm : 1 ≤ m) (hV : 1 ≤ V) :
    ∑ x ∈ shell V, hexTerm m x ≤ 8 * shellK m * (((V : ℝ) ^ (6 * m - 1)))⁻¹ := by
  have h := Finset.sum_le_card_nsmul (shell V) (hexTerm m)
    (shellK m * (((V : ℝ) ^ (6 * m)))⁻¹) (fun x hx => hexTerm_le_of_mem_shell hV hx)
  rw [card_shell hV, nsmul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have e : (V : ℝ) ^ (6 * m) = (V : ℝ) ^ (6 * m - 1) * V := by
    rw [← pow_succ]; congr 1; omega
  rw [e, mul_inv]
  push_cast
  field_simp

/-! ### The comparison `∑_{v > D} v^{1-d} ≤ D^{2-d}/(d-2)` by telescoping -/

/-- Bernoulli-type inequality `x^{e+1} + (e+1) x^e ≤ (x+1)^{e+1}` for `x ≥ 0`. -/
theorem pow_add_le_add_one_pow {x : ℝ} (hx : 0 ≤ x) (e : ℕ) :
    x ^ (e + 1) + ((e : ℝ) + 1) * x ^ e ≤ (x + 1) ^ (e + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hy : 0 ≤ x ^ e := pow_nonneg hx e
    have h1 : (x + 1) * (x ^ (e + 1) + ((e : ℝ) + 1) * x ^ e) ≤ (x + 1) * (x + 1) ^ (e + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : x ^ (e + 1 + 1) + (((e + 1 : ℕ) : ℝ) + 1) * x ^ (e + 1) ≤
        (x + 1) * (x ^ (e + 1) + ((e : ℝ) + 1) * x ^ e) := by
      push_cast
      rw [pow_succ x (e + 1), pow_succ x e]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) + 1) hy]
    calc _ ≤ _ := h2
      _ ≤ _ := h1
      _ = _ := by ring

/-- One telescoping step: `e (x+1)^{-(e+1)} ≤ x^{-e} - (x+1)^{-e}` for `x > 0`. -/
theorem step_inv_pow_le {x : ℝ} (hx : 0 < x) (e : ℕ) :
    (e : ℝ) * (((x + 1) ^ (e + 1)))⁻¹ ≤ (x ^ e)⁻¹ - ((x + 1) ^ e)⁻¹ := by
  have key := pow_add_le_add_one_pow hx.le e
  have hA : 0 < x ^ e := by positivity
  have hB : 0 < (x + 1) ^ e := by positivity
  have e1 : (x + 1) ^ (e + 1) = (x + 1) * (x + 1) ^ e := by rw [pow_succ]; ring
  have e2 : x ^ (e + 1) = x * x ^ e := by rw [pow_succ]; ring
  rw [e1] at key ⊢
  rw [e2] at key
  rw [← sub_nonneg]
  have : (x ^ e)⁻¹ - ((x + 1) ^ e)⁻¹ - (e : ℝ) * ((x + 1) * (x + 1) ^ e)⁻¹ =
      ((x + 1) * (x + 1) ^ e - x ^ e * (x + (e : ℝ) + 1)) /
        (x ^ e * (x + 1) * (x + 1) ^ e) := by
    field_simp
    ring
  rw [this]
  apply div_nonneg
  · nlinarith
  · positivity

/-- `∑_{D < v ≤ V} v^{-(e+1)} ≤ (D^{-e} - V^{-e})/e` (paper §6.1), for `e ≥ 1`, `D ≥ 1`. -/
theorem sum_inv_pow_Ioc_le {e : ℕ} (he : 1 ≤ e) {D : ℕ} (hD : 1 ≤ D) {V : ℕ} (hV : D ≤ V) :
    ∑ v ∈ Ioc D V, (((v : ℝ) ^ (e + 1)))⁻¹ ≤ ((((D : ℝ) ^ e)⁻¹ - (((V : ℝ) ^ e))⁻¹)) / e := by
  have hepos : (0 : ℝ) < e := by exact_mod_cast he
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hV ih =>
    rw [Finset.sum_Ioc_succ_top hV]
    have hVpos : (0 : ℝ) < V := by exact_mod_cast (hD.trans hV)
    have h := step_inv_pow_le hVpos e
    have h' : (((V + 1 : ℕ) : ℝ) ^ (e + 1))⁻¹ ≤ ((V : ℝ) ^ e)⁻¹ / e - (((V : ℝ) + 1) ^ e)⁻¹ / e := by
      push_cast
      rw [← sub_div, le_div_iff₀ hepos]
      linarith
    push_cast at h' ⊢
    calc _ ≤ ((((D : ℝ) ^ e)⁻¹ - (((V : ℝ) ^ e))⁻¹)) / e +
          (((V : ℝ) ^ e)⁻¹ / e - (((V : ℝ) + 1) ^ e)⁻¹ / e) := add_le_add ih h'
      _ = _ := by ring

/-- `∑_{v > D} v^{1-d} ≤ D^{2-d}/(d-2)`, with `d = e + 2` (paper §6.1). -/
theorem sum_inv_pow_Ioc_le' {e : ℕ} (he : 1 ≤ e) {D : ℕ} (hD : 1 ≤ D) {V : ℕ} (hV : D ≤ V) :
    ∑ v ∈ Ioc D V, (((v : ℝ) ^ (e + 1)))⁻¹ ≤ (((D : ℝ) ^ e)⁻¹) / e := by
  refine (sum_inv_pow_Ioc_le he hD hV).trans ?_
  have hepos : (0 : ℝ) < e := by exact_mod_cast he
  have : (0 : ℝ) ≤ (((V : ℝ) ^ e))⁻¹ := by positivity
  gcongr
  linarith

/-! ### Finite sums over `box V \ box D` -/

theorem sum_box_sdiff_le {m D : ℕ} (hm : 1 ≤ m) {V : ℕ} (hV : D ≤ V) :
    ∑ x ∈ box V \ box D, hexTerm m x ≤
      8 * shellK m * ∑ v ∈ Ioc D V, (((v : ℝ) ^ (6 * m - 1)))⁻¹ := by
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hV ih =>
    have hV1 : 1 ≤ V + 1 := by omega
    have hsets : box (V + 1) \ box D = (box V \ box D) ∪ shell (V + 1) := by
      ext x
      simp only [mem_sdiff, mem_union, shell, Nat.add_sub_cancel, mem_box]
      omega
    have hdisj : Disjoint (box V \ box D) (shell (V + 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [shell, Nat.add_sub_cancel, mem_sdiff] at hx hx'
      exact hx'.2 hx.1
    rw [hsets, Finset.sum_union hdisj, Finset.sum_Ioc_succ_top hV, mul_add]
    exact add_le_add ih (by
      have := sum_shell_le (m := m) hm hV1
      push_cast at this ⊢
      exact this)

/-- The tail weight: `(n² + n q + q²)^{-3m}` for `max(|n|, |q|) > D`, and `0` inside the square. -/
@[expose] noncomputable def tailTerm (m D : ℕ) (x : ℤ × ℤ) : ℝ :=
  if D < supIdx x then hexTerm m x else 0

theorem tailTerm_nonneg (m D : ℕ) (x : ℤ × ℤ) : 0 ≤ tailTerm m D x := by
  unfold tailTerm; split_ifs
  · exact hexTerm_nonneg m x
  · exact le_rfl

theorem sum_box_tailTerm {m D V : ℕ} (hV : D ≤ V) :
    ∑ x ∈ box V, tailTerm m D x = ∑ x ∈ box V \ box D, hexTerm m x := by
  rw [← Finset.sum_sdiff (box_mono hV) (f := tailTerm m D)]
  have h0 : ∑ x ∈ box D, tailTerm m D x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [mem_box] at hx
    simp [tailTerm, not_lt.2 hx]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  have : ¬ supIdx x ≤ D := by
    have := (mem_sdiff.1 hx).2
    rwa [mem_box] at this
  simp [tailTerm, not_le.1 this]

theorem exists_box_superset (s : Finset (ℤ × ℤ)) (D : ℕ) : ∃ V, D ≤ V ∧ s ⊆ box V :=
  ⟨max D (s.sup supIdx), le_max_left _ _, fun x hx => by
    rw [mem_box]
    exact (Finset.le_sup (f := supIdx) hx).trans (le_max_right _ _)⟩

/-- **`tail:coefficient-square`**. For `d = 6 m ≥ 6` and a positive integer `D` the sum of
`(n² + n q + q²)^{-d/2}` over the pairs outside the square `|n|, |q| ≤ D` (before multiplication by `a^{-d}`)
is summable and at most `8 (4/3)^{d/2} D^{2-d}/(d-2)`; here `d/2 = 3 m`, `D^{2-d} = (D^{6m-2})⁻¹`. -/
theorem coefficient_square {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    Summable (tailTerm m D) ∧
      ∑' x, tailTerm m D x ≤ 8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) := by
  have he : 1 ≤ 6 * m - 2 := by omega
  have hbound : ∀ s : Finset (ℤ × ℤ), ∑ x ∈ s, tailTerm m D x ≤
      8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) := by
    intro s
    obtain ⟨V, hDV, hsV⟩ := exists_box_superset s D
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsV (fun x _ _ => tailTerm_nonneg m D x)).trans ?_
    rw [sum_box_tailTerm hDV]
    refine (sum_box_sdiff_le hm hDV).trans ?_
    have e1 : 6 * m - 1 = (6 * m - 2) + 1 := by omega
    have hK : 0 ≤ shellK m := by unfold shellK; positivity
    rw [e1, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sum_inv_pow_Ioc_le' he hD hDV) (by positivity)
  exact ⟨summable_of_sum_le (fun x => tailTerm_nonneg m D x) hbound,
    Real.tsum_le_of_sum_le (fun x => tailTerm_nonneg m D x) hbound⟩

end Tails

end SandierSerfaty

end
