/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Rows
public import SandierSerfaty.Sphere.Ring.Slab

/-!
# The exact ring identity (sphere note, Definition 5.3, Proposition 5.5)

For a row configuration with `n = ∑ N_k` points, the partial sums `A_k = ∑_{j<k} N_j`, the mass slabs
`I_k = {t : A_k ≤ Φ(t) ≤ A_{k+1}} = [τ(A_k), τ(A_{k+1})]`, the cell terms
`Cell_k = ∫_{I_k} (N_k 1_{t ≥ t_k} - ν([τ(A_k), t]))² dt` (with `ν([τ(A_k), t]) = Φ(t) - A_k`), the
local aspects `x_k = N_k² / ϱ(t_k)` and `B_k = -(N_k/2) log x_k + Cell_k + ∑_{l ≠ k} X_{kl}`
(Definition 5.3; rows indexed from `0`):

* `Sphere.RowConfig.configEnergy_eq_ring`: if every `N_k > 0` and every `t_k` lies in the interior of
  its slab, then `E = (½ - log 2) n² - (n/2) log n + (n/2) log 2 + ∑_k B_k` (Proposition 5.5; the
  phases are arbitrary);
* `Sphere.RowConfig.IsSlabBarycentric`: the heights are the `ν`-barycentres of the slabs.

The identity holds for every choice of `t_k` in the interior of `I_k`: in the sphere note's proof the
Jensen terms cancel exactly, and that cancellation does not use the barycentre property. The
continuum facts of Lemma 5.4 are replaced by the explicit primitive of `(Φ - c)²` (`Sphere.integral_slab`)
and the telescoping of its boundary values.
-/

open Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `∑_{k,l<K} N_k N_l |t_k - t_l| = 2 ∑_k N_k (A_k + A_{k+1}) t_k - 2 A_K ∑_k N_k t_k` for
nondecreasing heights. -/
theorem sum_sum_mul_abs_sub (N t : ℕ → ℝ) : ∀ K : ℕ, (∀ k l, k < l → l < K → t k ≤ t l) →
    ∑ k ∈ range K, ∑ l ∈ range K, N k * N l * |t k - t l| =
      2 * ∑ k ∈ range K, N k * ((∑ j ∈ range k, N j) + ∑ j ∈ range (k + 1), N j) * t k -
        2 * (∑ j ∈ range K, N j) * ∑ k ∈ range K, N k * t k
  | 0, _ => by simp
  | K + 1, ht => by
    have ih := sum_sum_mul_abs_sub N t K (fun k l hkl hl => ht k l hkl (by omega))
    have hcol : ∑ k ∈ range K, N k * N K * |t k - t K| =
        N K * t K * (∑ j ∈ range K, N j) - N K * ∑ k ∈ range K, N k * t k := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k hk => ?_
      rw [abs_of_nonpos (sub_nonpos.2 (ht k K (mem_range.1 hk) (by omega)))]
      ring
    have hrow : ∑ l ∈ range K, N K * N l * |t K - t l| =
        N K * t K * (∑ j ∈ range K, N j) - N K * ∑ k ∈ range K, N k * t k := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun l hl => ?_
      rw [abs_of_nonneg (sub_nonneg.2 (ht l K (mem_range.1 hl) (by omega)))]
      ring
    have hsplit : ∑ k ∈ range (K + 1), ∑ l ∈ range (K + 1), N k * N l * |t k - t l| =
        ∑ k ∈ range K, ∑ l ∈ range K, N k * N l * |t k - t l| +
          ∑ k ∈ range K, N k * N K * |t k - t K| + ∑ l ∈ range K, N K * N l * |t K - t l| := by
      have e : ∀ k, ∑ l ∈ range (K + 1), N k * N l * |t k - t l| =
          ∑ l ∈ range K, N k * N l * |t k - t l| + N k * N K * |t k - t K| :=
        fun k => sum_range_succ _ _
      rw [sum_range_succ]
      simp only [e, sum_add_distrib, sub_self, abs_zero, mul_zero, add_zero]
    rw [hsplit, ih, hcol, hrow,
      sum_range_succ (fun k => N k * ((∑ j ∈ range k, N j) + ∑ j ∈ range (k + 1), N j) * t k),
      sum_range_succ (fun k => N k * t k), sum_range_succ N K]
    ring

namespace RowConfig

variable (R : RowConfig)

/-- The partial sums `A_k = ∑_{j<k} N_j` (`A_0 = 0`, `A_K = n`). -/
@[expose] def mass (k : ℕ) : ℕ := ∑ j ∈ range k, R.N j

theorem mass_succ (k : ℕ) : R.mass (k + 1) = R.mass k + R.N k := sum_range_succ _ _

theorem mass_K : R.mass R.K = R.card := rfl

theorem mass_mono {k l : ℕ} (h : k ≤ l) : R.mass k ≤ R.mass l :=
  sum_le_sum_of_subset (range_subset_range.2 h)

/-- The slab `I_k = {t : A_k ≤ Φ(t) ≤ A_{k+1}}` (`= [τ(A_k), τ(A_{k+1})]`, with `τ(0) = -∞`,
`τ(n) = +∞`). -/
@[expose] noncomputable def slab (k : ℕ) : Set ℝ :=
  {t | (R.mass k : ℝ) ≤ ringMass R.card t ∧ ringMass R.card t ≤ R.mass (k + 1)}

/-- The cell term `Cell_k = ∫_{I_k} (N_k 1_{t ≥ t_k} - ν([τ(A_k), t]))² dt`, with
`ν([τ(A_k), t]) = Φ(t) - A_k`. -/
@[expose] noncomputable def cell (k : ℕ) : ℝ :=
  ∫ t in R.slab k, ((if R.t k ≤ t then (R.N k : ℝ) else 0) - (ringMass R.card t - R.mass k)) ^ 2

/-- The local aspect `x_k = N_k² / ϱ(t_k)`. -/
@[expose] noncomputable def aspect (k : ℕ) : ℝ := (R.N k : ℝ) ^ 2 / ringDensity R.card (R.t k)

/-- `B_k = -(N_k/2) log x_k + Cell_k + ∑_{l ≠ k} X_{kl}`. -/
@[expose] noncomputable def rowB (k : ℕ) : ℝ :=
  -((R.N k : ℝ) / 2 * Real.log (R.aspect k)) + R.cell k + ∑ l ∈ (range R.K).erase k, R.X k l

/-- A **slab-barycentric** row configuration (Definition 5.3): nonempty rows whose heights are the
barycentres `t_k = N_k⁻¹ ∫_{I_k} t dν(t)`. -/
@[expose] def IsSlabBarycentric : Prop :=
  (∀ k < R.K, 0 < R.N k) ∧
    ∀ k < R.K, R.t k = (R.N k : ℝ)⁻¹ * ∫ s in R.slab k, s * ringDensity R.card s

theorem cell_eq (k : ℕ) (hk : k < R.K) (hN : 0 < R.N k)
    (hin : (R.mass k : ℝ) ≤ ringMass R.card (R.t k) ∧ ringMass R.card (R.t k) ≤ R.mass (k + 1)) :
    R.cell k = cellPrimitive R.card (R.card / 2 - R.mass k) (R.t k) -
        cellPrimitive R.card (R.card / 2 - R.mass (k + 1)) (R.t k) +
      cellBoundary R.card (R.mass (k + 1)) - cellBoundary R.card (R.mass k) := by
  have hNk : (R.N k : ℝ) = (R.mass (k + 1) : ℝ) - R.mass k := by
    rw [mass_succ]; push_cast; ring
  have hn : 0 < (R.card : ℝ) := by
    have : R.mass (k + 1) ≤ R.card := R.mass_mono (by omega)
    rw [mass_succ] at this
    exact_mod_cast (show 0 < R.card by omega)
  rw [cell, slab, hNk]
  exact integral_slab hn (Nat.cast_nonneg _) (by rw [mass_succ]; push_cast; exact_mod_cast
    (show (R.mass k : ℝ) < R.mass k + R.N k by exact_mod_cast (by omega : R.mass k < R.mass k + R.N k)))
    (by exact_mod_cast R.mass_mono (by omega : k + 1 ≤ R.K)) hin.1 hin.2

theorem sum_cell (hN : ∀ k < R.K, 0 < R.N k) (hK : 0 < R.K)
    (hin : ∀ k < R.K,
      (R.mass k : ℝ) ≤ ringMass R.card (R.t k) ∧ ringMass R.card (R.t k) ≤ R.mass (k + 1)) :
    ∑ k ∈ range R.K, R.cell k =
      ∑ k ∈ range R.K, (R.N k : ℝ) * ((R.card : ℝ) - R.mass k - R.mass (k + 1)) * R.t k +
        (R.card : ℝ) * ∑ k ∈ range R.K, (R.N k : ℝ) * Real.log (Real.cosh (R.t k)) +
        ((R.card : ℝ) ^ 2 * Real.log 2 - (R.card : ℝ) ^ 2 / 2) := by
  have hn : 0 < R.card := by
    have : R.mass 1 ≤ R.card := R.mass_mono hK
    rw [mass_succ] at this
    have := hN 0 hK
    omega
  rw [sum_congr rfl fun k hk => R.cell_eq k (mem_range.1 hk) (hN k (mem_range.1 hk))
    (hin k (mem_range.1 hk))]
  have htel : ∑ k ∈ range R.K, (cellBoundary R.card (R.mass (k + 1)) - cellBoundary R.card (R.mass k)) =
      (R.card : ℝ) ^ 2 * Real.log 2 - (R.card : ℝ) ^ 2 / 2 := by
    rw [sum_range_sub (fun k => cellBoundary R.card (R.mass k)), mass_K]
    have h0 : ((R.mass 0 : ℕ) : ℝ) = 0 := by simp [mass]
    have hn' : (R.card : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [h0, cellBoundary, cellBoundary, ite_eq_right hn', ite_eq_left rfl, ite_eq_left rfl]
    ring
  have hterm : ∀ k ∈ range R.K,
      cellPrimitive R.card (R.card / 2 - R.mass k) (R.t k) -
          cellPrimitive R.card (R.card / 2 - R.mass (k + 1)) (R.t k) +
        cellBoundary R.card (R.mass (k + 1)) - cellBoundary R.card (R.mass k) =
      ((R.N k : ℝ) * ((R.card : ℝ) - R.mass k - R.mass (k + 1)) * R.t k +
        (R.card : ℝ) * ((R.N k : ℝ) * Real.log (Real.cosh (R.t k)))) +
        (cellBoundary R.card (R.mass (k + 1)) - cellBoundary R.card (R.mass k)) := by
    intro k _
    have hm : ((R.mass (k + 1) : ℕ) : ℝ) = R.mass k + R.N k := by rw [mass_succ]; push_cast; ring
    rw [cellPrimitive, cellPrimitive, hm]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, htel, ← mul_sum]

/-- **Proposition 5.5 (exact ring identity)**, for heights in the interiors of their slabs: if every
row is nonempty and `A_k < Φ(t_k) < A_{k+1}`, then
`E = (½ - log 2) n² - (n/2) log n + (n/2) log 2 + ∑_k B_k`, for any phases. -/
theorem configEnergy_eq_ring (hN : ∀ k < R.K, 0 < R.N k)
    (hin : ∀ k < R.K,
      (R.mass k : ℝ) < ringMass R.card (R.t k) ∧ ringMass R.card (R.t k) < R.mass (k + 1)) :
    configEnergy R.points =
      (1 / 2 - Real.log 2) * (R.card : ℝ) ^ 2 - (R.card : ℝ) / 2 * Real.log R.card +
        (R.card : ℝ) / 2 * Real.log 2 + ∑ k ∈ range R.K, R.rowB k := by
  rcases Nat.eq_zero_or_pos R.K with hK | hK
  · have hc : R.card = 0 := by simp [card, hK]
    rw [configEnergy_eq_sum]
    have : IsEmpty (Σ k : Fin R.K, Fin (R.N k)) := by
      rw [hK]; infer_instance
    simp [hc, hK]
  have hn : 0 < R.card := by
    have : R.mass 1 ≤ R.card := R.mass_mono hK
    rw [mass_succ] at this
    have := hN 0 hK
    omega
  have hn' : (0 : ℝ) < R.card := by exact_mod_cast hn
  have hmono := ringMass_strictMono hn'
  -- strictly increasing heights
  have hlt : ∀ k l, k < l → l < R.K → R.t k < R.t l := by
    intro k l hkl hl
    have h1 := (hin k (by omega)).2
    have h2 := (hin l hl).1
    have h3 : (R.mass (k + 1) : ℝ) ≤ R.mass l := by exact_mod_cast R.mass_mono (by omega)
    exact hmono.lt_iff_lt.1 (by linarith)
  have hne : ∀ k < R.K, ∀ l < R.K, k ≠ l → R.t k ≠ R.t l := by
    intro k hk l hl hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact (hlt k l h hl).ne
    · exact (hlt l k h hk).ne'
  rw [R.configEnergy_points hN hne]
  -- the cells
  have hcell := R.sum_cell hN hK fun k hk => ⟨(hin k hk).1.le, (hin k hk).2.le⟩
  -- the ordering identity
  have habs := sum_sum_mul_abs_sub (fun k => (R.N k : ℝ)) R.t R.K
    (fun k l hkl hl => (hlt k l hkl hl).le)
  have hA : ∀ k, (∑ j ∈ range k, (R.N j : ℝ)) = R.mass k := fun k => by simp [mass]
  simp only [hA] at habs
  rw [R.mass_K] at habs
  -- the logarithms of the aspects
  have hlog : ∀ k ∈ range R.K, (R.N k : ℝ) / 2 * Real.log (R.aspect k) =
      (R.N k : ℝ) * Real.log (R.N k) - (R.N k : ℝ) / 2 * (Real.log R.card - Real.log 2) +
        (R.N k : ℝ) * Real.log (Real.cosh (R.t k)) := by
    intro k hk
    have hNk : (0 : ℝ) < R.N k := by exact_mod_cast hN k (mem_range.1 hk)
    have hc := Real.cosh_pos (R.t k)
    rw [aspect, ringDensity, Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_div (by positivity) (by positivity), Real.log_div hn'.ne' two_ne_zero,
      Real.log_pow]
    push_cast
    ring
  have hB : ∑ k ∈ range R.K, R.rowB k =
      -∑ k ∈ range R.K, (R.N k : ℝ) * Real.log (R.N k) +
        (R.card : ℝ) / 2 * (Real.log R.card - Real.log 2) -
        ∑ k ∈ range R.K, (R.N k : ℝ) * Real.log (Real.cosh (R.t k)) +
        ∑ k ∈ range R.K, R.cell k + ∑ k ∈ range R.K, ∑ l ∈ (range R.K).erase k, R.X k l := by
    unfold rowB
    rw [sum_add_distrib, sum_add_distrib, sum_neg_distrib, sum_congr rfl hlog, sum_add_distrib,
      sum_sub_distrib, ← sum_mul, ← sum_div]
    unfold card
    push_cast
    ring
  rw [hB, hcell, habs]
  have hsum : ∑ k ∈ range R.K, (R.N k : ℝ) * ((R.card : ℝ) - R.mass k - R.mass (k + 1)) * R.t k =
      (R.card : ℝ) * ∑ k ∈ range R.K, (R.N k : ℝ) * R.t k -
        ∑ k ∈ range R.K, (R.N k : ℝ) * ((R.mass k : ℝ) + R.mass (k + 1)) * R.t k := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hsum]
  ring

end RowConfig

end Sphere

end SandierSerfaty

end
