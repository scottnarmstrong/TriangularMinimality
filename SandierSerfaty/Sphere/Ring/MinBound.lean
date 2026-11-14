/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.UpperBound
public import SandierSerfaty.Sphere.Minimizer

/-!
# The upper bound for minimizers (sphere note, Theorem 5.13, the `E_log` form)

* `Sphere.IsSphereMinimizer.normalizedEnergy_le`: a minimizer has `𝔎` at most that of any
  configuration of distinct points of `S²`; `Sphere.IsSphereMinimizer.normalizedEnergy_le_ringConfig`:
  in particular at most `𝔎(Y_n)` (`n ≥ 102`);
* `Sphere.exists_normalizedEnergy_le_of_lt`: for the finitely many `n < 102`, `min 𝔎` is bounded;
* `Sphere.IsSphereMinimizer.normalizedEnergy_le_ring`: **Theorem 5.13 for `E_log`**:
  `min 𝔎 ≤ C_ring n + C n^{3/4}` for all `n ≥ 2`;
* `Sphere.IsSphereMinimizer.normalizedEnergy_le_eventually`: `limsup_n min 𝔎 / n ≤ C_ring`, in the
  form `∀ ε > 0, min 𝔎 ≤ (C_ring + ε) n` for all large `n`.
-/

open Finset

public section

namespace SandierSerfaty

namespace Sphere

theorem IsSphereMinimizer.normalizedEnergy_le {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y)
    {Z : Fin n → R3} (hZ : ∀ i, ‖Z i‖ = 1) (hinj : Function.Injective Z) :
    normalizedEnergy Y ≤ normalizedEnergy Z := by
  have := hY.le Z hZ hinj
  unfold normalizedEnergy
  linarith

/-- For a minimizer of `n ≥ 102` points, `𝔎(Y) ≤ 𝔎(Y_n)`. -/
theorem IsSphereMinimizer.normalizedEnergy_le_ringConfig {n : ℕ} (hn : 102 ≤ n) {Y : Fin n → R3}
    (hY : IsSphereMinimizer Y) : normalizedEnergy Y ≤ normalizedEnergy (ringConfig n) :=
  hY.normalizedEnergy_le (norm_ringConfig n) (ringConfig_injective hn)

/-- For the finitely many `n < 102`, the minimal normalized energy is bounded. -/
theorem exists_normalizedEnergy_le_of_lt : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n < 102 → ∀ Y : Fin n → R3,
    IsSphereMinimizer Y → normalizedEnergy Y ≤ M := by
  choose Z hZ hinj using exists_injective_sphere
  refine ⟨∑ m ∈ range 102, |normalizedEnergy (Z m)|, sum_nonneg fun _ _ => abs_nonneg _,
    fun n hn Y hY => ?_⟩
  have h1 := hY.normalizedEnergy_le (hZ n) (hinj n)
  have h2 : |normalizedEnergy (Z n)| ≤ ∑ m ∈ range 102, |normalizedEnergy (Z m)| :=
    single_le_sum (f := fun m => |normalizedEnergy (Z m)|) (fun _ _ => abs_nonneg _) (mem_range.2 hn)
  exact h1.trans ((le_abs_self _).trans h2)

/-- **Theorem 5.13 for minimizers**: there is an absolute `C` with
`min 𝔎 ≤ C_ring n + C n^{3/4}` for all `n ≥ 2`. -/
theorem IsSphereMinimizer.normalizedEnergy_le_ring : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∀ Y : Fin n → R3, IsSphereMinimizer Y →
      normalizedEnergy Y ≤ ringConstant * n + C * (n : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hring⟩ := normalizedEnergy_ringConfig_le_ring
  obtain ⟨M, hM, hsmall⟩ := exists_normalizedEnergy_le_of_lt
  refine ⟨C + M + 102 * |ringConstant|, by positivity, fun n hn Y hY => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : 1 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  rcases le_or_gt 102 n with h | h
  · have := (hY.normalizedEnergy_le_ringConfig h).trans (hring n h)
    have : 0 ≤ (M + 102 * |ringConstant|) * (n : ℝ) ^ (3 / 4 : ℝ) := by positivity
    nlinarith
  · have h1 := hsmall n h Y hY
    have h2 : -(102 * |ringConstant|) ≤ ringConstant * n := by
      have hn' : (n : ℝ) ≤ 102 := by exact_mod_cast h.le
      have := neg_abs_le ringConstant
      nlinarith [abs_nonneg ringConstant]
    have h3 : C + M + 102 * |ringConstant| ≤ (C + M + 102 * |ringConstant|) * (n : ℝ) ^ (3 / 4 : ℝ) := by
      have : 0 ≤ C + M + 102 * |ringConstant| := by positivity
      nlinarith
    linarith

/-- **`limsup_n min 𝔎 / n ≤ C_ring`**: for every `ε > 0`, `min 𝔎 ≤ (C_ring + ε) n` for all large `n`. -/
theorem IsSphereMinimizer.normalizedEnergy_le_eventually {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ Y : Fin n → R3, IsSphereMinimizer Y →
      normalizedEnergy Y ≤ (ringConstant + ε) * n := by
  obtain ⟨C, hC, h⟩ := IsSphereMinimizer.normalizedEnergy_le_ring
  refine ⟨max 2 ⌈(C / ε) ^ 4⌉₊, fun n hn Y hY => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have h1 := h n hn2 Y hY
  obtain ⟨hq1, hq4, -, -⟩ := fourth_root_facts (show 1 ≤ n by omega)
  rw [rpow_three_fourths] at h1
  set q := (n : ℝ) ^ (1 / 4 : ℝ)
  have hCε : 0 ≤ C / ε := by positivity
  have hq : C / ε ≤ q := by
    have hle : (C / ε) ^ 4 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
    have := Real.rpow_le_rpow (by positivity) hle (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : ((C / ε) ^ 4) ^ (1 / 4 : ℝ) = C / ε := by
      rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hCε (by norm_num)
    rwa [e] at this
  have hCq : C ≤ ε * q := by rwa [div_le_iff₀ hε, mul_comm] at hq
  have : C * q ^ 3 ≤ ε * n := by
    rw [← hq4]
    have := mul_le_mul_of_nonneg_right hCq (show 0 ≤ q ^ 3 by positivity)
    nlinarith
  nlinarith

end Sphere

end SandierSerfaty

end
