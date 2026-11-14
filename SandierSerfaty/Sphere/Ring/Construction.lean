/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Barycentre
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The ring configuration `Y_n` (sphere note Construction 5.7, Lemma 5.8 (G1))

Parameters (Construction 5.7): `T = ⌈n^{1/4}⌉`, `N_cap = max(40, 4T)`,
`N*(a) = √(2√3π a(n - a)/n)`, `ñ(a) = max(3, ⌊N*(a) + ½⌋)`; a step at mass `a` is *bulk* if
`N*(a) ≥ N_cap`. Rows are built from the south pole, the state after `k` rows being
`(A_k, N_{k-1}, j_{k-1})` (`Sphere.ringStep`, `Sphere.ringState`). At mass `a`, with `r = n - a`:

* (F) if `r ≤ 2ñ + 3`, the last row takes the `r` remaining points;
* (C) else, if there is a previous row, both this step and the previous one are bulk and
  `|N_{k-1} - N*(a)| ≤ T`, the row repeats the previous count with `j_k = j_{k-1} + 1`;
* (S) else the row has `ñ` points and `j_k = 0`.

Heights are the slab barycentres and the phases `φ_k = j_k π / N_k` (`Sphere.ringRows`).

* `Sphere.ringRows_card`: `∑ N_k = n`; `Sphere.ringRows_isSlabBarycentric`;
* `Sphere.three_le_ringRows_N`, `Sphere.ringRows_N_last_le` (`N_K ≤ 51`), `Sphere.not_bulk_last`:
  Lemma 5.8 (G1) (rows are indexed from `0`, so the last row is `K - 1`);
* `Sphere.ringConfig n : Fin n → ℝ³`, and `Sphere.sphereEnergy_ringConfig`: Proposition 5.5 for `Y_n`.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

/-- The tolerance `T = ⌈n^{1/4}⌉`. -/
@[expose] noncomputable def ringTol (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (1 / 4 : ℝ)⌉₊

/-- The cap threshold `N_cap = max(40, 4T)`. -/
@[expose] noncomputable def ringCap (n : ℕ) : ℕ := max 40 (4 * ringTol n)

/-- The target count `N*(a) = √(2√3π a(n - a)/n)`. -/
@[expose] noncomputable def ringTarget (n a : ℕ) : ℝ :=
  Real.sqrt (2 * Real.sqrt 3 * Real.pi * a * ((n : ℝ) - a) / n)

/-- The rounded target `ñ(a) = max(3, ⌊N*(a) + ½⌋)`. -/
@[expose] noncomputable def ringRound (n a : ℕ) : ℕ := max 3 ⌊ringTarget n a + 1 / 2⌋₊

open scoped Classical in
/-- One step of Construction 5.7 on the state `(A_k, N_{k-1}, j_{k-1})` (with `N_{-1} = 0`). A state
with `A_k ≥ n` is final and maps to `(A_k, 0, 0)`. -/
@[expose] noncomputable def ringStep (n : ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if n ≤ s.1 then (s.1, 0, 0)
  else if n - s.1 ≤ 2 * ringRound n s.1 + 3 then (n, n - s.1, 0)
  else if 0 < s.2.1 ∧ (ringCap n : ℝ) ≤ ringTarget n s.1 ∧
      (ringCap n : ℝ) ≤ ringTarget n (s.1 - s.2.1) ∧
      |(s.2.1 : ℝ) - ringTarget n s.1| ≤ ringTol n then (s.1 + s.2.1, s.2.1, s.2.2 + 1)
  else (s.1 + ringRound n s.1, ringRound n s.1, 0)

/-- The state `(A_k, N_{k-1}, j_{k-1})` after `k` steps. -/
@[expose] noncomputable def ringState (n k : ℕ) : ℕ × ℕ × ℕ := (ringStep n)^[k] (0, 0, 0)

theorem ringState_succ (n k : ℕ) : ringState n (k + 1) = ringStep n (ringState n k) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Numerical bounds on `2√3π` -/

theorem two_sqrt_three_pi_pos : 0 < 2 * Real.sqrt 3 * Real.pi := by positivity

theorem two_sqrt_three_pi_lt : 2 * Real.sqrt 3 * Real.pi < 10.9 := by
  have h3 : Real.sqrt 3 < 1.7321 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hπ := Real.pi_lt_d4
  have := Real.sqrt_nonneg 3
  nlinarith [Real.pi_pos]

theorem ringTarget_sq (n a : ℕ) (ha : a ≤ n) :
    ringTarget n a ^ 2 = 2 * Real.sqrt 3 * Real.pi * a * ((n : ℝ) - a) / n := by
  unfold ringTarget
  rw [Real.sq_sqrt]
  have : (a : ℝ) ≤ n := by exact_mod_cast ha
  have := two_sqrt_three_pi_pos
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    subst this; simp
  · have : (0 : ℝ) < n := by exact_mod_cast hn
    apply div_nonneg _ this.le
    apply mul_nonneg (by positivity) (by linarith)

theorem ringTarget_nonneg (n a : ℕ) : 0 ≤ ringTarget n a := Real.sqrt_nonneg _

/-- `N*(a)² ≤ 2√3π (n - a)`. -/
theorem ringTarget_sq_le (n a : ℕ) (ha : a ≤ n) :
    ringTarget n a ^ 2 ≤ 2 * Real.sqrt 3 * Real.pi * ((n : ℝ) - a) := by
  rw [ringTarget_sq n a ha]
  have hc := two_sqrt_three_pi_pos
  have han : (a : ℝ) ≤ n := by exact_mod_cast ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : a = 0 := by omega
    subst this; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have h1 : 0 ≤ (n : ℝ) - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg hc.le h1) h1]

theorem three_le_ringRound (n a : ℕ) : 3 ≤ ringRound n a := le_max_left _ _

theorem ringRound_le (n a : ℕ) (h : 3 < ringRound n a) :
    (ringRound n a : ℝ) ≤ ringTarget n a + 1 / 2 := by
  have : ringRound n a = ⌊ringTarget n a + 1 / 2⌋₊ := by
    unfold ringRound at h ⊢; omega
  rw [this]
  exact Nat.floor_le (by have := ringTarget_nonneg n a; linarith)

/-- In a (C)-step the repeated count is at most half of what remains. -/
theorem two_mul_le_of_cont {n a N : ℕ} (ha : a ≤ n) (hb : (ringCap n : ℝ) ≤ ringTarget n a)
    (hT : |(N : ℝ) - ringTarget n a| ≤ ringTol n) : 2 * (N : ℝ) ≤ n - a := by
  have hcap : (40 : ℝ) ≤ ringCap n := by
    have : 40 ≤ ringCap n := le_max_left _ _
    exact_mod_cast this
  have hT4 : 4 * (ringTol n : ℝ) ≤ ringCap n := by
    have : 4 * ringTol n ≤ ringCap n := le_max_right _ _
    exact_mod_cast this
  have hN : (N : ℝ) ≤ ringTarget n a + ringTol n := by
    have := (abs_le.1 hT).2; linarith
  have hsq := ringTarget_sq_le n a ha
  have hc := two_sqrt_three_pi_lt
  have hc0 := two_sqrt_three_pi_pos
  set x := ringTarget n a
  have hx40 : 40 ≤ x := hcap.trans hb
  -- `n - a ≥ x² / 10.9 ≥ 40 x / 10.9 ≥ 3.6 x ≥ 2.5 x ≥ 2 N`
  have h1 : x ^ 2 ≤ 10.9 * ((n : ℝ) - a) := by
    have : 0 ≤ (n : ℝ) - a := by
      have : (a : ℝ) ≤ n := by exact_mod_cast ha
      linarith
    nlinarith
  nlinarith

/-! ### The basic step facts -/

theorem ringStep_of_le {n : ℕ} {s : ℕ × ℕ × ℕ} (h : n ≤ s.1) : ringStep n s = (s.1, 0, 0) := by
  unfold ringStep; rw [ite_eq_left h]

/-- The facts about one step from a mass `a < n`. -/
theorem ringStep_spec {n : ℕ} {s : ℕ × ℕ × ℕ} (h : s.1 < n) :
    (ringStep n s).1 = s.1 + (ringStep n s).2.1 ∧ 0 < (ringStep n s).2.1 ∧ (ringStep n s).1 ≤ n ∧
      ((ringStep n s).1 = n → n - s.1 ≤ 51 ∧ ringTarget n s.1 < ringCap n) ∧
      ((ringStep n s).1 < n → 2 * (ringStep n s).2.1 ≤ n - s.1 ∧ 9 < n - s.1 ∧
        ((ringStep n s).2.1 = s.2.1 ∨ 3 ≤ (ringStep n s).2.1)) := by
  have hlt : ¬ n ≤ s.1 := not_le.2 h
  have hround := three_le_ringRound n s.1
  unfold ringStep
  rw [ite_eq_right hlt]
  split_ifs with hF hC
  · -- (F)
    refine ⟨by simp; omega, by simp; omega, le_rfl, fun _ => ?_, fun h' => absurd h' (lt_irrefl _)⟩
    -- `r ≤ 2ñ + 3` forces `r ≤ 51`
    set r := n - s.1
    have hr : (r : ℝ) = n - s.1 := by simp only [r]; push_cast [h.le]; ring
    have hsq := ringTarget_sq_le n s.1 h.le
    rw [← hr] at hsq
    have hc := two_sqrt_three_pi_lt
    have hc0 := two_sqrt_three_pi_pos
    have hx0 := ringTarget_nonneg n s.1
    have hr51 : r ≤ 51 := by
      by_contra hcon
      have hr52 : (52 : ℝ) ≤ r := by exact_mod_cast (not_le.1 hcon)
      rcases (three_le_ringRound n s.1).eq_or_lt with h3 | h3
      · rw [← h3] at hF; omega
      · have hle := ringRound_le n s.1 h3
        have hF' : (r : ℝ) ≤ 2 * ringRound n s.1 + 3 := by exact_mod_cast hF
        have hsq' : ringTarget n s.1 ^ 2 ≤ 10.9 * r := by nlinarith
        nlinarith
    refine ⟨hr51, ?_⟩
    have hr51' : (r : ℝ) ≤ 51 := by exact_mod_cast hr51
    have hcap : (40 : ℝ) ≤ ringCap n := by
      have : 40 ≤ ringCap n := le_max_left _ _
      exact_mod_cast this
    have : ringTarget n s.1 ^ 2 < 40 ^ 2 := by nlinarith
    have : ringTarget n s.1 < 40 := by nlinarith
    linarith
  · -- (C)
    obtain ⟨hN0, hb, _, hT⟩ := hC
    have h2 := two_mul_le_of_cont h.le hb hT
    have hr : (((n - s.1 : ℕ)) : ℝ) = n - s.1 := by push_cast [h.le]; ring
    have h2' : 2 * s.2.1 ≤ n - s.1 := by
      have : (2 * s.2.1 : ℝ) ≤ ((n - s.1 : ℕ) : ℝ) := by rw [hr]; exact h2
      exact_mod_cast this
    have hF' : 2 * ringRound n s.1 + 3 < n - s.1 := not_le.1 hF
    refine ⟨rfl, hN0, show s.1 + s.2.1 ≤ n by omega, fun h' => by simp at h'; omega,
      fun _ => ⟨h2', by omega, Or.inl rfl⟩⟩
  · -- (S)
    have hF' : 2 * ringRound n s.1 + 3 < n - s.1 := not_le.1 hF
    refine ⟨rfl, show 0 < ringRound n s.1 by omega, show s.1 + ringRound n s.1 ≤ n by omega,
      fun h' => by simp at h'; omega, fun _ => ⟨show 2 * ringRound n s.1 ≤ n - s.1 by omega,
        by omega, Or.inr hround⟩⟩

theorem ringState_fst_le (n k : ℕ) : (ringState n k).1 ≤ n ∨ n = 0 := by
  induction k with
  | zero => left; simp [ringState]
  | succ k ih =>
    rw [ringState_succ]
    rcases lt_or_ge (ringState n k).1 n with h | h
    · exact Or.inl (ringStep_spec h).2.2.1
    · rw [ringStep_of_le h]
      exact ih

theorem ringState_mono (n k : ℕ) : (ringState n k).1 ≤ (ringState n (k + 1)).1 := by
  rw [ringState_succ]
  rcases lt_or_ge (ringState n k).1 n with h | h
  · rw [(ringStep_spec h).1]; omega
  · rw [ringStep_of_le h]

/-- The mass grows by at least one per step until it reaches `n`. -/
theorem min_le_ringState (n k : ℕ) : min k n ≤ (ringState n k).1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ringState_succ]
    rcases lt_or_ge (ringState n k).1 n with h | h
    · have hs := ringStep_spec h
      have := hs.2.1
      omega
    · rw [ringStep_of_le h]; omega

theorem ringK_exists (n : ℕ) : ∃ k, n ≤ (ringState n k).1 :=
  ⟨n, by have := min_le_ringState n n; simpa using this⟩

/-- The number of rows `K`: the first `k` with `A_k ≥ n`. -/
@[expose] noncomputable def ringK (n : ℕ) : ℕ := Nat.find (ringK_exists n)

theorem le_ringState_ringK (n : ℕ) : n ≤ (ringState n (ringK n)).1 :=
  Nat.find_spec (ringK_exists n)

theorem ringState_lt_of_lt_ringK {n k : ℕ} (hk : k < ringK n) : (ringState n k).1 < n :=
  not_le.1 (Nat.find_min (ringK_exists n) hk)

theorem ringState_ringK (n : ℕ) : (ringState n (ringK n)).1 = n := by
  rcases ringState_fst_le n (ringK n) with h | h
  · exact le_antisymm h (le_ringState_ringK n)
  · subst h
    have : ringK 0 = 0 := (Nat.find_eq_zero (ringK_exists 0)).2 (Nat.zero_le _)
    rw [this]; rfl

/-! ### The row configuration -/

/-- The count `N_k` of row `k`. -/
@[expose] noncomputable def ringN (n k : ℕ) : ℕ := (ringState n (k + 1)).2.1

/-- The band index `j_k` of row `k`. -/
@[expose] noncomputable def ringJ (n k : ℕ) : ℕ := (ringState n (k + 1)).2.2

theorem ringStep_spec_at {n k : ℕ} (hk : k < ringK n) :
    (ringState n (k + 1)).1 = (ringState n k).1 + ringN n k ∧ 0 < ringN n k ∧
      ((ringState n (k + 1)).1 = n → n - (ringState n k).1 ≤ 51 ∧
        ringTarget n (ringState n k).1 < ringCap n) ∧
      ((ringState n (k + 1)).1 < n → 2 * ringN n k ≤ n - (ringState n k).1 ∧
        9 < n - (ringState n k).1 ∧ (ringN n k = (ringState n k).2.1 ∨ 3 ≤ ringN n k)) := by
  have h := ringStep_spec (ringState_lt_of_lt_ringK hk)
  rw [← ringState_succ] at h
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem ringState_fst_eq_sum (n : ℕ) : ∀ k ≤ ringK n,
    (ringState n k).1 = ∑ j ∈ Finset.range k, ringN n j
  | 0, _ => by simp [ringState]
  | k + 1, hk => by
    rw [(ringStep_spec_at (n := n) (k := k) (by omega)).1, Finset.sum_range_succ,
      ringState_fst_eq_sum n k (by omega)]

/-- The heights `t_k`: the `ν`-barycentres of the slabs `{A_k ≤ Φ ≤ A_{k+1}}`. -/
@[expose] noncomputable def ringHeight (n k : ℕ) : ℝ :=
  (ringN n k : ℝ)⁻¹ * ∫ s in {t | ((ringState n k).1 : ℝ) ≤ ringMass n t ∧
    ringMass n t ≤ (ringState n (k + 1)).1}, s * ringDensity n s

/-- The ring configuration of Construction 5.7 as a row configuration: rows `k < K`, counts `N_k`,
slab-barycentric heights, phases `φ_k = j_k π / N_k`. -/
@[expose] noncomputable def ringRows (n : ℕ) : RowConfig where
  K := ringK n
  N := ringN n
  t := ringHeight n
  φ := fun k => ringJ n k * Real.pi / ringN n k

theorem ringRows_mass (n k : ℕ) (hk : k ≤ ringK n) : (ringRows n).mass k = (ringState n k).1 :=
  (ringState_fst_eq_sum n k hk).symm

/-- **(G1)**, first part: `∑ N_k = n`. -/
theorem ringRows_card (n : ℕ) : (ringRows n).card = n := by
  rw [← RowConfig.mass_K]
  exact (ringRows_mass n (ringK n) le_rfl).trans (ringState_ringK n)

theorem ringRows_N_pos {n k : ℕ} (hk : k < ringK n) : 0 < (ringRows n).N k :=
  (ringStep_spec_at hk).2.1

theorem ringRows_isSlabBarycentric (n : ℕ) : (ringRows n).IsSlabBarycentric := by
  refine ⟨fun k hk => ringRows_N_pos hk, fun k hk => ?_⟩
  rw [RowConfig.slab, ringRows_card, ringRows_mass n k hk.le, ringRows_mass n (k + 1) hk]
  rfl

/-- **(G1)**: for `n ≥ 10` every row has at least `3` points. -/
theorem three_le_ringN {n : ℕ} (hn : 10 ≤ n) : ∀ k < ringK n, 3 ≤ ringN n k
  | 0, hk => by
    have hs := ringStep_spec_at hk
    rcases lt_or_eq_of_le (show (ringState n 1).1 ≤ n from by
      rcases ringState_fst_le n 1 with h | h
      · exact h
      · omega) with h | h
    · rcases (hs.2.2.2 h).2.2 with h' | h'
      · have : (ringState n 0).2.1 = 0 := rfl
        have := hs.2.1
        omega
      · exact h'
    · -- the first step is not final for `n ≥ 10`
      exfalso
      have h0 : (ringState n 0).1 = 0 := rfl
      have hst : ringState n 1 = ringStep n (0, 0, 0) := rfl
      have hround : ringRound n 0 = 3 := by
        have : ⌊ringTarget n 0 + 1 / 2⌋₊ = 0 := Nat.floor_eq_zero.2 (by norm_num [ringTarget])
        unfold ringRound; rw [this]; rfl
      have : ¬ n ≤ 0 := by omega
      have h9 : ¬ n - 0 ≤ 2 * ringRound n 0 + 3 := by rw [hround]; omega
      rw [hst] at h
      unfold ringStep at h
      rw [ite_eq_right this, ite_eq_right h9] at h
      split_ifs at h with hC
      · simp at hC
      · simp at h; omega
  | k + 1, hk => by
    have ih := three_le_ringN hn k (by omega)
    have hs := ringStep_spec_at hk
    have hs' := ringStep_spec_at (n := n) (k := k) (by omega)
    have hlt : (ringState n (k + 1)).1 < n := ringState_lt_of_lt_ringK hk
    obtain ⟨h2, h9, _⟩ := hs'.2.2.2 hlt
    rcases lt_or_eq_of_le (show (ringState n (k + 1 + 1)).1 ≤ n from by
      rcases ringState_fst_le n (k + 1 + 1) with h | h
      · exact h
      · omega) with h | h
    · rcases (hs.2.2.2 h).2.2 with h' | h'
      · rw [h']; exact ih
      · exact h'
    · -- the last row: `n - A_{k+1} ≥ (n - A_k)/2 > 4`
      have e1 : (ringState n (k + 1 + 1)).1 = (ringState n (k + 1)).1 + ringN n (k + 1) := hs.1
      have e2 : (ringState n (k + 1)).1 = (ringState n k).1 + ringN n k := hs'.1
      have hA : (ringState n k).1 < n := ringState_lt_of_lt_ringK (by omega)
      omega

/-- **(G1)**: the last row has at most `51` points. -/
theorem ringN_last_le {n : ℕ} (hK : 0 < ringK n) : ringN n (ringK n - 1) ≤ 51 := by
  have hk : ringK n - 1 < ringK n := by omega
  have hs := ringStep_spec_at hk
  have hfin : (ringState n (ringK n - 1 + 1)).1 = n := by
    rw [Nat.sub_add_cancel hK]; exact ringState_ringK n
  have := (hs.2.2.1 hfin).1
  have := hs.1
  omega

/-- **(G1)**: rule (F) is used only at the last step, and that step is not bulk. -/
theorem not_bulk_last {n : ℕ} (hK : 0 < ringK n) :
    ringTarget n (ringState n (ringK n - 1)).1 < ringCap n := by
  have hk : ringK n - 1 < ringK n := by omega
  have hfin : (ringState n (ringK n - 1 + 1)).1 = n := by
    rw [Nat.sub_add_cancel hK]; exact ringState_ringK n
  exact ((ringStep_spec_at hk).2.2.1 hfin).2

/-- The ring configuration `Y_n ∈ (S²)ⁿ` of Construction 5.7. -/
@[expose] noncomputable def ringConfig (n : ℕ) : Fin n → R3 :=
  (ringRows n).points ∘ finSigmaFinEquiv.symm ∘
    Fin.cast (by rw [Fin.sum_univ_eq_sum_range (fun k => (ringRows n).N k)]; exact
      (ringRows_card n).symm)

/-- **Proposition 5.5 for `Y_n`**:
`E(Y_n) = (½ - log 2) n² - (n/2) log n + (n/2) log 2 + ∑_k B_k`. -/
theorem sphereEnergy_ringConfig (n : ℕ) :
    sphereEnergy (ringConfig n) =
      (1 / 2 - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + (n : ℝ) / 2 * Real.log 2 +
        ∑ k ∈ Finset.range (ringK n), (ringRows n).rowB k := by
  have h := (ringRows n).configEnergy_eq_ring_of_isSlabBarycentric (ringRows_isSlabBarycentric n)
  rw [ringRows_card] at h
  rw [show ringK n = (ringRows n).K from rfl, ← h]
  have hn : n = ∑ k : Fin (ringRows n).K, (ringRows n).N k := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (ringRows n).N k)]; exact (ringRows_card n).symm
  exact sphereEnergy_comp_equiv ((finCongr hn).trans finSigmaFinEquiv.symm) (ringRows n).points

end Sphere

end SandierSerfaty

end
