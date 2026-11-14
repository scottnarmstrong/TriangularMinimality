/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Count

/-!
# The band decomposition of `Y_n` and the number of bands (sphere note, Lemma 5.8 (G6))

A **band start** (`Sphere.RingBandStart`) is a bulk row that is not a (C)-row; every bulk row `k` lies in a
band `[s, h]` that starts at a band start `s ≤ k` and ends at a row `h ≥ k` after which no (C)-row
follows.

* `Sphere.ringBulk_of_between`: the bulk rows form an interval of indices (`a ↦ a (n - a)` is
  quasi-concave);
* `Sphere.abs_ringN_sub_le_of_start`: a band start is made by rule (S), `|N_s - N*(A_s)| ≤ ½`;
* `Sphere.ringBand_length`: a band ended by a bulk row has at least `T / 44` rows (along the band the
  target count moves by `> T - ½`, while `|ΔN*| ≤ 2√3π · Δa / (N*(a) + N*(b))` and `Δa = m N_b`);
* `Sphere.ringBandStart_gap`: two band starts are at least `T / 44` apart;
* `Sphere.card_ringBandStart_le`: **(G6), bands**: there are at most `44 K / T + 1` band starts;
* `Sphere.exists_ringBand_start`, `Sphere.exists_ringBand_end`, `Sphere.le_of_ringBand_end`: the band
  decomposition of the bulk rows.
-/

open Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `a(n - a) ≥ min(x(n - x), z(n - z))` for `x ≤ a ≤ z`, hence `N*(a) ≥ min(N*(x), N*(z))`. -/
theorem ringTarget_ge_min {n x a z : ℕ} (hxa : x ≤ a) (haz : a ≤ z) :
    min (ringTarget n x) (ringTarget n z) ≤ ringTarget n a := by
  have hc := two_sqrt_three_pi_pos
  have hx' : (x : ℝ) ≤ a := by exact_mod_cast hxa
  have hz' : (a : ℝ) ≤ z := by exact_mod_cast haz
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have key : ∀ u v : ℝ, u * (n - u) ≤ v * (n - v) →
      2 * Real.sqrt 3 * Real.pi * u * ((n : ℝ) - u) / n ≤
        2 * Real.sqrt 3 * Real.pi * v * ((n : ℝ) - v) / n := by
    intro u v h
    apply div_le_div_of_nonneg_right _ hn0
    have := mul_le_mul_of_nonneg_left h hc.le
    linarith [show 2 * Real.sqrt 3 * Real.pi * u * ((n : ℝ) - u) =
      2 * Real.sqrt 3 * Real.pi * (u * (n - u)) by ring,
      show 2 * Real.sqrt 3 * Real.pi * v * ((n : ℝ) - v) =
      2 * Real.sqrt 3 * Real.pi * (v * (n - v)) by ring]
  rcases le_total ((x : ℝ) + a) n with h | h
  · refine min_le_of_left_le (Real.sqrt_le_sqrt (key _ _ ?_))
    nlinarith
  · refine min_le_of_right_le (Real.sqrt_le_sqrt (key _ _ ?_))
    nlinarith

/-- **The bulk rows form an interval of indices.** -/
theorem ringBulk_of_between {n k j l : ℕ} (hk : RingBulk n k) (hl : RingBulk n l) (hkj : k ≤ j)
    (hjl : j ≤ l) : RingBulk n j := by
  have hmono : ∀ {p q : ℕ}, p ≤ q → (ringState n p).1 ≤ (ringState n q).1 := fun h => by
    have := ringState_cast_le (n := n) h; exact_mod_cast this
  have := ringTarget_ge_min (n := n) (hmono hkj) (hmono hjl)
  exact (le_min hk hl).trans this

/-- A **band start**: a bulk row (of `Y_n`) that is not made by rule (C). -/
@[expose] def RingBandStart (n s : ℕ) : Prop := s < ringK n ∧ RingBulk n s ∧ ¬ RingCRow n s

/-- A band start is made by rule (S): `|N_s - N*(A_s)| ≤ ½`. -/
theorem abs_ringN_sub_le_of_start {n s : ℕ} (hs : RingBandStart n s) :
    |(ringN n s : ℝ) - ringTarget n (ringState n s).1| ≤ 1 / 2 := by
  obtain ⟨hsK, hb, hC⟩ := hs
  obtain ⟨hs1, hs'⟩ := ringBulk_interior hsK hb
  have hlt0 : (ringState n s).1 < n := ringState_lt_of_lt_ringK hsK
  have hlt : (ringStep n (ringState n s)).1 < n := by
    rw [← ringState_succ]; exact ringState_lt_of_lt_ringK hs'
  rcases (ringStep_cases hlt0 hlt).2 with ⟨hC', _⟩ | ⟨_, he⟩
  · exact absurd ⟨hs1, hs', hC'⟩ hC
  · have : ringN n s = ringRound n (ringState n s).1 := by
      unfold ringN; rw [ringState_succ, he]
    rw [this]
    have := forty_le_ringCap n
    unfold RingBulk at hb
    exact abs_ringRound_sub_le (by linarith)

/-- A band ended by a bulk row that is not a (C)-row: `|N_h - N*(A_{h+1})| > T`. -/
theorem lt_abs_ringN_sub_of_end {n h : ℕ} (hb : RingBulk n h) (hb' : RingBulk n (h + 1))
    (hK : h + 1 < ringK n) (hC : ¬ RingCRow n (h + 1)) :
    (ringTol n : ℝ) < |(ringN n h : ℝ) - ringTarget n (ringState n (h + 1)).1| := by
  obtain ⟨-, hh2⟩ := ringBulk_interior hK hb'
  have e : (ringState n (h + 1)).1 - (ringState n (h + 1)).2.1 = (ringState n h).1 := by
    have h1 := (ringStep_spec_at (n := n) (k := h) (by omega)).1
    have : (ringState n (h + 1)).2.1 = ringN n h := rfl
    rw [this, h1]; omega
  by_contra hT
  push Not at hT
  refine hC ⟨by omega, hh2, ringRows_N_pos (n := n) (k := h) (by omega), hb', ?_, hT⟩
  rw [e]; exact hb

/-- `|N*(b)² - N*(a)²| ≤ 2√3π (b - a)` for `a ≤ b ≤ n`. -/
theorem abs_ringTarget_sq_sub_le {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) (hn : 0 < n) :
    |ringTarget n b ^ 2 - ringTarget n a ^ 2| ≤ 10.9 * ((b : ℝ) - a) := by
  rw [ringTarget_sq n b hb, ringTarget_sq n a (hab.trans hb)]
  have hc := two_sqrt_three_pi_lt
  have hc0 := two_sqrt_three_pi_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hb' : (b : ℝ) ≤ n := by exact_mod_cast hb
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  set c := 2 * Real.sqrt 3 * Real.pi
  have e : c * b * ((n : ℝ) - b) / n - c * a * ((n : ℝ) - a) / n =
      c * ((b : ℝ) - a) * ((n : ℝ) - a - b) / n := by field_simp; ring
  rw [e, abs_le]
  have hba : 0 ≤ (b : ℝ) - a := by linarith
  have h1 : c * ((b : ℝ) - a) * ((n : ℝ) - a - b) ≤ c * ((b : ℝ) - a) * n :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : -(c * ((b : ℝ) - a) * n) ≤ c * ((b : ℝ) - a) * ((n : ℝ) - a - b) := by
    have := mul_le_mul_of_nonneg_left (show -(n : ℝ) ≤ n - a - b by linarith)
      (show 0 ≤ c * ((b : ℝ) - a) by positivity)
    linarith
  have h3 : c * ((b : ℝ) - a) ≤ 10.9 * ((b : ℝ) - a) := mul_le_mul_of_nonneg_right hc.le hba
  constructor
  · rw [le_div_iff₀ hn']; nlinarith
  · rw [div_le_iff₀ hn']; nlinarith

/-- `A_{h+1} = A_s + (h - s + 1) N_s` along a band `[s, h]`. -/
theorem ringState_band {n s h : ℕ} (hsh : s ≤ h) (hhK : h + 1 ≤ ringK n)
    (hband : ∀ j, s < j → j ≤ h → RingCRow n j) :
    (ringState n (h + 1)).1 = (ringState n s).1 + (h + 1 - s) * ringN n s := by
  rw [ringState_fst_eq_sum n (h + 1) hhK, ringState_fst_eq_sum n s (by omega),
    ← sum_range_add_sum_Ico _ (show s ≤ h + 1 by omega)]
  congr 1
  rw [sum_congr rfl fun j hj => ringBand_N hband j (mem_Ico.1 hj).1 (by have := (mem_Ico.1 hj).2; omega),
    sum_const, Nat.card_Ico, smul_eq_mul]

/-- **A band ended by a bulk row has at least `T / 44` rows.** -/
theorem ringBand_length {n s h : ℕ} (hn : 10 ≤ n) (hs : RingBandStart n s) (hsh : s ≤ h)
    (hband : ∀ j, s < j → j ≤ h → RingCRow n j) (hb' : RingBulk n (h + 1)) (hK : h + 1 < ringK n)
    (hC : ¬ RingCRow n (h + 1)) : (ringTol n : ℝ) ≤ 44 * ((h + 1 - s : ℕ) : ℝ) := by
  have hbs := hs.2.1
  have hbh : RingBulk n h := ringBand_bulk hbs hband h hsh le_rfl
  have hNh : ringN n h = ringN n s := ringBand_N hband h hsh le_rfl
  have hend := lt_abs_ringN_sub_of_end hbh hb' hK hC
  rw [hNh] at hend
  have hstart := abs_ringN_sub_le_of_start hs
  have hA := ringState_band hsh hK.le hband
  set a := (ringState n s).1
  set b := (ringState n (h + 1)).1
  set m := h + 1 - s
  set Nb := ringN n s
  set P := ringTarget n a
  set Q := ringTarget n b
  have hbn : b ≤ n := by have := ringState_lt_of_lt_ringK hK; omega
  have hsq := abs_ringTarget_sq_sub_le (n := n) (show a ≤ b by omega) hbn (by omega)
  have hba : ((b : ℝ) - a) = (m : ℝ) * Nb := by rw [hA]; push_cast; ring
  rw [hba] at hsq
  have hP0 : 0 ≤ P := ringTarget_nonneg _ _
  have hQ0 : 0 ≤ Q := ringTarget_nonneg _ _
  have hNb : (1 : ℝ) ≤ Nb := by exact_mod_cast ringRows_N_pos (n := n) (k := s) hs.1
  have hT1 : (1 : ℝ) ≤ ringTol n := by exact_mod_cast one_le_ringTol (by omega : 0 < n)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  -- `|Q - P| > T - ½`
  have hQP : (ringTol n : ℝ) - 1 / 2 < |Q - P| := by
    have := abs_sub_abs_le_abs_sub ((Nb : ℝ) - Q) ((Nb : ℝ) - P)
    rw [show (Nb : ℝ) - Q - (Nb - P) = P - Q by ring, abs_sub_comm P Q] at this
    rw [abs_sub_comm] at hend
    linarith [abs_sub_comm (Q : ℝ) Nb]
  -- `P + Q ≥ N_b / 2`
  have hPQ : (Nb : ℝ) / 2 ≤ P + Q := by
    have := (abs_le.1 hstart).2; linarith
  have hprod : |Q - P| * (P + Q) ≤ 10.9 * ((m : ℝ) * Nb) := by
    rw [show |Q - P| * (P + Q) = |Q ^ 2 - P ^ 2| by
      rw [show Q ^ 2 - P ^ 2 = (Q - P) * (P + Q) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ P + Q)]]
    exact hsq
  have h1 : ((ringTol n : ℝ) - 1 / 2) * ((Nb : ℝ) / 2) ≤ |Q - P| * (P + Q) :=
    mul_le_mul hQP.le hPQ (by positivity) (abs_nonneg _)
  have h2 : (ringTol n : ℝ) - 1 / 2 ≤ 21.8 * m := by
    have h3 : ((ringTol n : ℝ) - 1 / 2) * Nb ≤ (21.8 * m) * Nb := by linarith
    exact le_of_mul_le_mul_right h3 (by linarith)
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by simp only [m]; omega
    exact_mod_cast this
  linarith

/-- **Two band starts are at least `T / 44` apart.** -/
theorem ringBandStart_gap {n s s' : ℕ} (hn : 10 ≤ n) (hs : RingBandStart n s) (hs' : RingBandStart n s')
    (hss' : s < s') : (ringTol n : ℝ) ≤ 44 * ((s' : ℝ) - s) := by
  classical
  have hex : ∃ j, s ≤ j ∧ ¬ RingCRow n (j + 1) := ⟨s' - 1, by omega, by
    rw [show s' - 1 + 1 = s' by omega]; exact hs'.2.2⟩
  set h := Nat.find hex
  obtain ⟨hsh, hC⟩ := Nat.find_spec hex
  have hhs' : h ≤ s' - 1 := Nat.find_min' hex ⟨by omega, by
    rw [show s' - 1 + 1 = s' by omega]; exact hs'.2.2⟩
  have hband : ∀ j, s < j → j ≤ h → RingCRow n j := by
    intro j hj1 hj2
    have := Nat.find_min hex (show j - 1 < h by omega)
    push Not at this
    have := this (by omega)
    rwa [show j - 1 + 1 = j by omega] at this
  have hb' : RingBulk n (h + 1) :=
    ringBulk_of_between hs.2.1 hs'.2.1 (by omega) (by omega)
  have hlen := ringBand_length hn hs hsh hband hb' (by have := hs'.1; omega) hC
  have : ((h + 1 - s : ℕ) : ℝ) ≤ (s' : ℝ) - s := by
    have e : ((h + 1 - s : ℕ) : ℝ) = (h : ℝ) + 1 - s := by push_cast [show s ≤ h + 1 by omega]; ring
    rw [e]
    have : (h : ℝ) + 1 ≤ s' := by exact_mod_cast (show h + 1 ≤ s' by omega)
    linarith
  linarith

open scoped Classical in
/-- **(G6), bands**: there are at most `44 K / T + 1` band starts. -/
theorem card_ringBandStart_le {n : ℕ} (hn : 10 ≤ n) :
    (((range (ringK n)).filter fun s => RingBandStart n s).card : ℝ) ≤
      44 * ringK n / ringTol n + 1 := by
  have hT : (0 : ℝ) < ringTol n := by exact_mod_cast one_le_ringTol (by omega : 0 < n)
  refine card_le_of_one_le_abs_sub (u := fun s => 44 * (s : ℝ) / ringTol n) (by positivity)
    (fun _ _ => by positivity) (fun s hs => ?_) (fun s hs s' hs' hne => ?_)
  · have : (s : ℝ) ≤ ringK n := by exact_mod_cast (mem_range.1 (mem_filter.1 hs).1).le
    exact div_le_div_of_nonneg_right (by linarith) hT.le
  · have h1 := (mem_filter.1 hs).2
    have h2 := (mem_filter.1 hs').2
    rw [← sub_div, abs_div, abs_of_pos hT, le_div_iff₀ hT, one_mul]
    rcases lt_or_gt_of_ne hne with h | h
    · have := ringBandStart_gap hn h1 h2 h
      have hlt : (s : ℝ) < s' := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have := ringBandStart_gap hn h2 h1 h
      have hlt : (s' : ℝ) < s := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith

/-! ### The band decomposition -/

/-- Every bulk row lies in a band that starts at a band start. -/
theorem exists_ringBand_start {n : ℕ} : ∀ k, k < ringK n → RingBulk n k →
    ∃ s ≤ k, RingBandStart n s ∧ ∀ j, s < j → j ≤ k → RingCRow n j
  | k, hk, hb => by
    by_cases hC : RingCRow n k
    · have hk1 := hC.1
      obtain ⟨s, hs, hst, hband⟩ :=
        exists_ringBand_start (k - 1) (by omega) (ringCRow_bulk hC).2
      refine ⟨s, by omega, hst, fun j hj1 hj2 => ?_⟩
      rcases lt_or_eq_of_le hj2 with h | h
      · exact hband j hj1 (by omega)
      · rw [h]; exact hC
    · exact ⟨k, le_rfl, ⟨hk, hb, hC⟩, fun j hj1 hj2 => absurd hj2 (not_le.2 hj1)⟩

/-- Every row `s < K` has a band end: `h ∈ [s, K)` with `(s, h]` made of (C)-rows and `h + 1` not a
(C)-row. -/
theorem exists_ringBand_end {n s : ℕ} (hs : s < ringK n) :
    ∃ h, s ≤ h ∧ h < ringK n ∧ (∀ j, s < j → j ≤ h → RingCRow n j) ∧ ¬ RingCRow n (h + 1) := by
  classical
  have hex : ∃ j, s ≤ j ∧ ¬ RingCRow n (j + 1) :=
    ⟨ringK n - 1, by omega, fun h => by have := h.2.1; omega⟩
  obtain ⟨hsh, hC⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ ringK n - 1 :=
    Nat.find_min' hex ⟨by omega, fun h => by have := h.2.1; omega⟩
  refine ⟨Nat.find hex, hsh, by omega, fun j hj1 hj2 => ?_, hC⟩
  have := Nat.find_min hex (show j - 1 < Nat.find hex by omega)
  push Not at this
  have := this (by omega)
  rwa [show j - 1 + 1 = j by omega] at this

/-- A row `k` reached from `s` through (C)-rows lies before the band end of `s`. -/
theorem le_of_ringBand_end {n s k h : ℕ} (hband : ∀ j, s < j → j ≤ k → RingCRow n j)
    (hsh : s ≤ h) (hC : ¬ RingCRow n (h + 1)) : k ≤ h := by
  by_contra hkh
  exact hC (hband (h + 1) (by omega) (by omega))

end Sphere

end SandierSerfaty

end
