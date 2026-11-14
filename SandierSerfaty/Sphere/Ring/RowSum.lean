/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Aspect
public import SandierSerfaty.Sphere.Ring.Theta
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The row-sum bound (sphere note, Lemma 5.10)

For `n ≥ 102`, every row `k` and every `u₀ ≥ 0`,
`∑_{l ≠ k, |t_k - t_l| ≥ u₀} min(N_k, N_l) Θ(max(N_k, N_l) |t_k - t_l|) ≤ C_X N_k e^{-N_k u₀/2}`
with an absolute constant `C_X` (`Sphere.ringRowSum_le`).

The sphere note's dyadic counting is replaced by a comparison with an integral. By the separation of
the rows (G4), `Θ(M d) ≤ Θ(c₀) e^{c₀} e^{-M d}` with `M = max(N_k, N_l)`, `d = |t_k - t_l|`,
`c₀ = 3/112`. For an interior row `l`, `N_l |I_l| ≥ 3/4` (G3), and for `t ∈ I_l` one has
`|t - t_k| ≤ 1009 d` (G3, G4) and `N_l e^{-M |t - t_k|/2018} ≤ 4036 h(t)` with
`h(t) = N_k e^{-N_k |t - t_k|/4036}` (G5, `|(log ϱ)'| ≤ 2`). Hence `e^{-M d/2} ≤ (4/3) 4036 ∫_{I_l} h`,
and the slabs are adjacent, so the sum over interior rows is at most `(4/3) 4036 ∫_ℝ h ≤ (4/3) 4036²
· 2`. The two polar rows add at most `2`.
-/

open MeasureTheory Set Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `∫_a^b c e^{-c |t - x₀|} dt ≤ 2` for `c > 0`. -/
theorem integral_exp_neg_abs_le {c : ℝ} (hc : 0 < c) (x₀ a b : ℝ) :
    ∫ t in a..b, c * Real.exp (-(c * |t - x₀|)) ≤ 2 := by
  set f := fun t : ℝ => c * Real.exp (-(c * |t - x₀|))
  have hf : Continuous f := continuous_const.mul
    (Real.continuous_exp.comp ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).neg))
  have hf0 : ∀ t, 0 ≤ f t := fun t => (mul_pos hc (Real.exp_pos _)).le
  rcases lt_or_ge b a with hba | hab
  · rw [intervalIntegral.integral_symm, neg_le]
    exact le_trans (by norm_num) (intervalIntegral.integral_nonneg hba.le fun t _ => hf0 t)
  set lo := min a x₀
  set hi := max b x₀
  have h1 : ∫ t in a..b, f t ≤ ∫ t in lo..hi, f t :=
    intervalIntegral.integral_mono_interval (min_le_left _ _) hab (le_max_left _ _)
      (Filter.Eventually.of_forall fun t => hf0 t) (hf.intervalIntegrable _ _)
  have hlo : lo ≤ x₀ := min_le_right _ _
  have hhi : x₀ ≤ hi := le_max_right _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable lo x₀)
    (hf.intervalIntegrable x₀ hi)] at h1
  have e1 : ∫ t in lo..x₀, f t = 1 - Real.exp (-(c * (x₀ - lo))) := by
    have hd : ∀ t ∈ uIcc lo x₀, HasDerivAt (fun t => Real.exp (-(c * (x₀ - t))))
        (c * Real.exp (-(c * (x₀ - t)))) t := fun t _ => by
      have := ((((hasDerivAt_id' t).const_sub x₀).const_mul c).neg).exp
      convert this using 1; simp only [Pi.neg_apply]; ring
    rw [intervalIntegral.integral_congr (g := fun t => c * Real.exp (-(c * (x₀ - t)))) (fun t ht => by
      simp only [f]; rw [uIcc_of_le hlo] at ht; rw [abs_of_nonpos (by linarith [ht.2])]; ring_nf),
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul
          (continuous_const.sub continuous_id)).neg))).intervalIntegrable _ _)]
    simp
  have e2 : ∫ t in x₀..hi, f t = 1 - Real.exp (-(c * (hi - x₀))) := by
    have hd : ∀ t ∈ uIcc x₀ hi, HasDerivAt (fun t => -Real.exp (-(c * (t - x₀))))
        (c * Real.exp (-(c * (t - x₀)))) t := fun t _ => by
      have := ((((hasDerivAt_id' t).sub_const x₀).const_mul c).neg).exp.neg
      convert this using 1; simp only [Pi.neg_apply]; ring
    rw [intervalIntegral.integral_congr (g := fun t => c * Real.exp (-(c * (t - x₀)))) (fun t ht => by
      simp only [f]; rw [uIcc_of_le hhi] at ht; rw [abs_of_nonneg (by linarith [ht.1])]),
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.mul (Real.continuous_exp.comp ((continuous_const.mul
          (continuous_id.sub continuous_const)).neg))).intervalIntegrable _ _)]
    simp
    ring
  rw [e1, e2] at h1
  have := Real.exp_pos (-(c * (x₀ - lo)))
  have := Real.exp_pos (-(c * (hi - x₀)))
  linarith

/-- `Θ(s) ≤ Θ(s₀) e^{s₀} e^{-s}` for `0 < s₀ ≤ s`. -/
theorem ringTheta_le_exp {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    ringTheta s ≤ ringTheta s₀ * Real.exp s₀ * Real.exp (-s) := by
  have h := ringTheta_add_le hs₀ (sub_nonneg.2 hs)
  rw [add_sub_cancel] at h
  calc ringTheta s ≤ Real.exp (-(s - s₀)) * ringTheta s₀ := h
    _ = ringTheta s₀ * Real.exp s₀ * Real.exp (-s) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- `y e^{-y/c} ≤ c` for `y ≥ 0`, `c > 0`. -/
theorem mul_exp_neg_div_le {y c : ℝ} (hc : 0 < c) (_hy : 0 ≤ y) : y * Real.exp (-(y / c)) ≤ c := by
  have h := Real.add_one_le_exp (y / c)
  have hE := Real.exp_pos (y / c)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  have : y = c * (y / c) := by field_simp
  nlinarith

/-- `d = |t_k - t_l| ≥ c₀/N_l` for `k ≠ l`. -/
theorem ringHeight_dist_ge {n k l : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hl : l < ringK n)
    (hkl : k ≠ l) : 3 / (112 * (ringN n l : ℝ)) ≤ |ringHeight n k - ringHeight n l| := by
  have h0 : ∀ m < ringK n, (0 : ℝ) < 3 / (112 * (ringN n m : ℝ)) := fun m hm => by
    have : (3 : ℝ) ≤ ringN n m := by exact_mod_cast three_le_ringN (by omega) m hm
    positivity
  have hk0 := h0 k hk
  have hl0 := h0 l hl
  rcases lt_or_gt_of_ne hkl with h | h
  · have := ringHeight_sep hn h hl
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · have := ringHeight_sep hn h hk
    rw [abs_of_nonneg (by linarith)]; linarith

/-- The pointwise bound on an interior slab `I_l`, `l ≠ k`:
`N_l e^{-M d/2} ≤ 4036 N_k e^{-N_k |t - t_k|/4036}`. -/
theorem ringSlab_pointwise {n k l : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hl1 : 1 ≤ l)
    (hl : l + 1 < ringK n) (hkl : k ≠ l) {t : ℝ}
    (ht : t ∈ Icc (ringQuantile n (ringState n l).1) (ringQuantile n (ringState n (l + 1)).1)) :
    (ringN n l : ℝ) * Real.exp (-(((max (ringN n k) (ringN n l) : ℕ) : ℝ) *
        |ringHeight n k - ringHeight n l| / 2)) ≤
      4036 * ((ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) / 4036 * |t - ringHeight n k|))) := by
  have hNk3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN (by omega) k hk
  have hNl3 : (3 : ℝ) ≤ ringN n l := by exact_mod_cast three_le_ringN (by omega) l (by omega)
  have hd := ringHeight_dist_ge hn hk (show l < ringK n by omega) hkl
  obtain ⟨-, hL2⟩ := ringSlab_length_mem (by omega) hl1 hl
  obtain ⟨hm1, hm2⟩ := ringHeight_mem (show l < ringK n by omega)
  obtain ⟨-, -, -, hb, ha0, hbn⟩ := ringInterior_facts (by omega) hl1 hl
  have hab' : ((ringState n l).1 : ℝ) ≤ (ringState n (l + 1)).1 := ringState_cast_le (by omega)
  have htl1 : ringQuantile n (ringState n l).1 ≤ ringHeight n l :=
    (le_ringMass_iff ha0 (by linarith) _).1 hm1.le
  have htl2 : ringHeight n l ≤ ringQuantile n (ringState n (l + 1)).1 :=
    (ringMass_le_iff (by linarith) hbn _).1 hm2.le
  set Nk := (ringN n k : ℝ) with hNk
  set Nl := (ringN n l : ℝ) with hNl
  set M := (((max (ringN n k) (ringN n l) : ℕ) : ℝ)) with hMdef
  set d := |ringHeight n k - ringHeight n l| with hddef
  set u := |t - ringHeight n k| with hudef
  have hM : M = max Nk Nl := by rw [hMdef, hNk, hNl]; push_cast; rfl
  have hM2 : (Nk + Nl) / 2 ≤ M := by
    rw [hM]
    rcases le_total Nk Nl with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hu0 : 0 ≤ u := abs_nonneg _
  have hu : u ≤ 1009 * d := by
    have h1 : |t - ringHeight n l| ≤ 27 / Nl := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have h2 : 27 / Nl = 1008 * (3 / (112 * Nl)) := by field_simp; norm_num
    have h3 : u ≤ |t - ringHeight n l| + |ringHeight n l - ringHeight n k| := by
      rw [hudef, show t - ringHeight n k = (t - ringHeight n l) + (ringHeight n l - ringHeight n k)
        by ring]
      exact abs_add_le _ _
    rw [abs_sub_comm (ringHeight n l)] at h3
    linarith
  -- `e^{-M d/2} ≤ e^{-N_k u/4036} e^{-N_l u/4036}`
  have hexp : Real.exp (-(M * d / 2)) ≤ Real.exp (-(Nk / 4036 * u)) * Real.exp (-(Nl / 4036 * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e1 : (Nk + Nl) * u ≤ 2 * M * u := by linarith [mul_le_mul_of_nonneg_right hM2 hu0]
    have e2 : M * u ≤ M * (1009 * d) := mul_le_mul_of_nonneg_left hu (by linarith)
    have : -(Nk / 4036 * u) + -(Nl / 4036 * u) = -((Nk + Nl) * u) / 4036 := by ring
    rw [this]
    linarith
  -- `N_l e^{-N_l u/4036} ≤ 4036 N_k`
  have hNlb : Nl * Real.exp (-(Nl / 4036 * u)) ≤ 4036 * Nk := by
    rcases le_total u 1 with hu1 | hu1
    · have hρt := (ringDensity_interior (by omega) hl1 hl ht).2
      have hρ := ringDensity_le_mul_exp (Nat.cast_nonneg n) (ringHeight n k) t
      have hρk := ringDensity_height_le hn hk
      have he : Real.exp (2 * u) ≤ 9 := by
        have : Real.exp (2 * u) ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)
        have h3 : Real.exp 2 < 9 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          linarith [mul_le_mul_of_nonneg_left Real.exp_one_lt_d9.le (Real.exp_pos 1).le,
            Real.exp_one_lt_d9]
        linarith
      have hρ0 : 0 ≤ ringDensity n (ringHeight n k) := (ringDensity_pos (by positivity) _).le
      have hsq : Nl ^ 2 ≤ (4036 * Nk) ^ 2 :=
        calc Nl ^ 2 ≤ 18 * ringDensity n t := hρt
          _ ≤ 18 * (ringDensity n (ringHeight n k) * Real.exp (2 * |t - ringHeight n k|)) := by
              linarith
          _ ≤ 18 * (ringDensity n (ringHeight n k) * 9) := by
              have := mul_le_mul_of_nonneg_left he hρ0; rw [← hudef]; linarith
          _ ≤ 18 * (3 * Nk ^ 2 * 9) := by linarith
          _ ≤ (4036 * Nk) ^ 2 := by linarith [sq_nonneg Nk]
      have hle : Nl ≤ 4036 * Nk :=
        (pow_le_pow_iff_left₀ (by linarith) (by linarith) two_ne_zero).1 hsq
      have : Real.exp (-(Nl / 4036 * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 ≤ Nl / 4036 * u := by positivity
        linarith)
      calc Nl * Real.exp (-(Nl / 4036 * u)) ≤ Nl * 1 := mul_le_mul_of_nonneg_left this (by linarith)
        _ ≤ 4036 * Nk := by linarith
    · have h1 : Real.exp (-(Nl / 4036 * u)) ≤ Real.exp (-(Nl / 4036)) := by
        apply Real.exp_le_exp.2
        have : Nl / 4036 * 1 ≤ Nl / 4036 * u := mul_le_mul_of_nonneg_left hu1 (by positivity)
        linarith
      have h2 := mul_exp_neg_div_le (show (0 : ℝ) < 4036 by norm_num) (show 0 ≤ Nl by linarith)
      calc Nl * Real.exp (-(Nl / 4036 * u)) ≤ Nl * Real.exp (-(Nl / 4036)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ 4036 := h2
        _ ≤ 4036 * Nk := by linarith
  calc Nl * Real.exp (-(M * d / 2)) ≤
        Nl * (Real.exp (-(Nk / 4036 * u)) * Real.exp (-(Nl / 4036 * u))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = (Nl * Real.exp (-(Nl / 4036 * u))) * Real.exp (-(Nk / 4036 * u)) := by ring
    _ ≤ (4036 * Nk) * Real.exp (-(Nk / 4036 * u)) :=
        mul_le_mul_of_nonneg_right hNlb (Real.exp_pos _).le
    _ = _ := by ring

/-- The bound for an interior row `l ≠ k`:
`e^{-M d/2} ≤ (4/3) 4036 ∫_{I_l} N_k e^{-N_k |t - t_k|/4036}`. -/
theorem exp_neg_le_integral {n k l : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hl1 : 1 ≤ l)
    (hl : l + 1 < ringK n) (hkl : k ≠ l) :
    Real.exp (-(((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l| / 2)) ≤
      4 / 3 * 4036 * ∫ t in ringQuantile n (ringState n l).1..ringQuantile n (ringState n (l + 1)).1,
        (ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) / 4036 * |t - ringHeight n k|)) := by
  have hNl3 : (3 : ℝ) ≤ ringN n l := by exact_mod_cast three_le_ringN (by omega) l (by omega)
  obtain ⟨hL1, -⟩ := ringSlab_length_mem (by omega) hl1 hl
  set α := ringQuantile n (ringState n l).1
  set β := ringQuantile n (ringState n (l + 1)).1
  set E := Real.exp (-(((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l| / 2))
  have hαβ : α ≤ β := by
    have : (0 : ℝ) < 3 / (4 * (ringN n l : ℝ)) := by positivity
    linarith
  have hcont : Continuous fun t => (ringN n k : ℝ) *
      Real.exp (-((ringN n k : ℝ) / 4036 * |t - ringHeight n k|)) :=
    continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).neg))
  have hint := intervalIntegral.integral_mono_on hαβ intervalIntegrable_const
    ((hcont.const_mul 4036).intervalIntegrable (μ := volume) α β)
    (fun t ht => ringSlab_pointwise hn hk hl1 hl hkl ht)
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at hint
  have hLN : 3 / 4 ≤ (β - α) * (ringN n l : ℝ) := by
    have := mul_le_mul_of_nonneg_right hL1 (show (0 : ℝ) ≤ ringN n l by linarith)
    have e : 3 / (4 * (ringN n l : ℝ)) * (ringN n l : ℝ) = 3 / 4 := by field_simp
    linarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc E ≤ 4 / 3 * ((β - α) * (ringN n l : ℝ)) * E := by
        have := mul_le_mul_of_nonneg_right hLN hE0; linarith
    _ = 4 / 3 * ((β - α) * ((ringN n l : ℝ) * E)) := by ring
    _ ≤ 4 / 3 * (4036 * ∫ t in α..β, (ringN n k : ℝ) *
          Real.exp (-((ringN n k : ℝ) / 4036 * |t - ringHeight n k|))) := by linarith
    _ = _ := by ring

/-- **Lemma 5.10 (row-sum bound).** There is an absolute `C_X` such that for `n ≥ 102`, every row `k`
and every `u₀ ≥ 0`,
`∑_{l ≠ k, |t_k - t_l| ≥ u₀} min(N_k, N_l) Θ(max(N_k, N_l) |t_k - t_l|) ≤ C_X N_k e^{-N_k u₀/2}`. -/
theorem ringRowSum_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n → ∀ k < ringK n, ∀ u₀ : ℝ, 0 ≤ u₀ →
    ∑ l ∈ ((range (ringK n)).erase k).filter (fun l => u₀ ≤ |ringHeight n k - ringHeight n l|),
      ((min (ringN n k) (ringN n l) : ℕ) : ℝ) *
        ringTheta (((max (ringN n k) (ringN n l) : ℕ) : ℝ) * |ringHeight n k - ringHeight n l|) ≤
      C * ringN n k * Real.exp (-((ringN n k : ℝ) * u₀ / 2)) := by
  set c₀ : ℝ := 3 / 112
  set A : ℝ := ringTheta c₀ * Real.exp c₀
  have hA : 0 < A := mul_pos (by
    unfold ringTheta
    have h1 : 0 < 1 - Real.exp (-c₀) := by
      have : Real.exp (-c₀) < 1 := Real.exp_lt_one_iff.2 (by norm_num [c₀])
      linarith
    have h2 : 1 - Real.exp (-c₀) < 1 := by linarith [Real.exp_pos (-c₀)]
    have := Real.log_neg h1 h2
    linarith) (Real.exp_pos _)
  refine ⟨A * (2 + 4 / 3 * 4036 * (2 * 4036)), by positivity, fun n hn k hk u₀ hu₀ => ?_⟩
  have hNk3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN (by omega) k hk
  set K := ringK n
  set M := fun l => (((max (ringN n k) (ringN n l) : ℕ) : ℝ))
  set d := fun l => |ringHeight n k - ringHeight n l|
  set F := fun l => if l = k then 0 else Real.exp (-(M l * d l / 2))
  have hF0 : ∀ l, 0 ≤ F l := fun l => by
    simp only [F]; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  -- the separation `M d ≥ c₀` for `l ≠ k`
  have hsep : ∀ l < K, l ≠ k → c₀ ≤ M l * d l := by
    intro l hl hkl
    have hNl3 : (3 : ℝ) ≤ ringN n l := by exact_mod_cast three_le_ringN (by omega) l hl
    have hMl : (ringN n l : ℝ) ≤ M l := by simp only [M]; exact_mod_cast le_max_right _ _
    have hd : 3 / (112 * (ringN n l : ℝ)) ≤ d l := by
      rcases lt_or_gt_of_ne hkl with h | h
      · have := ringHeight_sep hn h hk
        have : 0 < 3 / (112 * (ringN n k : ℝ)) := by positivity
        have : 0 < 3 / (112 * (ringN n l : ℝ)) := by positivity
        simp only [d]; rw [abs_of_nonneg (by linarith)]; linarith
      · have := ringHeight_sep hn h hl
        have : 0 < 3 / (112 * (ringN n l : ℝ)) := by positivity
        have : 0 < 3 / (112 * (ringN n k : ℝ)) := by positivity
        simp only [d]; rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    calc c₀ = (ringN n l : ℝ) * (3 / (112 * (ringN n l : ℝ))) := by simp only [c₀]; field_simp
      _ ≤ M l * d l := mul_le_mul hMl hd (by positivity) (by linarith)
  -- each summand
  have hterm : ∀ l ∈ ((range K).erase k).filter (fun l => u₀ ≤ d l),
      ((min (ringN n k) (ringN n l) : ℕ) : ℝ) * ringTheta (M l * d l) ≤
        (ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) * u₀ / 2)) * A * F l := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hl
    obtain ⟨⟨hkl, hlK⟩, hu⟩ := hl
    have hs := hsep l hlK hkl
    have hθ := ringTheta_le_exp (show (0 : ℝ) < c₀ by norm_num [c₀]) hs
    have hmin : ((min (ringN n k) (ringN n l) : ℕ) : ℝ) ≤ (ringN n k : ℝ) := by exact_mod_cast min_le_left _ _
    have hMk : (ringN n k : ℝ) ≤ M l := by simp only [M]; exact_mod_cast le_max_left _ _
    have hsplit : Real.exp (-(M l * d l)) ≤ Real.exp (-((ringN n k : ℝ) * u₀ / 2)) * Real.exp (-(M l * d l / 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul hMk hu hu₀ (by linarith)]
    have hθ0 : 0 ≤ ringTheta (M l * d l) := ringTheta_nonneg (by norm_num [c₀] at hs ⊢; linarith)
    have hFl : F l = Real.exp (-(M l * d l / 2)) := by simp [F, hkl]
    rw [hFl]
    calc ((min (ringN n k) (ringN n l) : ℕ) : ℝ) * ringTheta (M l * d l) ≤
          (ringN n k : ℝ) * (A * Real.exp (-(M l * d l))) := mul_le_mul hmin hθ hθ0 (by linarith)
      _ ≤ (ringN n k : ℝ) * (A * (Real.exp (-((ringN n k : ℝ) * u₀ / 2)) * Real.exp (-(M l * d l / 2)))) := by gcongr
      _ = _ := by ring
  -- reduce to `∑_{l < K} F l`
  have hsum1 := sum_le_sum hterm
  rw [← mul_sum] at hsum1
  have hsub : ∑ l ∈ ((range K).erase k).filter (fun l => u₀ ≤ d l), F l ≤ ∑ l ∈ range K, F l :=
    sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans (erase_subset _ _))
      fun l _ _ => hF0 l
  -- bound `∑_{l < K} F l`
  have hK2 := two_le_ringK (show 10 ≤ n by omega)
  set h := fun t : ℝ => (ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) / 4036 * |t - ringHeight n k|))
  set a := fun j : ℕ => ringQuantile n (ringState n (j + 1)).1
  have hmid : ∀ j < K - 2, F (j + 1) ≤ 4 / 3 * 4036 * ∫ t in a j..a (j + 1), h t := by
    intro j hj
    simp only [F]
    split_ifs with hjk
    · have hab : a j ≤ a (j + 1) := by
        have := (ringSlab_length_mem (n := n) (k := j + 1) (by omega) (by omega) (by omega)).1
        have : (0 : ℝ) < 3 / (4 * (ringN n (j + 1) : ℝ)) := by
          have : (0 : ℝ) < ringN n (j + 1) := by exact_mod_cast (ringStep_spec_at
            (n := n) (k := j + 1) (by omega)).2.1
          positivity
        simp only [a]; linarith
      have : 0 ≤ ∫ t in a j..a (j + 1), h t := intervalIntegral.integral_nonneg hab fun t _ =>
        (mul_pos (by linarith) (Real.exp_pos _)).le
      positivity
    · exact exp_neg_le_integral hn hk (by omega) (by omega) (Ne.symm hjk)
  have hF1 : ∀ l, F l ≤ 1 := fun l => by
    simp only [F]; split_ifs
    · norm_num
    · exact Real.exp_le_one_iff.2 (by
        have : 0 ≤ M l := by simp only [M]; positivity
        have : 0 ≤ d l := abs_nonneg _
        have : 0 ≤ M l * d l := by positivity
        linarith)
  have hcont : Continuous h := continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).neg))
  have hsplitK : ∑ l ∈ range K, F l = F 0 + ∑ j ∈ range (K - 2), F (j + 1) + F (K - 1) := by
    have e : K = K - 2 + 1 + 1 := by omega
    conv_lhs => rw [e]
    rw [sum_range_succ, sum_range_succ']
    congr 1
    · ring
    · congr 1; omega
  have hmidsum : ∑ j ∈ range (K - 2), F (j + 1) ≤ 4 / 3 * 4036 * (2 * 4036) := by
    calc ∑ j ∈ range (K - 2), F (j + 1) ≤ ∑ j ∈ range (K - 2), 4 / 3 * 4036 * ∫ t in a j..a (j + 1), h t :=
          sum_le_sum fun j hj => hmid j (Finset.mem_range.1 hj)
      _ = 4 / 3 * 4036 * ∫ t in a 0..a (K - 2), h t := by
          rw [← mul_sum, intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
            hcont.intervalIntegrable _ _]
      _ ≤ 4 / 3 * 4036 * (2 * 4036) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have := integral_exp_neg_abs_le (show (0 : ℝ) < (ringN n k : ℝ) / 4036 by positivity) (ringHeight n k)
            (a 0) (a (K - 2))
          have e : ∫ t in a 0..a (K - 2), h t =
              4036 * ∫ t in a 0..a (K - 2), (ringN n k : ℝ) / 4036 * Real.exp (-((ringN n k : ℝ) / 4036 * |t - ringHeight n k|)) := by
            rw [← intervalIntegral.integral_const_mul]
            congr 1; funext t; simp only [h]; ring
          rw [e]; linarith
  have hFsum : ∑ l ∈ range K, F l ≤ 2 + 4 / 3 * 4036 * (2 * 4036) := by
    rw [hsplitK]; linarith [hF1 0, hF1 (K - 1)]
  have hpos : 0 ≤ (ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) * u₀ / 2)) * A := by positivity
  calc _ ≤ (ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) * u₀ / 2)) * A *
        ∑ l ∈ ((range K).erase k).filter (fun l => u₀ ≤ d l), F l := hsum1
    _ ≤ (ringN n k : ℝ) * Real.exp (-((ringN n k : ℝ) * u₀ / 2)) * A * (2 + 4 / 3 * 4036 * (2 * 4036)) :=
        mul_le_mul_of_nonneg_left (hsub.trans hFsum) hpos
    _ = _ := by ring

end Sphere

end SandierSerfaty

end
