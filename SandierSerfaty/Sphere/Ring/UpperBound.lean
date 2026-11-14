/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Bands
public import SandierSerfaty.Sphere.Ring.BandBound
public import SandierSerfaty.Sphere.Ring.OnSphere

/-!
# The ring upper bound (sphere note, Theorem 5.13)

* `Sphere.sum_exp_neg_succ_le`, `Sphere.sum_band_exp_le`: the geometric sums over a band;
* `Sphere.one_third_le_ringAspect`: `x_k ≥ 1/3` for every row (G5);
* `Sphere.ringCB1`, `Sphere.ringCB2`: the constants of Proposition 5.12 (i), (ii) (chosen);
* `Sphere.ringRows_rowB_sub_le_bulk`, `Sphere.sum_ringRows_rowB_sub_le_bulk`: bulk rows, per row and
  summed over the bands; `Sphere.sum_ringRows_rowB_sub_le_not_bulk`: non-bulk rows;
* `Sphere.sum_ringRows_rowB_le`: `∑_k B_k ≤ n e(√3π) + C n^{3/4}` for `n ≥ 102`;
* `Sphere.normalizedEnergy_ringConfig_le_ring`: **Theorem 5.13**,
  `𝔎(Y_n) ≤ C_ring n + C n^{3/4}` for `n ≥ 102`.

The proof follows the sphere note. Proposition 5.12 (i) bounds the non-bulk rows, which hold
`O(N_cap³) = O(n^{3/4})` points (G6). On bulk rows, Proposition 5.12 (ii), the Lipschitz bound for `e`
on `[1/3, ∞)` and (G5) give `B_k - N_k e(√3π) ≤ C (T + 1) + C + C √n (e^{-a_k/C} + e^{-b_k/C})`, where
`a_k, b_k` are the distances to the two ends of the band of `k`. The geometric sums are `O(1)` per band,
and there are `O(K/T + 1) = O(n^{1/4})` bands (G6).
-/

open Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- `∑_{m < M} e^{-(m+1)/C} ≤ (1 - e^{-1/C})⁻¹`. -/
theorem sum_exp_neg_succ_le {C : ℝ} (hC : 0 < C) (M : ℕ) :
    ∑ m ∈ range M, Real.exp (-(((m + 1 : ℕ) : ℝ) / C)) ≤ (1 - Real.exp (-(1 / C)))⁻¹ := by
  set x := Real.exp (-(1 / C))
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x < 1 := Real.exp_lt_one_iff.2 (by have := one_div_pos.2 hC; linarith)
  have e : ∀ m : ℕ, Real.exp (-(((m + 1 : ℕ) : ℝ) / C)) = x ^ (m + 1) := fun m => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp_rw [e]
  calc ∑ m ∈ range M, x ^ (m + 1) ≤ ∑ m ∈ range M, x ^ m :=
        sum_le_sum fun m _ => pow_le_pow_of_le_one hx0 hx1.le (Nat.le_succ m)
    _ ≤ ∑' m : ℕ, x ^ m :=
        (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ (fun m _ => pow_nonneg hx0 m)
    _ = (1 - x)⁻¹ := tsum_geometric_of_lt_one hx0 hx1

/-- The geometric sums over a band `[s, h]`: `∑_{k ∈ [s, h]} (e^{-(k-s+1)/C} + e^{-(h-k+1)/C}) ≤ 2G`. -/
theorem sum_band_exp_le {C : ℝ} (hC : 0 < C) (s h : ℕ) :
    ∑ k ∈ Icc s h, (Real.exp (-(((k - s + 1 : ℕ) : ℝ) / C)) +
      Real.exp (-(((h - k + 1 : ℕ) : ℝ) / C))) ≤ 2 * (1 - Real.exp (-(1 / C)))⁻¹ := by
  rw [sum_add_distrib, two_mul]
  refine add_le_add ?_ ?_
  · rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    refine le_trans (le_of_eq (sum_congr rfl fun m _ => ?_)) (sum_exp_neg_succ_le hC (h + 1 - s))
    rw [show s + m - s + 1 = m + 1 by omega]
  · have hsub : Icc s h ⊆ range (h + 1) := fun k hk => mem_range.2 (by have := (mem_Icc.1 hk).2; omega)
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans ?_
    have := sum_range_reflect (fun m => Real.exp (-(((m + 1 : ℕ) : ℝ) / C))) (h + 1)
    rw [show h + 1 - 1 = h by omega] at this
    rw [this]
    exact sum_exp_neg_succ_le hC (h + 1)

/-- **(G5)** for every row: `x_k ≥ 1/3`. -/
theorem one_third_le_ringAspect {n k : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) :
    1 / 3 ≤ (ringRows n).aspect k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hasp : (ringRows n).aspect k = (ringN n k : ℝ) ^ 2 / ringDensity n (ringHeight n k) := by
    rw [RowConfig.aspect, ringRows_card]; rfl
  have hρ := ringDensity_height_le hn hk
  have hρ0 := ringDensity_pos hn' (ringHeight n k)
  rw [hasp, le_div_iff₀ hρ0]
  linarith

theorem ringLip_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ ringLip a := by
  unfold ringLip
  have h1 : 0 < 1 - Real.exp (-a) := by
    have := Real.exp_lt_one_iff.2 (show -a < 0 by linarith); linarith
  have h2 : 0 ≤ ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(((m + 1 : ℕ) : ℝ) * a)) :=
    tsum_nonneg fun m => by positivity
  positivity

theorem one_third_le_sqrt_three_mul_pi : (1 / 3 : ℝ) ≤ Real.sqrt 3 * Real.pi := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have := Real.pi_gt_three
  nlinarith

/-- The fourth root `q = n^{1/4}`: `q ≥ 1`, `q⁴ = n`, `q ≤ T ≤ q + 1`. -/
theorem fourth_root_facts {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) ∧ ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n ∧
      (n : ℝ) ^ (1 / 4 : ℝ) ≤ ringTol n ∧ (ringTol n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) + 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq1 : 1 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hn' (by norm_num)
  refine ⟨hq1, ?_, Nat.le_ceil _, (Nat.ceil_lt_add_one (by linarith)).le⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  norm_num

/-- `n^{3/4} = q³`. -/
theorem rpow_three_fourths {n : ℕ} : (n : ℝ) ^ (3 / 4 : ℝ) = ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

/-! ### The constants of Proposition 5.12 -/

/-- The constant of Proposition 5.12 (i). -/
noncomputable def ringCB1 : ℝ := Classical.choose ringRows_rowB_le

theorem ringCB1_spec : 0 < ringCB1 ∧ ∀ n : ℕ, 102 ≤ n → ∀ k < ringK n,
    (ringRows n).rowB k ≤ ringCB1 * ringN n k :=
  Classical.choose_spec ringRows_rowB_le

/-- The constant of Proposition 5.12 (ii). -/
noncomputable def ringCB2 : ℝ := Classical.choose ringRows_rowB_le_band

theorem ringCB2_spec : 0 < ringCB2 ∧ ∀ n : ℕ, 102 ≤ n → ∀ lo hi k : ℕ, hi < ringK n →
    RingBulk n lo → (∀ j, lo < j → j ≤ hi → RingCRow n j) → lo ≤ k → k ≤ hi →
    (ringRows n).rowB k ≤ (ringN n k : ℝ) * ringAspectEnergy ((ringRows n).aspect k) + ringCB2 +
      ringCB2 * ringN n k * Real.exp (-(((min (k - lo + 1) (hi - k + 1) : ℕ) : ℝ) / ringCB2)) :=
  Classical.choose_spec ringRows_rowB_le_band

/-- The constant `C_a = 42 + 324 e^{18}` of (G5) in the bulk. -/
noncomputable def ringCa : ℝ := 42 + 324 * Real.exp 18

theorem ringCa_pos : 0 < ringCa := by unfold ringCa; positivity

/-- The geometric constant `G = (1 - e^{-1/C})⁻¹` of the band sums. -/
noncomputable def ringCG : ℝ := (1 - Real.exp (-(1 / ringCB2)))⁻¹

theorem ringCG_pos : 0 < ringCG := by
  have h := one_div_pos.2 ringCB2_spec.1
  have := Real.exp_lt_one_iff.2 (show -(1 / ringCB2) < 0 by linarith)
  exact inv_pos.2 (by linarith)

/-! ### Bulk rows -/

/-- **A bulk row in a band `[s, h]`**:
`B_k - N_k e(√3π) ≤ L C_a (T + 1) + C + 3 C √n (e^{-(k-s+1)/C} + e^{-(h-k+1)/C})`. -/
theorem ringRows_rowB_sub_le_bulk {n k s h : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hb : RingBulk n k)
    (hst : RingBandStart n s) (hsk : s ≤ k) (hkh : k ≤ h) (hhK : h < ringK n)
    (hband : ∀ j, s < j → j ≤ h → RingCRow n j) :
    (ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi) ≤
      ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2 +
        3 * ringCB2 * Real.sqrt n * (Real.exp (-(((k - s + 1 : ℕ) : ℝ) / ringCB2)) +
          Real.exp (-(((h - k + 1 : ℕ) : ℝ) / ringCB2))) := by
  obtain ⟨hC₂, hB2⟩ := ringCB2_spec
  have h1 := hB2 n hn s h k hhK hst.2.1 hband hsk hkh
  obtain ⟨hk1, hk'⟩ := ringBulk_interior hk hb
  have hN0 : (0 : ℝ) < ringN n k := by exact_mod_cast ringRows_N_pos (n := n) hk
  have hNq : (ringN n k : ℝ) ≤ 3 * Real.sqrt n := by
    have := Real.sqrt_le_sqrt (ringN_sq_le (by omega) hk1 hk')
    rwa [Real.sqrt_sq hN0.le, Real.sqrt_mul (by norm_num),
      show Real.sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  set E := Real.exp (-(((k - s + 1 : ℕ) : ℝ) / ringCB2)) + Real.exp (-(((h - k + 1 : ℕ) : ℝ) / ringCB2))
  set X := Real.exp (-(((min (k - s + 1) (h - k + 1) : ℕ) : ℝ) / ringCB2))
  have hexp : X ≤ E := by
    simp only [X, E]
    rcases min_choice (k - s + 1) (h - k + 1) with e | e <;> rw [e]
    · linarith [Real.exp_pos (-(((h - k + 1 : ℕ) : ℝ) / ringCB2))]
    · linarith [Real.exp_pos (-(((k - s + 1 : ℕ) : ℝ) / ringCB2))]
  have h2 : ringCB2 * ringN n k * X ≤ 3 * ringCB2 * Real.sqrt n * E := by
    have h4 := mul_le_mul hNq hexp (Real.exp_pos _).le (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h4 hC₂.le
    calc ringCB2 * ringN n k * X = ringCB2 * ((ringN n k : ℝ) * X) := by ring
      _ ≤ ringCB2 * (3 * Real.sqrt n * E) := h5
      _ = 3 * ringCB2 * Real.sqrt n * E := by ring
  -- the Lipschitz term
  have hL := ringLip_nonneg (a := 1 / 3) (by norm_num)
  have hlip := abs_ringAspectEnergy_sub_le (a := 1 / 3) (by norm_num) (one_third_le_ringAspect hn hk)
    one_third_le_sqrt_three_mul_pi
  have hasp := ringAspect_sub_le hn hk hb
  set D := |(ringRows n).aspect k - Real.sqrt 3 * Real.pi|
  have a2 : (ringN n k : ℝ) * D ≤ ringCa * ((ringTol n : ℝ) + 1) := by
    rw [le_div_iff₀ hN0] at hasp; unfold ringCa; linarith
  have h3 : (ringN n k : ℝ) * (ringAspectEnergy ((ringRows n).aspect k) -
      ringAspectEnergy (Real.sqrt 3 * Real.pi)) ≤ ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) := by
    calc (ringN n k : ℝ) * (ringAspectEnergy ((ringRows n).aspect k) -
          ringAspectEnergy (Real.sqrt 3 * Real.pi))
        ≤ (ringN n k : ℝ) * (ringLip (1 / 3) * D) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hlip) hN0.le
      _ = ringLip (1 / 3) * ((ringN n k : ℝ) * D) := by ring
      _ ≤ ringLip (1 / 3) * (ringCa * ((ringTol n : ℝ) + 1)) := mul_le_mul_of_nonneg_left a2 hL
      _ = ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) := by ring
  linarith

open scoped Classical in
/-- **The bulk rows**: `∑_{bulk} (B_k - N_k e(√3π)) ≤ K (L C_a (T + 1) + C) + 6 C G √n · #bands`. -/
theorem sum_ringRows_rowB_sub_le_bulk {n : ℕ} (hn : 102 ≤ n) :
    ∑ k ∈ (range (ringK n)).filter (fun k => RingBulk n k),
        ((ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi)) ≤
      ringK n * (ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2) +
        3 * ringCB2 * Real.sqrt n *
          (2 * ringCG * (((range (ringK n)).filter fun s => RingBandStart n s).card : ℝ)) := by
  have hC₂ := ringCB2_spec.1
  have hlo : ∀ k, ∃ s, k < ringK n ∧ RingBulk n k →
      s ≤ k ∧ RingBandStart n s ∧ ∀ j, s < j → j ≤ k → RingCRow n j := fun k => by
    by_cases hk : k < ringK n ∧ RingBulk n k
    · obtain ⟨s, hs⟩ := exists_ringBand_start k hk.1 hk.2
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose lo hlo using hlo
  have hH : ∀ s, ∃ h, s < ringK n →
      s ≤ h ∧ h < ringK n ∧ (∀ j, s < j → j ≤ h → RingCRow n j) ∧ ¬ RingCRow n (h + 1) := fun s => by
    by_cases hs : s < ringK n
    · obtain ⟨h, hh⟩ := exists_ringBand_end hs
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose H hH using hH
  let F : ℕ → ℝ := fun k => Real.exp (-(((k - lo k + 1 : ℕ) : ℝ) / ringCB2)) +
    Real.exp (-(((H (lo k) - k + 1 : ℕ) : ℝ) / ringCB2))
  let B := (range (ringK n)).filter (fun k => RingBulk n k)
  let St := (range (ringK n)).filter fun s => RingBandStart n s
  have hrow : ∀ k ∈ B, (ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi) ≤
      ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2 + 3 * ringCB2 * Real.sqrt n * F k := by
    intro k hk
    obtain ⟨hk, hb⟩ := mem_filter.1 hk
    have hk := mem_range.1 hk
    obtain ⟨hsk, hst, hband⟩ := hlo k ⟨hk, hb⟩
    obtain ⟨hsh, hhK, hband', hC⟩ := hH (lo k) hst.1
    exact ringRows_rowB_sub_le_bulk hn hk hb hst hsk (le_of_ringBand_end hband hsh hC) hhK hband'
  have hsumF : ∑ k ∈ B, F k ≤ 2 * ringCG * St.card := by
    have hmaps : ∀ k ∈ B, lo k ∈ St := fun k hk => by
      obtain ⟨hk, hb⟩ := mem_filter.1 hk
      have := (hlo k ⟨mem_range.1 hk, hb⟩).2.1
      exact mem_filter.2 ⟨mem_range.2 this.1, this⟩
    rw [← sum_fiberwise_of_maps_to hmaps, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun s hs => ?_
    have hs' := (mem_filter.1 hs).2
    obtain ⟨hsh, -, -, hC⟩ := hH s hs'.1
    have hsub : B.filter (fun k => lo k = s) ⊆ Icc s (H s) := by
      intro k hk
      obtain ⟨hk, hks⟩ := mem_filter.1 hk
      obtain ⟨hk, hb⟩ := mem_filter.1 hk
      obtain ⟨hsk, -, hband⟩ := hlo k ⟨mem_range.1 hk, hb⟩
      rw [hks] at hsk hband
      exact mem_Icc.2 ⟨hsk, le_of_ringBand_end hband hsh hC⟩
    calc ∑ k ∈ B.filter (fun k => lo k = s), F k
        = ∑ k ∈ B.filter (fun k => lo k = s), (Real.exp (-(((k - s + 1 : ℕ) : ℝ) / ringCB2)) +
            Real.exp (-(((H s - k + 1 : ℕ) : ℝ) / ringCB2))) :=
          sum_congr rfl fun k hk => by simp only [F]; rw [(mem_filter.1 hk).2]
      _ ≤ ∑ k ∈ Icc s (H s), (Real.exp (-(((k - s + 1 : ℕ) : ℝ) / ringCB2)) +
            Real.exp (-(((H s - k + 1 : ℕ) : ℝ) / ringCB2))) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ 2 * ringCG := sum_band_exp_le hC₂ s (H s)
  have hc : (B.card : ℝ) ≤ ringK n := by
    have := card_filter_le (range (ringK n)) (fun k => RingBulk n k)
    rw [card_range] at this
    exact_mod_cast this
  have hL := ringLip_nonneg (a := 1 / 3) (by norm_num)
  have hCa := ringCa_pos
  have hG := ringCG_pos
  calc ∑ k ∈ B, ((ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi))
      ≤ ∑ k ∈ B, (ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2 +
          3 * ringCB2 * Real.sqrt n * F k) := sum_le_sum hrow
    _ = (B.card : ℝ) * (ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2) +
          3 * ringCB2 * Real.sqrt n * ∑ k ∈ B, F k := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (by positivity))
          (mul_le_mul_of_nonneg_left hsumF (by positivity))

/-! ### Non-bulk rows -/

open scoped Classical in
/-- **The non-bulk rows**:
`∑_{non-bulk} (B_k - N_k e(√3π)) ≤ (C + |e(√3π)|)(2 N_cap² + 1)((5/4) N_cap + 51)`. -/
theorem sum_ringRows_rowB_sub_le_not_bulk {n : ℕ} (hn : 102 ≤ n) :
    ∑ k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k),
        ((ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi)) ≤
      (ringCB1 + |ringAspectEnergy (Real.sqrt 3 * Real.pi)|) *
        ((2 * (ringCap n : ℝ) ^ 2 + 1) * (5 / 4 * ringCap n + 51)) := by
  obtain ⟨hC₁, hB1⟩ := ringCB1_spec
  set e₀ := ringAspectEnergy (Real.sqrt 3 * Real.pi)
  have hnon : ∀ k < ringK n, (ringRows n).rowB k - ringN n k * e₀ ≤ (ringCB1 + |e₀|) * ringN n k := by
    intro k hk
    have h1 := hB1 n hn k hk
    have hN : (0 : ℝ) ≤ ringN n k := Nat.cast_nonneg _
    have h2 : -(ringN n k * e₀) ≤ |e₀| * ringN n k := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le e₀) hN
      linarith
    linarith
  calc _ ≤ ∑ k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k),
        (ringCB1 + |e₀|) * (ringN n k : ℝ) :=
        sum_le_sum fun k hk => hnon k (mem_range.1 (mem_filter.1 hk).1)
    _ = (ringCB1 + |e₀|) *
          ∑ k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k), (ringN n k : ℝ) := by
        rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_ringN_not_bulk_le (by omega)) (by positivity)

/-! ### Theorem 5.13 -/

/-- The bulk total in terms of `q = n^{1/4}`. -/
theorem bulk_total_le {n : ℕ} (hn : 102 ≤ n) {K S : ℝ} (hK : K ≤ 4 * Real.sqrt n + 4)
    (hS : S ≤ 44 * K / ringTol n + 1) :
    K * (ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2) +
        3 * ringCB2 * Real.sqrt n * (2 * ringCG * S) ≤
      (8 * (3 * ringLip (1 / 3) * ringCa + ringCB2) + 2118 * ringCB2 * ringCG) *
        ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 3 := by
  obtain ⟨hq1, hq4, hqT, hTq⟩ := fourth_root_facts (show 1 ≤ n by omega)
  set q := (n : ℝ) ^ (1 / 4 : ℝ)
  have hsqrt : Real.sqrt n = q ^ 2 := by
    rw [← hq4, show q ^ 4 = (q ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsqrt] at hK ⊢
  have hL := ringLip_nonneg (a := 1 / 3) (by norm_num)
  have hCa := ringCa_pos
  have hC₂ := ringCB2_spec.1
  have hG := ringCG_pos
  have hKq : K ≤ 8 * q ^ 2 := by nlinarith
  have hA : K * (ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2) ≤
      8 * (3 * ringLip (1 / 3) * ringCa + ringCB2) * q ^ 3 := by
    have h1 : ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2 ≤
        (3 * ringLip (1 / 3) * ringCa + ringCB2) * q := by
      have := mul_le_mul_of_nonneg_left (show (ringTol n : ℝ) + 1 ≤ 3 * q by linarith)
        (by positivity : 0 ≤ ringLip (1 / 3) * ringCa)
      nlinarith
    calc K * (ringLip (1 / 3) * ringCa * ((ringTol n : ℝ) + 1) + ringCB2)
        ≤ (8 * q ^ 2) * ((3 * ringLip (1 / 3) * ringCa + ringCB2) * q) :=
          mul_le_mul hKq h1 (by positivity) (by positivity)
      _ = 8 * (3 * ringLip (1 / 3) * ringCa + ringCB2) * q ^ 3 := by ring
  have hB : 3 * ringCB2 * q ^ 2 * (2 * ringCG * S) ≤ 2118 * ringCB2 * ringCG * q ^ 3 := by
    have hT0 : (0 : ℝ) < ringTol n := by linarith
    have hKT : 44 * K / ringTol n ≤ 352 * q := by
      rw [div_le_iff₀ hT0]
      have := mul_le_mul_of_nonneg_left hqT (show (0 : ℝ) ≤ 352 * q by positivity)
      linarith
    have hS' : S ≤ 353 * q := by linarith
    have := mul_le_mul_of_nonneg_left hS' (show 0 ≤ 6 * ringCB2 * ringCG * q ^ 2 by positivity)
    calc 3 * ringCB2 * q ^ 2 * (2 * ringCG * S) = 6 * ringCB2 * ringCG * q ^ 2 * S := by ring
      _ ≤ 6 * ringCB2 * ringCG * q ^ 2 * (353 * q) := this
      _ = 2118 * ringCB2 * ringCG * q ^ 3 := by ring
  linarith

/-- The non-bulk total in terms of `q = n^{1/4}`. -/
theorem not_bulk_total_le {n : ℕ} (hn : 102 ≤ n) {A : ℝ} (hA : 0 ≤ A) :
    A * ((2 * (ringCap n : ℝ) ^ 2 + 1) * (5 / 4 * ringCap n + 51)) ≤
      511599 * A * ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 3 := by
  obtain ⟨hq1, -, -, hTq⟩ := fourth_root_facts (show 1 ≤ n by omega)
  set q := (n : ℝ) ^ (1 / 4 : ℝ)
  have hcap : (ringCap n : ℝ) ≤ 48 * q := by
    have h1 : ringCap n ≤ 40 + 4 * ringTol n := max_le (by omega) (by omega)
    have h2 : (ringCap n : ℝ) ≤ 40 + 4 * (ringTol n : ℝ) := by exact_mod_cast h1
    linarith
  have hcap0 : (0 : ℝ) ≤ ringCap n := Nat.cast_nonneg _
  have h1 : 2 * (ringCap n : ℝ) ^ 2 + 1 ≤ 4609 * q ^ 2 := by nlinarith
  have h2 : 5 / 4 * (ringCap n : ℝ) + 51 ≤ 111 * q := by linarith
  have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  calc A * ((2 * (ringCap n : ℝ) ^ 2 + 1) * (5 / 4 * ringCap n + 51))
      ≤ A * (4609 * q ^ 2 * (111 * q)) := mul_le_mul_of_nonneg_left h3 hA
    _ = 511599 * A * q ^ 3 := by ring

open scoped Classical in
/-- **Theorem 5.13, the row sums**: `∑_k B_k ≤ n e(√3π) + C n^{3/4}` for `n ≥ 102`. -/
theorem sum_ringRows_rowB_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n →
    ∑ k ∈ range (ringK n), (ringRows n).rowB k ≤
      n * ringAspectEnergy (Real.sqrt 3 * Real.pi) + C * (n : ℝ) ^ (3 / 4 : ℝ) := by
  have hL := ringLip_nonneg (a := 1 / 3) (by norm_num)
  have hCa := ringCa_pos
  have hC₁ := ringCB1_spec.1
  have hC₂ := ringCB2_spec.1
  have hG := ringCG_pos
  refine ⟨(8 * (3 * ringLip (1 / 3) * ringCa + ringCB2) + 2118 * ringCB2 * ringCG) +
    511599 * (ringCB1 + |ringAspectEnergy (Real.sqrt 3 * Real.pi)|), by positivity, fun n hn => ?_⟩
  rw [rpow_three_fourths]
  have hsplit : ∑ k ∈ range (ringK n), (ringRows n).rowB k =
      n * ringAspectEnergy (Real.sqrt 3 * Real.pi) +
        (∑ k ∈ (range (ringK n)).filter (fun k => RingBulk n k),
          ((ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi)) +
        ∑ k ∈ (range (ringK n)).filter (fun k => ¬ RingBulk n k),
          ((ringRows n).rowB k - ringN n k * ringAspectEnergy (Real.sqrt 3 * Real.pi))) := by
    rw [sum_filter_add_sum_filter_not, sum_sub_distrib, ← sum_mul, sum_ringN]
    ring
  rw [hsplit]
  have h1 := (sum_ringRows_rowB_sub_le_bulk hn).trans
    (bulk_total_le hn (ringK_le (by omega)) (card_ringBandStart_le (by omega)))
  have h2 := (sum_ringRows_rowB_sub_le_not_bulk hn).trans
    (not_bulk_total_le hn (A := ringCB1 + |ringAspectEnergy (Real.sqrt 3 * Real.pi)|) (by positivity))
  linarith

/-- **Theorem 5.13** (sphere note): there is an absolute `C` with `𝔎(Y_n) ≤ C_ring n + C n^{3/4}` for
`n ≥ 102`. -/
theorem normalizedEnergy_ringConfig_le_ring : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n →
    normalizedEnergy (ringConfig n) ≤ ringConstant * n + C * (n : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, h⟩ := sum_ringRows_rowB_le
  refine ⟨C, hC, fun n hn => ?_⟩
  rw [normalizedEnergy_ringConfig, ringConstant]
  have := h n hn
  linarith

end Sphere

end SandierSerfaty

end
