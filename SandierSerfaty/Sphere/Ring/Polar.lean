/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Cell

/-!
# The polar rows (sphere note, Lemma 5.8 (G4), Lemma 5.9, polar parts)

* `Sphere.integral_Iic_mul_ringDensity`, `Sphere.integral_Ici_mul_ringDensity`: the first moments of
  `ν` on half-lines, in closed form;
* `Sphere.ringQuantile_sub_slabBary_south`: on the south polar slab `(-∞, τ(b)]` with `2b ≤ n`, the
  barycentre lies at distance `≤ 1` below `τ(b)`; `Sphere.slabBary_sub_ringQuantile_north`: the same
  above `τ(a)` on the north polar slab when `n ≤ 2a`;
* `Sphere.cellPrimitive_half_sub`: `P(n/2, u) - P(n/2, -∞) = (n²/2)(log(1 + w) - w/(1 + w))`,
  `w = e^{2u}`;
* `Sphere.cell_south_le`, `Sphere.cell_north_le`: the polar cell terms are at most `3 N²`;
* `Sphere.ringCell_polar_le`: `Cell_0, Cell_{K-1} ≤ 153 N_k` for `n ≥ 102`.
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty

namespace Sphere

theorem tendsto_mul_exp_two_atBot : Tendsto (fun t : ℝ => t * Real.exp (2 * t)) atBot (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hg : Tendsto (fun t : ℝ => -(2 * t)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_id.const_mul_atBot two_pos)
  have := (h.comp hg).const_mul (-(1 / 2))
  rw [mul_zero] at this
  refine this.congr fun t => ?_
  simp only [Function.comp, pow_one, neg_neg]
  ring

theorem tendsto_mul_exp_neg_two_atTop :
    Tendsto (fun t : ℝ => t * Real.exp (-(2 * t))) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hg : Tendsto (fun t : ℝ => 2 * t) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have := (h.comp hg).const_mul (1 / 2)
  rw [mul_zero] at this
  refine this.congr fun t => ?_
  simp only [Function.comp, pow_one]
  ring

theorem ringMass_eq_exp (n t : ℝ) :
    ringMass n t = n * Real.exp (2 * t) / (1 + Real.exp (2 * t)) := by
  rw [ringMass_eq]
  have hE : Real.exp (-(2 * t)) * Real.exp (2 * t) = 1 := by rw [← Real.exp_add]; simp
  have h1 : 0 < 1 + Real.exp (-(2 * t)) := by positivity
  have h2 : 0 < 1 + Real.exp (2 * t) := by positivity
  rw [div_eq_div_iff h1.ne' h2.ne']
  linear_combination (-n) * hE

theorem sub_ringMass_eq_exp (n t : ℝ) :
    n - ringMass n t = n * Real.exp (-(2 * t)) / (1 + Real.exp (-(2 * t))) := by
  rw [ringMass_eq]
  have h1 : 0 < 1 + Real.exp (-(2 * t)) := by positivity
  field_simp
  ring

/-- `∫_{(-∞, β]} t dν = β Φ(β) - (n/2) log(1 + e^{2β})`. -/
theorem integral_Iic_mul_ringDensity (n β : ℝ) :
    ∫ t in Iic β, t * ringDensity n t =
      β * ringMass n β - n / 2 * Real.log (1 + Real.exp (2 * β)) := by
  have hd : ∀ x, HasDerivAt (fun t => t * ringMass n t - n / 2 * Real.log (1 + Real.exp (2 * t)))
      (x * ringDensity n x) x := fun x => by
    have h1 := (hasDerivAt_id' x).mul (hasDerivAt_ringMass n x)
    have h2 := ((((hasDerivAt_id' x).const_mul 2).exp).const_add 1).log (by positivity)
    refine (h1.sub (h2.const_mul (n / 2))).congr_deriv ?_
    rw [ringMass_eq_exp]
    field_simp
    ring
  have hlim : Tendsto (fun t => t * ringMass n t - n / 2 * Real.log (1 + Real.exp (2 * t))) atBot
      (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (2 * t)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot two_pos)
    have h1 : Tendsto (fun t => t * ringMass n t) atBot (𝓝 0) := by
      have := (tendsto_mul_exp_two_atBot.const_mul n).div (he.const_add 1) (by norm_num)
      rw [mul_zero, zero_div] at this
      refine this.congr fun t => ?_
      simp only [Pi.div_apply]; rw [ringMass_eq_exp]; ring
    have h2 : Tendsto (fun t => Real.log (1 + Real.exp (2 * t))) atBot (𝓝 0) := by
      have := (he.const_add 1).log (by norm_num)
      simpa using this
    have := h1.sub (h2.const_mul (n / 2))
    simpa using this
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_ringDensity n).integrableOn hlim]
  ring

/-- `∫_{[α, ∞)} t dν = α (n - Φ(α)) + (n/2) log(1 + e^{-2α})`. -/
theorem integral_Ici_mul_ringDensity (n α : ℝ) :
    ∫ t in Ici α, t * ringDensity n t =
      α * (n - ringMass n α) + n / 2 * Real.log (1 + Real.exp (-(2 * α))) := by
  have hd : ∀ x, HasDerivAt (fun t => -(t * (n - ringMass n t)) -
      n / 2 * Real.log (1 + Real.exp (-(2 * t)))) (x * ringDensity n x) x := fun x => by
    have h1 := ((hasDerivAt_id' x).mul ((hasDerivAt_ringMass n x).const_sub n)).neg
    have h2 := (((((hasDerivAt_id' x).const_mul 2).neg).exp).const_add 1).log (by positivity)
    refine (h1.sub (h2.const_mul (n / 2))).congr_deriv ?_
    simp only [Pi.neg_apply]
    rw [sub_ringMass_eq_exp]
    field_simp
    ring
  have hlim : Tendsto (fun t => -(t * (n - ringMass n t)) -
      n / 2 * Real.log (1 + Real.exp (-(2 * t)))) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop two_pos))
    have h1 : Tendsto (fun t => t * (n - ringMass n t)) atTop (𝓝 0) := by
      have := (tendsto_mul_exp_neg_two_atTop.const_mul n).div (he.const_add 1) (by norm_num)
      rw [mul_zero, zero_div] at this
      refine this.congr fun t => ?_
      simp only [Pi.div_apply]; rw [sub_ringMass_eq_exp]; ring
    have h2 : Tendsto (fun t => Real.log (1 + Real.exp (-(2 * t)))) atTop (𝓝 0) := by
      have := (he.const_add 1).log (by norm_num)
      simpa using this
    have := h1.neg.sub (h2.const_mul (n / 2))
    simpa using this
  have hint : IntegrableOn (fun t => t * ringDensity n t) (Ioi α) :=
    (integrable_mul_ringDensity n).integrableOn
  rw [integral_Ici_eq_integral_Ioi, integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hint hlim]
  ring

theorem exp_two_mul_ringQuantile {n a : ℝ} (ha : 0 < a) (han : a < n) :
    Real.exp (2 * ringQuantile n a) = a / (n - a) := by
  rw [ringQuantile, show 2 * (Real.log (a / (n - a)) / 2) = Real.log (a / (n - a)) by ring,
    Real.exp_log (div_pos ha (by linarith))]

/-- On the south polar slab with `2 b ≤ n`, `τ(b) - t ≤ 1` for the barycentre `t`. -/
theorem ringQuantile_sub_slabBary_south {n b : ℝ} (hb : 0 < b) (h2b : 2 * b ≤ n) :
    ringQuantile n b - slabBary n 0 b ≤ 1 := by
  have hbn : b < n := by linarith
  have hn : 0 < n := by linarith
  have hset : {t | (0 : ℝ) ≤ ringMass n t ∧ ringMass n t ≤ b} = Iic (ringQuantile n b) := by
    ext t; simp [(ringMass_pos hn t).le, ringMass_le_iff hb hbn]
  set β := ringQuantile n b
  have hβ : ringMass n β = b := ringMass_quantile hb hbn
  have he := exp_two_mul_ringQuantile hb hbn
  rw [slabBary, hset, integral_Iic_mul_ringDensity, hβ, he, sub_zero]
  have hlog : Real.log (1 + b / (n - b)) ≤ b / (n - b) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + b / (n - b) by
      have : 0 < b / (n - b) := div_pos hb (by linarith)
      linarith)
    linarith
  have hnb : 0 < n - b := by linarith
  rw [show β - b⁻¹ * (β * b - n / 2 * Real.log (1 + b / (n - b))) =
    n / (2 * b) * Real.log (1 + b / (n - b)) by field_simp; ring]
  calc n / (2 * b) * Real.log (1 + b / (n - b)) ≤ n / (2 * b) * (b / (n - b)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = n / (2 * (n - b)) := by field_simp
    _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith

/-- On the north polar slab with `n ≤ 2 a`, `t - τ(a) ≤ 1` for the barycentre `t`. -/
theorem slabBary_sub_ringQuantile_north {n a : ℝ} (han : a < n) (h2a : n ≤ 2 * a) :
    slabBary n a n - ringQuantile n a ≤ 1 := by
  have ha : 0 < a := by linarith
  have hn : 0 < n := by linarith
  have hset : {t | a ≤ ringMass n t ∧ ringMass n t ≤ n} = Ici (ringQuantile n a) := by
    ext t; simp [(ringMass_lt hn t).le, le_ringMass_iff ha han]
  set α := ringQuantile n a
  have hα : ringMass n α = a := ringMass_quantile ha han
  have he : Real.exp (-(2 * α)) = (n - a) / a := by
    rw [Real.exp_neg, exp_two_mul_ringQuantile ha han, inv_div]
  rw [slabBary, hset, integral_Ici_mul_ringDensity, hα, he]
  have hna : 0 < n - a := by linarith
  have hlog : Real.log (1 + (n - a) / a) ≤ (n - a) / a := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (n - a) / a by
      have : 0 < (n - a) / a := div_pos hna ha
      linarith)
    linarith
  rw [show (n - a)⁻¹ * (α * (n - a) + n / 2 * Real.log (1 + (n - a) / a)) - α =
    n / (2 * (n - a)) * Real.log (1 + (n - a) / a) by field_simp; ring]
  calc n / (2 * (n - a)) * Real.log (1 + (n - a) / a) ≤ n / (2 * (n - a)) * ((n - a) / a) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = n / (2 * a) := by field_simp
    _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith

/-- `P(n/2, u) - (n²/4 - (n²/2) log 2) = (n²/2)(log(1 + w) - w/(1 + w))` with `w = e^{2u}`. -/
theorem cellPrimitive_half_sub (n u : ℝ) :
    cellPrimitive n (n / 2) u - (n ^ 2 / 4 - n ^ 2 / 2 * Real.log 2) =
      n ^ 2 / 2 * (Real.log (1 + Real.exp (2 * u)) - Real.exp (2 * u) / (1 + Real.exp (2 * u))) := by
  have hE := Real.exp_pos u
  have h2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  have hc : Real.cosh u = Real.exp (-u) * (1 + Real.exp (2 * u)) / 2 := by
    rw [Real.cosh_eq, h2, Real.exp_neg]; field_simp; ring
  have ht : Real.tanh u = (Real.exp (2 * u) - 1) / (Real.exp (2 * u) + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, h2, Real.exp_neg]
    field_simp
  have hw : 0 < 1 + Real.exp (2 * u) := by positivity
  rw [cellPrimitive, ht, hc, Real.log_div (by positivity) two_ne_zero,
    Real.log_mul (Real.exp_pos _).ne' hw.ne', Real.log_exp]
  field_simp
  ring

/-- `log(1 + w) - w/(1 + w) ≤ w²` for `w ≥ 0`. -/
theorem log_one_add_sub_le_sq {w : ℝ} (hw : 0 ≤ w) :
    Real.log (1 + w) - w / (1 + w) ≤ w ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + w by linarith)
  have : w - w / (1 + w) ≤ w ^ 2 := by
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_eq_mul_inv]
    have h1 : 0 < 1 + w := by linarith
    have : w - w ^ 2 ≤ w * (1 + w)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1]; nlinarith
    linarith
  linarith

/-- **South polar cell**: for `0 < b`, `2b ≤ n`, the cell term of the slab `{0 ≤ Φ ≤ b}` with its
barycentre is at most `3 b²`. -/
theorem cell_south_le {n b : ℝ} (hb : 0 < b) (h2b : 2 * b ≤ n) :
    ∫ t in {t | (0 : ℝ) ≤ ringMass n t ∧ ringMass n t ≤ b},
        ((if slabBary n 0 b ≤ t then b - 0 else 0) - (ringMass n t - 0)) ^ 2 ≤ 3 * b ^ 2 := by
  have hbn : b < n := by linarith
  have hn : 0 < n := by linarith
  set s := slabBary n 0 b
  set β := ringQuantile n b
  obtain ⟨hs1, hs2⟩ := barycentre_mem_interior hn le_rfl hb hbn.le
  change 0 < ringMass n s at hs1
  change ringMass n s < b at hs2
  have hsβ : s ≤ β := (ringMass_le_iff hb hbn s).1 hs2.le
  have hβs := ringQuantile_sub_slabBary_south hb h2b
  rw [integral_slab hn le_rfl hb hbn.le hs1.le hs2.le]
  -- the second half: `cB b - P(n/2 - b, s) = ∫_s^β (Φ - b)² ≤ b² (β - s)`
  have hsec : cellBoundary n b - cellPrimitive n (n / 2 - b) s = ∫ t in s..β, (ringMass n t - b) ^ 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cellPrimitive n b x)
      ((continuous_cellIntegrand n b).intervalIntegrable _ _), cellBoundary,
      ite_eq_right hb.ne', ite_eq_right hbn.ne]
  have hsec' : ∫ t in s..β, (ringMass n t - b) ^ 2 ≤ b ^ 2 * 1 := by
    have h := intervalIntegral.integral_mono_on hsβ ((continuous_cellIntegrand n b).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := b ^ 2)) fun t ht => by
        have h1 : ringMass n t ≤ b := (ringMass_le_iff hb hbn t).2 ht.2
        have h0 := ringMass_pos hn t
        rw [show (ringMass n t - b) ^ 2 = (b - ringMass n t) ^ 2 by ring]
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    have : (β - s) * b ^ 2 ≤ 1 * b ^ 2 := mul_le_mul_of_nonneg_right hβs (sq_nonneg _)
    linarith
  -- the first half: `P(n/2, s) - cB 0 ≤ (n²/2) w² ≤ 2 b²`
  have hfirst : cellPrimitive n (n / 2 - 0) s - cellBoundary n 0 ≤ 2 * b ^ 2 := by
    rw [sub_zero, cellBoundary, ite_eq_left rfl, cellPrimitive_half_sub]
    set w := Real.exp (2 * s)
    have hw0 : 0 ≤ w := (Real.exp_pos _).le
    have hΦ : ringMass n s = n * w / (1 + w) := ringMass_eq_exp n s
    have hw : w ≤ 2 * b / n := by
      rw [hΦ] at hs2
      rw [div_lt_iff₀ (by positivity)] at hs2
      rw [le_div_iff₀ hn]; nlinarith
    have h1 := log_one_add_sub_le_sq hw0
    have h2 : w ^ 2 ≤ (2 * b / n) ^ 2 := pow_le_pow_left₀ hw0 hw 2
    calc n ^ 2 / 2 * (Real.log (1 + w) - w / (1 + w)) ≤ n ^ 2 / 2 * (2 * b / n) ^ 2 :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 2 * b ^ 2 := by field_simp
  linarith

/-- **North polar cell**: for `a < n ≤ 2a`, the cell term of the slab `{a ≤ Φ ≤ n}` with its
barycentre is at most `3 (n - a)²`. -/
theorem cell_north_le {n a : ℝ} (han : a < n) (h2a : n ≤ 2 * a) :
    ∫ t in {t | a ≤ ringMass n t ∧ ringMass n t ≤ n},
        ((if slabBary n a n ≤ t then n - a else 0) - (ringMass n t - a)) ^ 2 ≤ 3 * (n - a) ^ 2 := by
  have ha : 0 < a := by linarith
  have hn : 0 < n := by linarith
  set s := slabBary n a n
  set α := ringQuantile n a
  obtain ⟨hs1, hs2⟩ := barycentre_mem_interior hn ha.le han le_rfl
  change a < ringMass n s at hs1
  change ringMass n s < n at hs2
  have hαs : α ≤ s := (le_ringMass_iff ha han s).1 hs1.le
  have hsα := slabBary_sub_ringQuantile_north han h2a
  rw [integral_slab hn ha.le han le_rfl hs1.le hs2.le]
  -- the first half: `P(n/2 - a, s) - cB a = ∫_α^s (Φ - a)² ≤ (n - a)² (s - α)`
  have hfst : cellPrimitive n (n / 2 - a) s - cellBoundary n a = ∫ t in α..s, (ringMass n t - a) ^ 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cellPrimitive n a x)
      ((continuous_cellIntegrand n a).intervalIntegrable _ _), cellBoundary,
      ite_eq_right ha.ne', ite_eq_right han.ne]
  have hfst' : ∫ t in α..s, (ringMass n t - a) ^ 2 ≤ (n - a) ^ 2 * 1 := by
    have h := intervalIntegral.integral_mono_on hαs ((continuous_cellIntegrand n a).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := (n - a) ^ 2)) fun t ht => by
        have h1 : a ≤ ringMass n t := (le_ringMass_iff ha han t).2 ht.1
        have h0 := ringMass_lt hn t
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    have : (s - α) * (n - a) ^ 2 ≤ 1 * (n - a) ^ 2 := mul_le_mul_of_nonneg_right hsα (sq_nonneg _)
    linarith
  -- the second half: `cB n - P(-n/2, s) = P(n/2, -s) - cB 0 ≤ 2 (n - a)²`
  have hsec : cellBoundary n n - cellPrimitive n (n / 2 - n) s ≤ 2 * (n - a) ^ 2 := by
    have hneg : cellPrimitive n (n / 2 - n) s = -cellPrimitive n (n / 2) (-s) := by
      have := cellPrimitive_neg n (-(n / 2)) (-s)
      rw [neg_neg, neg_neg] at this
      rw [show n / 2 - n = -(n / 2) by ring, this]
    rw [hneg, cellBoundary, ite_eq_right hn.ne', ite_eq_left rfl]
    have e := cellPrimitive_half_sub n (-s)
    set w := Real.exp (2 * -s)
    have hw0 : 0 ≤ w := (Real.exp_pos _).le
    have hΦ : n - ringMass n s = n * w / (1 + w) := by
      rw [sub_ringMass_eq_exp]; simp only [w, mul_neg]
    have hw : w ≤ 2 * (n - a) / n := by
      have h' : n - ringMass n s < n - a := by linarith
      rw [hΦ, div_lt_iff₀ (by positivity)] at h'
      rw [le_div_iff₀ hn]; nlinarith
    have h1 := log_one_add_sub_le_sq hw0
    have h2 : w ^ 2 ≤ (2 * (n - a) / n) ^ 2 := pow_le_pow_left₀ hw0 hw 2
    have h3 : n ^ 2 / 2 * (Real.log (1 + w) - w / (1 + w)) ≤ 2 * (n - a) ^ 2 :=
      calc n ^ 2 / 2 * (Real.log (1 + w) - w / (1 + w)) ≤ n ^ 2 / 2 * (2 * (n - a) / n) ^ 2 :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = 2 * (n - a) ^ 2 := by field_simp
    linarith
  linarith

/-! ### The polar rows of `Y_n` -/

theorem ringN_zero {n : ℕ} (hn : 10 ≤ n) : ringN n 0 = 3 := by
  have hst : ringState n 1 = ringStep n (0, 0, 0) := rfl
  have hround : ringRound n 0 = 3 := by
    have : ⌊ringTarget n 0 + 1 / 2⌋₊ = 0 := Nat.floor_eq_zero.2 (by norm_num [ringTarget])
    unfold ringRound; rw [this]; rfl
  have h1 : ¬ n ≤ 0 := by omega
  have h9 : ¬ n - 0 ≤ 2 * ringRound n 0 + 3 := by rw [hround]; omega
  unfold ringN
  rw [hst]
  unfold ringStep
  rw [ite_eq_right h1, ite_eq_right h9]
  split_ifs with hC
  · simp at hC
  · exact hround

/-- **Lemma 5.9, south polar row**: `Cell_0 ≤ 27` for `n ≥ 102`. -/
theorem ringCell_south_le {n : ℕ} (hn : 102 ≤ n) : (ringRows n).cell 0 ≤ 27 := by
  have hK := two_le_ringK (show 10 ≤ n by omega)
  have hs := ringStep_spec_at (n := n) (k := 0) (by omega)
  have h0 : ((ringState n 0).1 : ℝ) = 0 := by simp [ringState]
  have hb : ((ringState n 1).1 : ℝ) = 3 := by
    rw [hs.1, ringN_zero (by omega)]; simp [ringState]
  have hn' : (6 : ℝ) ≤ n := by exact_mod_cast (show 6 ≤ n by omega)
  rw [ringRows_cell_eq (by omega), ringHeight_eq_slabBary (by omega), h0, hb]
  have := cell_south_le (n := (n : ℝ)) (b := 3) (by norm_num) (by linarith)
  norm_num at this ⊢
  linarith

/-- **Lemma 5.9, north polar row**: `Cell_{K-1} ≤ 3 N_{K-1}²` for `n ≥ 102`. -/
theorem ringCell_north_le {n : ℕ} (hn : 102 ≤ n) :
    (ringRows n).cell (ringK n - 1) ≤ 3 * (ringN n (ringK n - 1) : ℝ) ^ 2 := by
  have hK := two_le_ringK (show 10 ≤ n by omega)
  have hk : ringK n - 1 < ringK n := by omega
  have hs := ringStep_spec_at hk
  have hfin : (ringState n (ringK n - 1 + 1)).1 = n := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ ringK n)]; exact ringState_ringK n
  have h51 := (hs.2.2.1 hfin).1
  have hlt : (ringState n (ringK n - 1)).1 < n := ringState_lt_of_lt_ringK hk
  have hN : ((ringN n (ringK n - 1)) : ℝ) = n - (ringState n (ringK n - 1)).1 := by
    have := hs.1; rw [hfin] at this
    have : ringN n (ringK n - 1) = n - (ringState n (ringK n - 1)).1 := by omega
    rw [this]; push_cast [hlt.le]; ring
  have hfin' : ((ringState n (ringK n - 1 + 1)).1 : ℝ) = n := by rw [hfin]
  have ha2 : (n : ℝ) ≤ 2 * (ringState n (ringK n - 1)).1 := by
    exact_mod_cast (show n ≤ 2 * (ringState n (ringK n - 1)).1 by omega)
  rw [ringRows_cell_eq hk, ringHeight_eq_slabBary hk, hfin', hN]
  exact cell_north_le (by exact_mod_cast hlt) ha2

/-- **Lemma 5.9, polar rows**: `Cell_k ≤ 153 N_k` for `k = 0` and `k = K - 1`, `n ≥ 102`. -/
theorem ringCell_polar_le {n k : ℕ} (hn : 102 ≤ n) (hk : k = 0 ∨ k = ringK n - 1) :
    (ringRows n).cell k ≤ 153 * (ringN n k : ℝ) := by
  have hK := two_le_ringK (show 10 ≤ n by omega)
  rcases hk with rfl | rfl
  · rw [ringN_zero (by omega)]
    have := ringCell_south_le hn
    push_cast; linarith
  · have h := ringCell_north_le hn
    have h51 : (ringN n (ringK n - 1) : ℝ) ≤ 51 := by exact_mod_cast ringN_last_le (by omega)
    have h0 : (0 : ℝ) ≤ ringN n (ringK n - 1) := Nat.cast_nonneg _
    nlinarith

end Sphere

end SandierSerfaty

end
