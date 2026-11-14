/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.SectorDeriv

/-!
# `H + log r` is Lipschitz across a site

Near a site `p`, `H = -log r + H₁` with `H₁(z) = Bl(‖z - p‖) + serF(‖z - p‖, gauge)`, where
`Bl r = B r + log r` for `r ≠ 0` and `Bl 0 = 0`. Because `|Bl r| ≤ C r²`, `|Bl'| ≤ C r`, and the
series is `O(g⁶)`, the function `H₁` is Lipschitz on a ball about `p` and vanishes at `p`
(`lipschitzOnWith_H1`). Consequently `h - H`, where `h = s - log r` is the Green potential with
smooth `s`, is Lipschitz across the site with value `s(p)` there (zero constant term of `H`).
-/

open Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

variable {ι : Type*} {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ} {p z : ℂ}

theorem gauge_zero (hS : SepSites P d₀) (hp : p ∈ P) : gauge P p 0 = 0 := by
  refine le_antisymm ?_ (gauge_nonneg hS hp 0)
  rw [gauge_le_iff hS hp]
  intro q _
  simp [gaugeLin]

/-- `Bl r = B r + log r` for `r ≠ 0`, and `0` at `0`. -/
@[expose] noncomputable def Bl (R : RadialData ι) (r : ℝ) : ℝ :=
  if r = 0 then 0 else R.B r + Real.log r

theorem serF_zero (hR : R.IsAdmissible d₀) : serF R (0, 0) = 0 := by
  unfold serF termFn
  have h0 : ∀ i, (0 : ℝ) ^ R.k i * R.D i 0 = 0 := fun i => by
    have : R.k i ≠ 0 := by have := hR.six_le i; omega
    simp [this]
  simp [h0]

theorem abs_serF_le_dist (hR : R.IsAdmissible d₀) {T₀ : ℝ} {M : ι → ℝ} (hM : Bnd R d₀ T₀ M)
    (hd : 0 < d₀) (hT : d₀ ≤ T₀) {y : ℝ × ℝ} (hy : y ∈ cone d₀ T₀) :
    |serF R y| ≤ ((∑' i, M i) / d₀) * dist y (0, 0) := by
  have hsn : 0 ≤ ∑' i, M i := tsum_nonneg fun i => hM.nonneg hd hT i
  have h1 := abs_serF_le hM hR hd hy
  have hg1 := hy.2.1
  have hg0 := hy.1
  have h2 : y.2 ^ 6 ≤ y.2 := by
    calc y.2 ^ 6 ≤ y.2 ^ 1 := pow_le_pow_of_le_one hg0.le hg1 (by norm_num)
      _ = y.2 := pow_one _
  have h3 : y.2 ≤ y.1 / d₀ := by rw [le_div_iff₀ hd]; linarith [hy.2.2.1]
  have h4 : y.1 ≤ dist y (0, 0) := by
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact (le_abs_self _).trans (le_max_left _ _)
  calc |serF R y| ≤ y.2 ^ 6 * ∑' i, M i := h1
    _ ≤ y.2 * ∑' i, M i := mul_le_mul_of_nonneg_right h2 hsn
    _ ≤ (y.1 / d₀) * ∑' i, M i := mul_le_mul_of_nonneg_right h3 hsn
    _ ≤ (dist y (0, 0) / d₀) * ∑' i, M i := by gcongr
    _ = _ := by ring

theorem lipschitzOnWith_serF_insert (hR : R.IsAdmissible d₀) {T₀ : ℝ} {M : ι → ℝ}
    (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) (hT : d₀ ≤ T₀) :
    LipschitzOnWith (Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) + Real.toNNReal ((∑' i, M i) / d₀))
      (serF R) (insert (0, 0) (cone d₀ T₀)) := by
  have hKs := lipschitzOnWith_serF hR hM hd
  have hsn : 0 ≤ ∑' i, M i := tsum_nonneg fun i => hM.nonneg hd hT i
  have hz := serF_zero hR
  set K1 := Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) with hK1
  set K2 := Real.toNNReal ((∑' i, M i) / d₀) with hK2
  have hK2' : (K2 : ℝ) = (∑' i, M i) / d₀ := Real.coe_toNNReal _ (by positivity)
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hnn : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ dist x y → a ≤ a + b := fun a b _ hb _ => by linarith
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · simp
  · rw [Real.dist_eq, hz, zero_sub, abs_neg, dist_comm]
    calc _ ≤ ((∑' i, M i) / d₀) * dist y (0, 0) := abs_serF_le_dist hR hM hd hT hy
      _ = (K2 : ℝ) * dist y (0, 0) := by rw [hK2']
      _ ≤ ((K1 + K2 : NNReal) : ℝ) * dist y (0, 0) := by
          gcongr; exact le_add_self
  · rw [Real.dist_eq, hz, sub_zero]
    calc _ ≤ ((∑' i, M i) / d₀) * dist x (0, 0) := abs_serF_le_dist hR hM hd hT hx
      _ = (K2 : ℝ) * dist x (0, 0) := by rw [hK2']
      _ ≤ ((K1 + K2 : NNReal) : ℝ) * dist x (0, 0) := by
          gcongr; exact le_add_self
  · have := hKs.dist_le_mul x hx y hy
    refine this.trans ?_
    gcongr; exact le_self_add

theorem lipschitzOnWith_Bl {C ρ ρ' : ℝ} (hρ' : 0 < ρ') (hρ'ρ : ρ' < ρ)
    (hB : ContDiffOn ℝ 1 R.B (Ioi 0))
    (hCρ : ∀ r ∈ Ioo 0 ρ, |R.B r + Real.log r| ≤ C * r ^ 2 ∧ |deriv R.B r + 1 / r| ≤ C * r) :
    LipschitzOnWith (Real.toNNReal (C * ρ')) (Bl R) (Icc 0 ρ') := by
  have hC : 0 ≤ C := by
    have := (hCρ (ρ' / 2) ⟨by positivity, by linarith⟩).1
    have h2 : 0 ≤ C * (ρ' / 2) ^ 2 := (abs_nonneg _).trans this
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [sq_nonneg (ρ' / 2), mul_pos (neg_pos.2 hneg) (by positivity : 0 < (ρ' / 2) ^ 2)]
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ ρ' → |Bl R x - Bl R y| ≤ C * ρ' * |x - y| := by
    intro x y hx hxy hy
    rcases hx.eq_or_lt with rfl | hx0
    · rcases hxy.eq_or_lt with rfl | hy0
      · simp
      · have h1 := (hCρ y ⟨hy0, by linarith⟩).1
        simp only [Bl, ite_true, hy0.ne', ite_false]
        rw [zero_sub, abs_neg, zero_sub, abs_neg, abs_of_pos hy0]
        calc _ ≤ C * y ^ 2 := h1
          _ = (C * y) * y := by ring
          _ ≤ (C * ρ') * y := by gcongr
    · have hd : ∀ r ∈ Icc x y, HasDerivWithinAt (Bl R) (deriv R.B r + 1 / r) (Icc x y) r := by
        intro r hr
        have hr0 : 0 < r := hx0.trans_le hr.1
        have h1 : HasDerivAt R.B (deriv R.B r) r :=
          ((hB.contDiffAt (isOpen_Ioi.mem_nhds hr0)).differentiableAt one_ne_zero).hasDerivAt
        have h2 := h1.add (Real.hasDerivAt_log hr0.ne')
        have h3 : HasDerivAt (Bl R) (deriv R.B r + r⁻¹) r := by
          refine h2.congr_of_eventuallyEq ?_
          filter_upwards [isOpen_Ioi.mem_nhds hr0] with t ht
          simp [Bl, ne_of_gt ht]
        simpa [one_div] using h3.hasDerivWithinAt
      have hb : ∀ r ∈ Icc x y, ‖deriv R.B r + 1 / r‖ ≤ C * ρ' := by
        intro r hr
        have hr0 : 0 < r := hx0.trans_le hr.1
        rw [Real.norm_eq_abs]
        refine ((hCρ r ⟨hr0, by linarith [hr.2]⟩).2).trans ?_
        gcongr; linarith [hr.2]
      have := (convex_Icc x y).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
        (show x ∈ Icc x y from ⟨le_rfl, hxy⟩) (show y ∈ Icc x y from ⟨hxy, le_rfl⟩)
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
      rw [abs_sub_comm, abs_sub_comm x y]; exact this
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  rcases le_total x y with h | h
  · exact key x y hx.1 h hy.2
  · rw [abs_sub_comm, abs_sub_comm x y]; exact key y x hy.1 h hx.2

/-- `H₁ = H + log ‖· - p‖` extended by `0` at the site. -/
@[expose] noncomputable def H1 (R : RadialData ι) (P : Set ℂ) (p z : ℂ) : ℝ :=
  Bl R ‖z - p‖ + serF R (‖z - p‖, gauge P p (z - p))

theorem H1_eq_cellH_add_log (hz : z ≠ p) : H1 R P p z = cellH R P p z + Real.log ‖z - p‖ := by
  have : ‖z - p‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
  unfold H1 cellH Fpair Bl
  rw [ite_eq_right this]; ring

theorem H1_self (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) (hp : p ∈ P) : H1 R P p p = 0 := by
  unfold H1 Bl
  simp [gauge_zero hS hp, serF_zero hR]

theorem ball_subset_voronoiCell (hS : SepSites P d₀) (hp : p ∈ P) :
    ball p d₀ ⊆ voronoiCell P p := by
  intro z hz q hq
  by_cases hqp : q = p
  · rw [hqp]
  · have h1 := hS.sep p hp q hq (Ne.symm hqp)
    have h2 := mem_ball_iff_norm.1 hz
    have h3 : ‖p - q‖ ≤ ‖p - z‖ + ‖z - q‖ := norm_sub_le_norm_sub_add_norm_sub p z q
    rw [norm_sub_rev p z] at h3
    linarith

/-- **`H + log r` is Lipschitz across the site**, uniformly in the site. -/
theorem exists_lipschitzOnWith_H1 (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) :
    ∃ (K : NNReal) (ρ₁ : ℝ), 0 < ρ₁ ∧ ρ₁ ≤ d₀ ∧ ∀ p ∈ P, LipschitzOnWith K (H1 R P p) (ball p ρ₁) := by
  obtain ⟨R₁, T₀, M, hR₁, hT, hdT', hM⟩ := exists_bnd hR hS
  have hd := hS.pos
  have hdT : d₀ ≤ T₀ := hdT'.le
  obtain ⟨C, ρ, hρ, hCρ⟩ := hR.origin
  have hBl := lipschitzOnWith_Bl (R := R) (ρ' := ρ / 2) (by positivity) (by linarith) hR.contDiffOn_B hCρ
  have hser := lipschitzOnWith_serF_insert hR hM hd hdT
  refine ⟨Real.toNNReal (C * (ρ / 2)) + (Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) +
      Real.toNNReal ((∑' i, M i) / d₀)) * max 1 (Real.toNNReal (1 / d₀)), min d₀ (ρ / 2),
    lt_min hd (by positivity), min_le_left _ _, fun p hp => ?_⟩
  have hball : ball p (min d₀ (ρ / 2)) ⊆ ball p d₀ := ball_subset_ball (min_le_left _ _)
  have h1 : LipschitzOnWith (Real.toNNReal (C * (ρ / 2)))
      (fun z : ℂ => Bl R ‖z - p‖) (ball p (min d₀ (ρ / 2))) := by
    have := hBl.comp (lipschitzWith_norm_sub p).lipschitzOnWith (s := ball p (min d₀ (ρ / 2)))
      (fun z hz => by
        refine ⟨norm_nonneg _, ?_⟩
        have := mem_ball_iff_norm.1 hz
        exact (this.le.trans (min_le_right _ _)))
    rw [mul_one] at this
    exact this
  have h2 : LipschitzOnWith ((Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) +
      Real.toNNReal ((∑' i, M i) / d₀)) * max 1 (Real.toNNReal (1 / d₀)))
      (fun z : ℂ => serF R (‖z - p‖, gauge P p (z - p))) (ball p (min d₀ (ρ / 2))) := by
    have hmap : LipschitzWith (max 1 (Real.toNNReal (1 / d₀)))
        (fun z : ℂ => (‖z - p‖, gauge P p (z - p))) :=
      (lipschitzWith_norm_sub p).prodMk (lipschitzWith_gauge_sub hS hp)
    refine hser.comp hmap.lipschitzOnWith (s := ball p (min d₀ (ρ / 2))) fun z hz => ?_
    by_cases hzp : z = p
    · subst hzp; simp [gauge_zero hS hp]
    · exact Or.inr (mem_cone_of_mem_cell hS hp hR₁ hT (ball_subset_voronoiCell hS hp (hball hz)) hzp)
  exact h1.add h2

end Dual

end SandierSerfaty

end
