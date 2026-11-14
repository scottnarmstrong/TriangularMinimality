/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Prim

/-!
# From local Hessian positivity to `K ≤ 2g` on `𝒟₀` (paper `comp:hessian`, theorem T4, real analysis)

The primitive `g(d, x) = g_d(x)` has the exact partial derivatives `∂ₓ g = G` and `∂_d g = gd = ∫₀ˣ G_d(d, s) ds`
(`Box.hasDerivAt_g_d_gen`), but its second derivative in `d` jumps at the spline knots. This module therefore avoids
second derivatives and works with the *directional quantity* `theta u v (d, x) = u·gd d x + v·G d x`
(`= d/dτ g((d, x) + τ(u, v))`) and its finite increments.

* `LocalHess S`: the local form of the Hessian assertion on a convex set `S`: for a point `q ∈ S` and a direction
  `(u, v)` that keeps the forward ray in `S` for a short time, `theta u v` does not decrease along the ray for a short
  time. The certificate proves it from the interval Hessian tests (`Box.HessSound`).
* `g_step`: the one-step Taylor inequality, from the derivative bounds only (`DerivBounds`):
  `g(q + δw) - g(q) ≥ δ·theta(q) - C δ²`.
* `inner_of_localHess`: on a convex `S ⊆ 𝒟`, if `q₀ ∈ S` is stationary (`gd q₀ = 0`, `G q₀ = 0`) and `LocalHess S`
  holds, then `g q₀ ≤ g q` on `S`. (Real induction gives `theta ≥ 0` along the segment from `q₀`; a telescoping sum of
  `g_step` gives the conclusion.)
-/

open Set Filter Topology

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Calibration

variable {dLo dHi xHi L1 L2 L3 L4 : ℝ}

/-- `d/dτ g((d, x) + τ(u, v)) = u gd + v G`. -/
@[expose] noncomputable def theta (u v d x : ℝ) : ℝ := u * gd d x + v * G d x

/-- **The local Hessian hypothesis** on `S`. -/
@[expose] def LocalHess (S : Set (ℝ × ℝ)) : Prop :=
  ∀ d x u v : ℝ, (d, x) ∈ S → (∃ ε > 0, ∀ h ∈ Icc (0 : ℝ) ε, (d + h * u, x + h * v) ∈ S) →
    ∃ ε > 0, ∀ h ∈ Icc (0 : ℝ) ε, theta u v d x ≤ theta u v (d + h * u) (x + h * v)

/-- `x ↦ ∫₀ˣ G_d(d, s) ds` is `L₁`-Lipschitz on `[0, xHi]`. -/
theorem DerivBounds.gd_lip_xx (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d : ℝ} (hd : d ∈ Icc dLo dHi) :
    ∀ x ∈ Icc 0 xHi, ∀ x' ∈ Icc 0 xHi, |gd d x' - gd d x| ≤ L1 * |x' - x| := by
  intro x hx x' hx'
  have hd0 : 0 < d := lt_of_lt_of_le hB.pos hd.1
  have hint := continuous_Gd_of hd0
  unfold gd
  rw [intervalIntegral.integral_interval_sub_left (hint.intervalIntegrable 0 x') (hint.intervalIntegrable 0 x)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x') (C := L1) (f := fun s => Gd d s)
    (fun s hs => by
      have hs' : s ∈ Icc 0 xHi := Set.uIcc_subset_Icc hx hx' (Set.uIoc_subset_uIcc hs)
      rw [Real.norm_eq_abs]
      exact hB.gd_le d hd s hs')
  simpa [Real.norm_eq_abs] using this

theorem continuousOn_of_abs_le {f : ℝ → ℝ} {T : Set ℝ} {C : ℝ} (h : ∀ a ∈ T, ∀ b ∈ T, |f a - f b| ≤ C * |a - b|) :
    ContinuousOn f T := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have hC : 0 < |C| + 1 := by positivity
  refine ⟨ε / (|C| + 1), by positivity, fun a ha hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  have h1 := h a ha b hb
  have h2 : C * |a - b| ≤ |C| * |a - b| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
  have h3 : |a - b| * (|C| + 1) < ε := by
    rwa [lt_div_iff₀ hC] at hab
  nlinarith [abs_nonneg (a - b), abs_nonneg C]

/-- The Lipschitz estimate of `theta` along a segment inside the box. -/
theorem theta_seg_lip (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d0 x0 u v : ℝ} {T : Set ℝ}
    (hT : ∀ τ ∈ T, d0 + τ * u ∈ Icc dLo dHi ∧ x0 + τ * v ∈ Icc 0 xHi) :
    ∀ a ∈ T, ∀ b ∈ T, |theta u v (d0 + a * u) (x0 + a * v) - theta u v (d0 + b * u) (x0 + b * v)| ≤
      (|u| * (L1 * |v| + xHi * L3 * |u|) + |v| * (L1 * |u| + L2 * |v|)) * |a - b| := by
  intro a ha b hb
  obtain ⟨ha1, ha2⟩ := hT a ha
  obtain ⟨hb1, hb2⟩ := hT b hb
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hB.nonneg
  set d1 := d0 + a * u
  set d2 := d0 + b * u
  set x1 := x0 + a * v
  set x2 := x0 + b * v
  have hdd : |d1 - d2| = |u| * |a - b| := by
    have : d1 - d2 = u * (a - b) := by simp only [d1, d2]; ring
    rw [this, abs_mul]
  have hxx : |x1 - x2| = |v| * |a - b| := by
    have : x1 - x2 = v * (a - b) := by simp only [x1, x2]; ring
    rw [this, abs_mul]
  have e1 : |gd d1 x1 - gd d2 x2| ≤ L1 * |x1 - x2| + xHi * L3 * |d1 - d2| := by
    have h1 := hB.gd_lip_x ha2 d1 ha1 d2 hb1
    have h2 := hB.gd_lip_xx hb1 x2 hb2 x1 ha2
    have h3 : x1 * L3 * |d1 - d2| ≤ xHi * L3 * |d1 - d2| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha2.2 hL3) (abs_nonneg _)
    calc |gd d1 x1 - gd d2 x2| = |(gd d1 x1 - gd d2 x1) + (gd d2 x1 - gd d2 x2)| := by ring_nf
      _ ≤ |gd d1 x1 - gd d2 x1| + |gd d2 x1 - gd d2 x2| := abs_add_le _ _
      _ ≤ _ := by linarith
  have e2 : |G d1 x1 - G d2 x2| ≤ L2 * |x1 - x2| + L1 * |d1 - d2| := by
    have h1 := hB.G_lip_s ha1 x1 ha2 x2 hb2
    have h2 := hB.G_lip_d hb2 d1 ha1 d2 hb1
    calc |G d1 x1 - G d2 x2| = |(G d1 x1 - G d1 x2) + (G d1 x2 - G d2 x2)| := by ring_nf
      _ ≤ |G d1 x1 - G d1 x2| + |G d1 x2 - G d2 x2| := abs_add_le _ _
      _ ≤ _ := by linarith
  have : theta u v d1 x1 - theta u v d2 x2 = u * (gd d1 x1 - gd d2 x2) + v * (G d1 x1 - G d2 x2) := by
    simp only [theta]; ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  rw [hdd, hxx] at e1 e2
  have := mul_le_mul_of_nonneg_left e1 (abs_nonneg u)
  have := mul_le_mul_of_nonneg_left e2 (abs_nonneg v)
  nlinarith [abs_nonneg u, abs_nonneg v, abs_nonneg (a - b)]

/-- **One step of the primitive** (Taylor in each variable successively, derivative bounds only):
`g(d', x') - g(d, x) ≥ (d' - d) gd d x + (x' - x) G d x - E` with
`E = L₂(x'-x)²/2 + L₁|d'-d||x'-x| + xHi L₃ (d'-d)²/2`. -/
theorem g_step (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d d' x x' : ℝ} (hd : d ∈ Icc dLo dHi)
    (hd' : d' ∈ Icc dLo dHi) (hx : x ∈ Icc 0 xHi) (hx' : x' ∈ Icc 0 xHi) :
    (d' - d) * gd d x + (x' - x) * G d x -
        (L2 * (x' - x) ^ 2 / 2 + L1 * |d' - d| * |x' - x| + xHi * L3 * (d' - d) ^ 2 / 2) ≤
      g d' x' - g d x := by
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hB.nonneg
  have hd0' : 0 < d' := lt_of_lt_of_le hB.pos hd'.1
  have hdd0 : ∀ u ∈ Icc dLo dHi, 0 < u := fun u hu => lt_of_lt_of_le hB.pos hu.1
  -- Taylor in `x` at `d'`
  have t1 := taylor_lip (ψ := g d') (ψ' := G d') (a := 0) (b := xHi) (M := L2)
    (fun y _ => hasDerivAt_g hd0' y) (fun y hy y' hy' => hB.G_lip_s hd' y hy y' hy') hx hx'
  -- Taylor in `d` at `x`
  have t2 := taylor_lip (ψ := fun u => g u x) (ψ' := fun u => gd u x) (a := dLo) (b := dHi) (M := xHi * L3)
    (fun u hu => hasDerivAt_g_d_gen (hdd0 u hu) hx.1)
    (fun u hu u' hu' => by
      have := hB.gd_lip_x hx u hu u' hu'
      calc _ ≤ x * L3 * |u - u'| := this
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx.2 hL3) (abs_nonneg _)) hd hd'
  have t3 := hB.G_lip_d hx d' hd' d hd
  have a1 := (abs_le.1 t1).1
  have a2 := (abs_le.1 t2).1
  have a3 := (abs_le.1 t3).2
  have h4 : (x' - x) * (G d' x - G d x) ≥ -(L1 * |d' - d| * |x' - x|) := by
    have : |(x' - x) * (G d' x - G d x)| ≤ |x' - x| * (L1 * |d' - d|) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left t3 (abs_nonneg _)
    have h5 := (abs_le.1 this).1
    nlinarith
  nlinarith


/-- A convex `S` contains the point `q₀ + τ(q - q₀)`, written in coordinates. -/
theorem seg_mem {S : Set (ℝ × ℝ)} (hSc : Convex ℝ S) {d0 x0 d1 x1 : ℝ} (h0 : (d0, x0) ∈ S) (h1 : (d1, x1) ∈ S)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : (d0 + τ * (d1 - d0), x0 + τ * (x1 - x0)) ∈ S := by
  have := hSc h0 h1 (sub_nonneg.2 hτ.2) hτ.1 (by ring)
  convert this using 1
  ext <;> simp <;> ring

/-- **`theta ≥ 0` along the segment from a stationary point** (real induction from the local hypothesis). -/
theorem theta_nonneg_seg (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {S : Set (ℝ × ℝ)}
    (hS : S ⊆ Icc dLo dHi ×ˢ Icc 0 xHi) (hSc : Convex ℝ S) (hloc : LocalHess S) {d0 x0 d1 x1 : ℝ}
    (h0 : (d0, x0) ∈ S) (h1 : (d1, x1) ∈ S) (hgd : gd d0 x0 = 0) (hG : G d0 x0 = 0) :
    ∀ τ ∈ Icc (0 : ℝ) 1, 0 ≤ theta (d1 - d0) (x1 - x0) (d0 + τ * (d1 - d0)) (x0 + τ * (x1 - x0)) := by
  set u := d1 - d0 with hu
  set v := x1 - x0 with hv
  set Θ : ℝ → ℝ := fun τ => theta u v (d0 + τ * u) (x0 + τ * v) with hΘ
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, (d0 + τ * u, x0 + τ * v) ∈ S := fun τ hτ => seg_mem hSc h0 h1 hτ
  have hcont : ContinuousOn Θ (Icc 0 1) :=
    continuousOn_of_abs_le (theta_seg_lip hB (T := Icc 0 1) (d0 := d0) (x0 := x0) (u := u) (v := v)
      (fun τ hτ => by have := hS (hseg τ hτ); exact ⟨this.1, this.2⟩))
  have hclosed : IsClosed ({τ | 0 ≤ Θ τ} ∩ Icc 0 1) := by
    have := hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
    convert this using 1
    ext τ; simp [and_comm]
  have ha : (0 : ℝ) ∈ {τ | 0 ≤ Θ τ} := by
    simp [hΘ, theta, hgd, hG]
  have key := hclosed.Icc_subset_of_forall_exists_gt ha (fun τ hτ y hy => by
    obtain ⟨hτ0, hτl, hτh⟩ := hτ
    have hm := hseg τ ⟨hτl, hτh.le⟩
    obtain ⟨ε, hε, hε'⟩ := hloc (d0 + τ * u) (x0 + τ * v) u v hm
      ⟨1 - τ, by linarith [hτh], fun h hh => by
        have := hseg (τ + h) ⟨by linarith [hτl, hh.1], by linarith [hh.2]⟩
        convert this using 2 <;> ring⟩
    set h0' := min ε (y - τ) with hh0
    have hpos : 0 < h0' := lt_min hε (by linarith [hy.out])
    have hle1 : h0' ≤ ε := min_le_left _ _
    have hle2 : h0' ≤ y - τ := min_le_right _ _
    refine ⟨τ + h0', ?_, by linarith, by linarith⟩
    have := hε' h0' ⟨hpos.le, hle1⟩
    show 0 ≤ Θ (τ + h0')
    have e1 : d0 + τ * u + h0' * u = d0 + (τ + h0') * u := by ring
    have e2 : x0 + τ * v + h0' * v = x0 + (τ + h0') * v := by ring
    rw [e1, e2] at this
    exact le_trans hτ0 this)
  exact fun τ hτ => key hτ

/-- **The inner assertion from the local Hessian hypothesis** (`comp:inner-conclusion`): `g q₀ ≤ g q` on `S`. -/
theorem inner_of_localHess (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {S : Set (ℝ × ℝ)}
    (hS : S ⊆ Icc dLo dHi ×ˢ Icc 0 xHi) (hSc : Convex ℝ S) (hloc : LocalHess S) {d0 x0 d1 x1 : ℝ}
    (h0 : (d0, x0) ∈ S) (h1 : (d1, x1) ∈ S) (hgd : gd d0 x0 = 0) (hG : G d0 x0 = 0) :
    g d0 x0 ≤ g d1 x1 := by
  set u := d1 - d0 with hu
  set v := x1 - x0 with hv
  have hth := theta_nonneg_seg hB hS hSc hloc h0 h1 hgd hG
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hB.nonneg
  set C : ℝ := L2 * v ^ 2 / 2 + L1 * |u| * |v| + xHi * L3 * u ^ 2 / 2 with hC
  have hbox : ∀ τ ∈ Icc (0 : ℝ) 1, d0 + τ * u ∈ Icc dLo dHi ∧ x0 + τ * v ∈ Icc 0 xHi := fun τ hτ => by
    have := hS (seg_mem hSc h0 h1 hτ)
    exact ⟨this.1, this.2⟩
  have hN : ∀ N : ℕ, 0 < N → -(C / N) ≤ g d1 x1 - g d0 x0 := by
    intro N hNpos
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    set ψ : ℕ → ℝ := fun k => g (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v) with hψ
    have hτ : ∀ k, k ≤ N → ((k : ℝ) / N) ∈ Icc (0 : ℝ) 1 := fun k hk =>
      ⟨by positivity, by rw [div_le_one hNr]; exact_mod_cast hk⟩
    have step : ∀ k ∈ Finset.range N, -(C / (N : ℝ) ^ 2) ≤ ψ (k + 1) - ψ k := by
      intro k hk
      have hk' : k < N := Finset.mem_range.1 hk
      obtain ⟨b1, b2⟩ := hbox _ (hτ k hk'.le)
      obtain ⟨b3, b4⟩ := hbox _ (hτ (k + 1) hk')
      have hs := g_step hB b1 b3 b2 b4
      have hd' : (d0 + (((k + 1 : ℕ) : ℝ) / N) * u) - (d0 + ((k : ℝ) / N) * u) = u / N := by
        push_cast; field_simp; ring
      have hx' : (x0 + (((k + 1 : ℕ) : ℝ) / N) * v) - (x0 + ((k : ℝ) / N) * v) = v / N := by
        push_cast; field_simp; ring
      rw [hd', hx'] at hs
      have ht := hth ((k : ℝ) / N) (hτ k hk'.le)
      simp only [theta] at ht
      have e1 : (u / N) * gd (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v) +
          (v / N) * G (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v) =
          (1 / N) * (u * gd (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v) +
          v * G (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v)) := by ring
      have e2 : L2 * (v / N) ^ 2 / 2 + L1 * |u / N| * |v / N| + xHi * L3 * (u / N) ^ 2 / 2 = C / (N : ℝ) ^ 2 := by
        rw [abs_div, abs_div, abs_of_pos hNr, hC]
        field_simp
      have e3 : 0 ≤ (1 / (N : ℝ)) * (u * gd (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v) +
          v * G (d0 + ((k : ℝ) / N) * u) (x0 + ((k : ℝ) / N) * v)) := mul_nonneg (by positivity) ht
      simp only [hψ]
      linarith
    have hsum := Finset.sum_le_sum step
    rw [Finset.sum_range_sub ψ N] at hsum
    have hψN : ψ N = g d1 x1 := by
      simp only [hψ, div_self hNr.ne', one_mul, hu, hv]
      congr 1 <;> ring
    have hψ0 : ψ 0 = g d0 x0 := by simp [hψ]
    rw [hψN, hψ0] at hsum
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have : (N : ℝ) * -(C / (N : ℝ) ^ 2) = -(C / N) := by field_simp
    linarith
  by_contra hcon
  push Not at hcon
  have hδ : 0 < g d0 x0 - g d1 x1 := by linarith
  obtain ⟨N, hN'⟩ := exists_nat_gt (C / (g d0 x0 - g d1 x1))
  have hNpos : 0 < N := by
    have hxH : 0 ≤ xHi := (hS h0).2.1.trans (hS h0).2.2
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    have : (0 : ℝ) ≤ C / (g d0 x0 - g d1 x1) := div_nonneg hC0 hδ.le
    exact_mod_cast lt_of_le_of_lt this hN'
  have h1 := hN N hNpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [div_lt_iff₀ hδ] at hN'
  have : C / N < g d0 x0 - g d1 x1 := by rw [div_lt_iff₀ hNr]; linarith
  linarith

end SandierSerfaty.Certificate.Box
