/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Interp
public import SandierSerfaty.Calibration.Stationarity
public import SandierSerfaty.Calibration.SectorPrimitive

/-!
# The primitive `g_d(x)` on the box: derivative bounds and one cell (paper `comp:outer-errors`)

`DerivBounds` packages the finite derivative assertion A7 of the certificate
(paper `comp:global-derivative-bounds`) in the form the interpolation and midpoint
arguments consume: `|G_d| ≤ L₁`, `|G_s| ≤ L₂` and the Lipschitz constants `L₃` of `G_d` in `d`, `L₄` of `G_s` in
`s` (the global bounds on `G_dd`, `G_ss`; only Lipschitz-ness is used, so the one-sided second derivatives at
the spline knots, where `e''` jumps, cause no trouble) on a box `[dLo, dHi] × [0, xHi]`.

* `hasDerivAt_g_d`: `∂_d g_d(x) = ∫₀ˣ G_d(d, s) ds` for every `d > 0`, `x ≥ 0` (differentiation under the
  integral sign; the case `(d, x) = (p, x₀)` is `Calibration.hasDerivAt_g_d`);
* `cell_lower`: on a grid cell `[d₁, d₂] × [x₁, x₂]`, `2g ≥ c - E_x - E_d` if `2g ≥ c` at the four corners
  (the successive 1-D interpolation of `comp:outer-errors`; `E_x = 2L₂(x₂-x₁)²/8`, `E_d = 2 xHi L₃ (d₂-d₁)²/8`).
-/

open Set MeasureTheory Filter Topology

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Calibration

/-- The finite derivative assertion A7 on the box `[dLo, dHi] × [0, xHi]`. -/
structure DerivBounds (dLo dHi xHi L1 L2 L3 L4 : ℝ) : Prop where
  /-- The box lies in `d > 0`. -/
  pos : 0 < dLo
  /-- Nonnegativity of the constants. -/
  nonneg : 0 ≤ L1 ∧ 0 ≤ L2 ∧ 0 ≤ L3 ∧ 0 ≤ L4
  /-- `|G_d| ≤ L₁`. -/
  gd_le : ∀ d ∈ Icc dLo dHi, ∀ s ∈ Icc 0 xHi, |Gd d s| ≤ L1
  /-- `|G_s| ≤ L₂`. -/
  gs_le : ∀ d ∈ Icc dLo dHi, ∀ s ∈ Icc 0 xHi, |Gs d s| ≤ L2
  /-- `G_d` is `L₃`-Lipschitz in `d`. -/
  gd_lip : ∀ s ∈ Icc 0 xHi, ∀ d ∈ Icc dLo dHi, ∀ d' ∈ Icc dLo dHi, |Gd d s - Gd d' s| ≤ L3 * |d - d'|
  /-- `G_s` is `L₄`-Lipschitz in `s`. -/
  gs_lip : ∀ d ∈ Icc dLo dHi, ∀ s ∈ Icc 0 xHi, ∀ s' ∈ Icc 0 xHi, |Gs d s - Gs d s'| ≤ L4 * |s - s'|

variable {dLo dHi xHi L1 L2 L3 L4 : ℝ}

theorem continuous_Gd_of {d : ℝ} (hd : 0 < d) : Continuous (Gd d) := by
  have h := continuousOn_Gd.comp_continuous (g := fun q : ℝ × ℝ => Gd q.1 q.2) (f := fun s : ℝ => (d, s))
    (Continuous.prodMk continuous_const continuous_id)
    (fun s => (⟨hd, mem_univ s⟩ : (d, s) ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ))))
  simpa [Function.comp_def] using h

theorem continuousOn_Gs : ContinuousOn (fun q : ℝ × ℝ => Gs q.1 q.2) (Ioi 0 ×ˢ univ) := by
  have hT : Continuous fun q : ℝ × ℝ => tt q.1 q.2 := by unfold tt; fun_prop
  have hTpos : MapsTo (fun q : ℝ × ℝ => tt q.1 q.2) (Ioi 0 ×ˢ univ) (Ioi 0) :=
    fun q hq => tt_pos hq.1
  have h1 := continuousOn_f.comp hT.continuousOn hTpos
  have h2 := continuousOn_df.comp hT.continuousOn hTpos
  have h3 := continuousOn_e.comp hT.continuousOn hTpos
  have h4 := continuousOn_deriv_e.comp hT.continuousOn hTpos
  have hne : ∀ q ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), tt q.1 q.2 ≠ 0 := fun q hq => (tt_pos hq.1).ne'
  have hd : ∀ q ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), q.1 ≠ 0 := fun q hq => hq.1.ne'
  have A := hT.continuousOn (s := (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)))
  have B : ContinuousOn (fun q : ℝ × ℝ => q.1) (Ioi 0 ×ˢ univ) := continuousOn_fst
  have C : ContinuousOn (fun q : ℝ × ℝ => q.2) (Ioi 0 ×ˢ univ) := continuousOn_snd
  have t1 := ((B.mul C).mul h2).div (A.pow 3) fun q hq => pow_ne_zero 3 (hne q hq)
  have t2 := (((continuousOn_const (c := (2 : ℝ))).mul B).mul C |>.mul h1).div (A.pow 4)
    fun q hq => pow_ne_zero 4 (hne q hq)
  have t3 := (((continuousOn_const (c := (2 : ℝ))).mul C).mul h3).div (A.pow 2)
    fun q hq => pow_ne_zero 2 (hne q hq)
  have t4 := ((C.pow 3).mul h4).div (A.pow 3) fun q hq => pow_ne_zero 3 (hne q hq)
  have t5 := (((continuousOn_const (c := (2 : ℝ))).mul (C.pow 3)).mul h3).div (A.pow 4)
    fun q hq => pow_ne_zero 4 (hne q hq)
  exact (t1.sub t2).sub (((t3.add t4).sub t5).div B hd)

theorem continuous_Gs_of {d : ℝ} (hd : 0 < d) : Continuous (Gs d) := by
  have h := continuousOn_Gs.comp_continuous (g := fun q : ℝ × ℝ => Gs q.1 q.2) (f := fun s : ℝ => (d, s))
    (Continuous.prodMk continuous_const continuous_id)
    (fun s => (⟨hd, mem_univ s⟩ : (d, s) ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ))))
  simpa [Function.comp_def] using h

/-- `G(d, ·)` is `L₂`-Lipschitz on `[0, xHi]`. -/
theorem DerivBounds.G_lip_s (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d : ℝ} (hd : d ∈ Icc dLo dHi) :
    ∀ s ∈ Icc 0 xHi, ∀ s' ∈ Icc 0 xHi, |G d s - G d s'| ≤ L2 * |s - s'| := by
  intro s hs s' hs'
  have hd0 : 0 < d := lt_of_lt_of_le hB.pos hd.1
  have := (convex_Icc 0 xHi).norm_image_sub_le_of_norm_hasDerivWithin_le (f := G d) (f' := Gs d) (C := L2)
    (fun x _ => (hasDerivAt_G_s hd0 x).hasDerivWithinAt) (fun x hx => by simpa using hB.gs_le d hd x hx) hs' hs
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- `G(·, s)` is `L₁`-Lipschitz on `[dLo, dHi]`. -/
theorem DerivBounds.G_lip_d (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {s : ℝ} (hs : s ∈ Icc 0 xHi) :
    ∀ d ∈ Icc dLo dHi, ∀ d' ∈ Icc dLo dHi, |G d s - G d' s| ≤ L1 * |d - d'| := by
  intro d hd d' hd'
  have := (convex_Icc dLo dHi).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun d => G d s) (f' := fun d => Gd d s)
    (C := L1)
    (fun x hx => (hasDerivAt_G_d (lt_of_lt_of_le hB.pos hx.1) s).hasDerivWithinAt)
    (fun x hx => by simpa using hB.gd_le x hx s hs) hd' hd
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-! ### Differentiation of the primitive in `d` -/

/-- The `d`-derivative of the primitive, `∫₀ˣ G_d(d, s) ds`. -/
@[expose] noncomputable def gd (d x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, Gd d s

theorem hasDerivAt_g_d_gen {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun u => g u x) (gd d x) d := by
  set S : Set (ℝ × ℝ) := Icc (d / 2) (2 * d) ×ˢ Icc 0 x with hSdef
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSU : S ⊆ Ioi 0 ×ˢ univ := fun q hq => ⟨lt_of_lt_of_le (by positivity) hq.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn (continuousOn_Gd.mono hSU)
  have hnhds : Ioo (d / 2) (2 * d) ∈ 𝓝 d := Ioo_mem_nhds (by linarith) (by linarith)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun d s => G d s)
    (F' := Gd) (bound := fun _ => M) hnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [Ioi_mem_nhds hd] with d' hd'
    exact (continuous_G hd').aestronglyMeasurable
  · exact (continuous_G hd).intervalIntegrable 0 x
  · exact (continuous_Gd_of hd).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s hs u hu => ?_
    rw [Set.uIoc_of_le hx] at hs
    exact hM (u, s) ⟨⟨hu.1.le, hu.2.le⟩, ⟨hs.1.le, hs.2⟩⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun s _ u hu =>
      hasDerivAt_G_d (lt_trans (by linarith [hu.1]) hu.1) s

/-- `u ↦ ∫₀ˣ G_d(u, s) ds` is `x L₃`-Lipschitz on `[dLo, dHi]`. -/
theorem DerivBounds.gd_lip_x (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {x : ℝ} (hx : x ∈ Icc 0 xHi) :
    ∀ u ∈ Icc dLo dHi, ∀ u' ∈ Icc dLo dHi, |gd u x - gd u' x| ≤ x * L3 * |u - u'| := by
  intro u hu u' hu'
  have hu0 : 0 < u := lt_of_lt_of_le hB.pos hu.1
  have hu0' : 0 < u' := lt_of_lt_of_le hB.pos hu'.1
  unfold gd
  rw [← intervalIntegral.integral_sub ((continuous_Gd_of hu0).intervalIntegrable 0 x)
    ((continuous_Gd_of hu0').intervalIntegrable 0 x)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := L3 * |u - u'|)
    (f := fun s => Gd u s - Gd u' s) (fun s hs => by
      rw [Set.uIoc_of_le hx.1] at hs
      rw [Real.norm_eq_abs]
      exact hB.gd_lip s ⟨hs.1.le, hs.2.trans hx.2⟩ u hu u' hu')
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx.1] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **One grid cell** (`comp:outer-errors`): if `2g ≥ c` at the four corners of `[d₁, d₂] × [x₁, x₂]`, then
`2g ≥ c - E_x - E_d` on the cell, `E_x = 2L₂(x₂-x₁)²/8`, `E_d = 2 xHi L₃ (d₂-d₁)²/8` (the 1-D interpolation
error in each variable successively; no mixed derivative). -/
theorem DerivBounds.cell_lower (hB : DerivBounds dLo dHi xHi L1 L2 L3 L4) {d₁ d₂ x₁ x₂ c : ℝ} (hd₁ : dLo ≤ d₁)
    (hd₂ : d₂ ≤ dHi) (hx₁ : 0 ≤ x₁) (hx₂ : x₂ ≤ xHi) (h11 : c ≤ 2 * g d₁ x₁) (h12 : c ≤ 2 * g d₁ x₂)
    (h21 : c ≤ 2 * g d₂ x₁) (h22 : c ≤ 2 * g d₂ x₂) {d x : ℝ} (hd : d ∈ Icc d₁ d₂) (hx : x ∈ Icc x₁ x₂) :
    c - 2 * L2 * (x₂ - x₁) ^ 2 / 8 - 2 * xHi * L3 * (d₂ - d₁) ^ 2 / 8 ≤ 2 * g d x := by
  have hx0 : 0 ≤ x := hx₁.trans hx.1
  have hxH : x ≤ xHi := hx.2.trans hx₂
  have hdI : ∀ d' ∈ Icc d₁ d₂, d' ∈ Icc dLo dHi := fun d' h => ⟨hd₁.trans h.1, h.2.trans hd₂⟩
  have hxI : ∀ y ∈ Icc x₁ x₂, y ∈ Icc 0 xHi := fun y h => ⟨hx₁.trans h.1, h.2.trans hx₂⟩
  -- interpolation in `x` at the two values of `d`
  have step1 : ∀ d' ∈ Icc d₁ d₂, c ≤ 2 * g d' x₁ → c ≤ 2 * g d' x₂ →
      c - 2 * L2 * (x₂ - x₁) ^ 2 / 8 ≤ 2 * g d' x := by
    intro d' hd' ha hb
    have hd0 : 0 < d' := lt_of_lt_of_le hB.pos (hdI d' hd').1
    have := interp_ge (ψ := fun y => 2 * g d' y) (ψ' := fun y => 2 * G d' y) (a := x₁) (b := x₂) (M := 2 * L2)
      (fun y _ => (hasDerivAt_g hd0 y).const_mul 2)
      (fun y hy y' hy' => by
        have := hB.G_lip_s (hdI d' hd') y (hxI y hy) y' (hxI y' hy')
        calc _ = 2 * |G d' y - G d' y'| := by rw [← mul_sub, abs_mul]; norm_num
          _ ≤ _ := by linarith) hx
    have hmin : c ≤ min (2 * g d' x₁) (2 * g d' x₂) := le_min ha hb
    linarith
  have s1 := step1 d₁ ⟨le_rfl, (hd.1.trans hd.2)⟩ h11 h12
  have s2 := step1 d₂ ⟨(hd.1.trans hd.2), le_rfl⟩ h21 h22
  -- interpolation in `d` at fixed `x`
  have := interp_ge (ψ := fun u => 2 * g u x) (ψ' := fun u => 2 * gd u x) (a := d₁) (b := d₂)
    (M := 2 * xHi * L3)
    (fun u hu => (hasDerivAt_g_d_gen (lt_of_lt_of_le hB.pos (hdI u hu).1) hx0).const_mul 2)
    (fun u hu u' hu' => by
      have := hB.gd_lip_x ⟨hx0, hxH⟩ u (hdI u hu) u' (hdI u' hu')
      calc _ = 2 * |gd u x - gd u' x| := by rw [← mul_sub, abs_mul]; norm_num
        _ ≤ 2 * (x * L3 * |u - u'|) := by linarith
        _ ≤ _ := by
          have : x * L3 ≤ xHi * L3 := mul_le_mul_of_nonneg_right hxH hB.nonneg.2.2.1
          nlinarith [abs_nonneg (u - u')]) hd
  have hmin : c - 2 * L2 * (x₂ - x₁) ^ 2 / 8 ≤ min (2 * g d₁ x) (2 * g d₂ x) := le_min s1 s2
  linarith

end SandierSerfaty.Certificate.Box
