/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Lambda.LoopSound

/-!
# Soundness of the fine enclosure of `λ`

`lamFine_sound`: if the fine table is realized (`FRealized`: the box realization `Box.TableRealized` and the node
tuples), the basis constants are valid, the finite-core premise holds and `rad ≥ 10⁻¹¹·2^128`, then
`lamFine F d P = some I` gives `Calibration.lam ∈ I`.

Assembly: `Calibration.lam_mul_x₀` (`λ x₀ = (f₀(R₀) - f₀(p))/x₀ - x₀ e(R₀)/p² + ∫₀^{x₀} q + (1/p²) ∫₀^{x₀} e(t)`,
the multiplied-out form of `cal:constants`), the split `∫₀^{x₀} q = ∫₀^{s₀} q + ∫_{s₀}^{x₀} q`,
`Calibration.lambda_origin` for `∫₀^{s₀} q` and `qSum_sound`, `eSum_sound` for the other two integrals.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The data produced by a successful evaluation. -/
theorem lamFine_some {F : FTable} {d : BasisData} {P : LamPar} {I : IV 128} (h : lamFine F d P = some I) :
    ∃ (l hh : ℕ) (cB cY : Tup) (FP FP1 FR ER IQ IE : IV 128),
      IV.sqrtCheck (IV.add d.p2 (IV.sq (s0Of P))) l hh = true ∧
      lookup F.T (IV.hull d.p d.r0) = some cB ∧ lookup F.T (IV.hull d.p (IV.ofNatPair l hh)) = some cY ∧
      fPt F P.rad d.p = some FP ∧ f1Pt F P.rad d.p = some FP1 ∧ fPt F P.rad d.r0 = some FR ∧
      ePt F P.rad d.r0 = some ER ∧ qSum F (qCtxOf d P.Nq P.rad (s0Of P) cB FP) = some IQ ∧
      eSum F (eCtxOf d P.Ne P.rad cB) = some IE ∧ 0 < P.s0d ∧ 0 < P.Nq ∧ 0 < P.Ne ∧
      posChecks d.p d.p2 (x0Of d) (s0Of P) (IV.ofNatPair l hh) = true ∧
      I = lamAssemble (x0Of d) d.p2 FR FP ER
        (originEnc d.p d.p2 (s0Of P) FP1 (IV.addRad cY.f2 P.rad) (IV.ofNatPair l hh)) IQ IE := by
  unfold lamFine lamFineT at h
  set lh := IV.sqrtProposal (IV.add d.p2 (IV.sq (s0Of P)))
  cases hs : IV.sqrtCheck (IV.add d.p2 (IV.sq (s0Of P))) lh.1 lh.2 <;>
    simp only [hs, Bool.cond_false, Bool.cond_true, reduceCtorEq] at h
  cases hB : lookup F.T (IV.hull d.p d.r0) <;> cases hY : lookup F.T (IV.hull d.p (IV.ofNatPair lh.1 lh.2)) <;>
    simp only [hB, hY, lamFineL, reduceCtorEq] at h
  rename_i cB cY
  cases h1 : fPt F P.rad d.p <;> cases h2 : f1Pt F P.rad d.p <;> cases h3 : fPt F P.rad d.r0 <;>
    cases h4 : ePt F P.rad d.r0 <;> simp only [h1, h2, h3, h4, lamFineP, reduceCtorEq] at h
  rename_i FP FP1 FR ER
  cases h5 : qSum F (qCtxOf d P.Nq P.rad (s0Of P) cB FP) <;> cases h6 : eSum F (eCtxOf d P.Ne P.rad cB) <;>
    simp only [h5, h6, lamFineS, reduceCtorEq] at h
  rename_i IQ IE
  cases h7 : Nat.blt 0 P.s0d <;> cases h8 : Nat.blt 0 P.Nq <;> cases h9 : Nat.blt 0 P.Ne <;>
    cases h10 : posChecks d.p d.p2 (x0Of d) (s0Of P) (IV.ofNatPair lh.1 lh.2) <;>
    simp only [h7, h8, h9, h10, Bool.and_true, Bool.and_false, Bool.cond_false, Bool.cond_true, reduceCtorEq,
      Option.some.injEq] at h
  exact ⟨lh.1, lh.2, cB, cY, FP, FP1, FR, ER, IQ, IE, hs, rfl, hY, rfl, rfl, rfl, rfl, h5, h6,
    Nat.le_of_ble_eq_true h7, Nat.le_of_ble_eq_true h8, Nat.le_of_ble_eq_true h9, h10, h.symm⟩

theorem posChecks_sound {p' p2 x0 S0 T0 : IV 128} (h : posChecks p' p2 x0 S0 T0 = true) :
    IV.posB p' = true ∧ IV.posB p2 = true ∧ IV.posB x0 = true ∧ IV.posB S0 = true ∧ IV.ltB S0 x0 = true ∧
      IV.posB (IV.sq p2) = true ∧ IV.posB (IV.sq (IV.add T0 p')) = true ∧ IV.posB (IV.mulNat p' 4) = true := by
  simp only [posChecks, Bool.and_eq_true] at h
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4, a5⟩, a6, a7, a8⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

theorem mem_x0Of {d : BasisData} (hd : d.Valid) : IV.Mem x₀ (x0Of d) := by
  have := IV.mem_divPow2 hd.mr0 1
  refine mem_of_mem_iff this ?_
  unfold x₀; norm_num

/-- **The origin term** `∫₀^{s₀} q` (`comp:lambda-origin`, `Calibration.lambda_origin`). -/
theorem originEnc_mem {d : BasisData} (hd : d.Valid) {s₀ : ℝ} {S0 F1 Y T0 : IV 128} (hs : 0 < s₀)
    (hS0 : IV.Mem s₀ S0) (hT0 : IV.Mem (√(p ^ 2 + s₀ ^ 2)) T0) (hF1 : IV.Mem (deriv f₀ p) F1)
    (hY : ∀ ξ ∈ Icc p (√(p ^ 2 + s₀ ^ 2)), IV.Mem (deriv (deriv f₀) ξ) Y) (hp : IV.posB d.p = true)
    (hp2 : IV.posB d.p2 = true) (hpp2 : IV.posB (IV.sq d.p2) = true) (hTp : IV.posB (IV.sq (IV.add T0 d.p)) = true)
    (hp4 : IV.posB (IV.mulNat d.p 4) = true) :
    IV.Mem (∫ s in (0 : ℝ)..s₀, qq s) (originEnc d.p d.p2 S0 F1 Y T0) := by
  have hpp := p_pos
  obtain ⟨α, β, y, hα, hβ, ⟨ξ, hξ, rfl⟩, heq⟩ := lambda_origin hs
  have hI : ∫ s in (0 : ℝ)..s₀, qq s =
      (deriv f₀ p * (s₀ / 2 - s₀ ^ 3 / (24 * p ^ 2) + α) + s₀ ^ 3 / 6 * β * deriv (deriv f₀) ξ) / p := by
    rw [← heq]; field_simp; rfl
  rw [hI]
  have hcube : IV.Mem (s₀ ^ 3) (cube S0) := mem_of_mem_iff (IV.mem_mul (IV.mem_sq hS0) hS0) (by ring)
  have hA : IV.Mem α (IV.hull (IV.ofNat 0) (IV.divPos (IV.divNat (IV.mul (IV.sq (IV.sq S0)) S0) 80)
      (IV.sq d.p2))) := by
    have h0 : IV.Mem (0 : ℝ) (IV.ofNat 0 : IV 128) := by simpa using IV.mem_ofNat (P := 128) 0
    have h1 := IV.mem_divPos hpp2 (IV.mem_divNat (IV.mem_mul (IV.mem_sq (IV.mem_sq hS0)) hS0)
      (by norm_num : 0 < 80)) (IV.mem_sq hd.mp2)
    refine mem_hull_between h0 h1 hα.1 (hα.2.trans_eq ?_)
    push_cast; ring
  have hB : IV.Mem β (IV.hull (IV.divPos d.p (IV.sq (IV.add T0 d.p))) (IV.invPos (IV.mulNat d.p 4))) := by
    have h1 := IV.mem_divPos hTp hd.mp (IV.mem_sq (IV.mem_add hT0 hd.mp))
    have h2 := Jet.mem_invPos hp4 (IV.mem_mulNat hd.mp 4)
    refine mem_hull_between h1 h2 hβ.1 (hβ.2.trans_eq ?_)
    push_cast; ring
  have hc := IV.mem_add (IV.mem_sub (IV.mem_divPow2 hS0 1)
    (IV.mem_divPos hp2 (IV.mem_divNat hcube (by norm_num : 0 < 24)) hd.mp2)) hA
  have hsum := IV.mem_add (IV.mem_mul hF1 hc)
    (IV.mem_mul (IV.mem_mul (IV.mem_divNat hcube (by norm_num : 0 < 6)) hB) (hY ξ hξ))
  have := IV.mem_divPos hp hsum hd.mp
  refine mem_of_mem_iff this ?_
  push_cast; ring

/-- **The fine enclosure of `λ` is sound.** -/
theorem lamFine_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (hF : FRealized F a) {d : BasisData}
    (hd : d.Valid) {P : LamPar} (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ P.rad) {I : IV 128}
    (h : lamFine F d P = some I) : IV.Mem Calibration.lam I := by
  obtain ⟨l, hh, cB, cY, FP, FP1, FR, ER, IQ, IE, hsq, hB, hY, h1, h2, h3, h4, h5, h6, hs0d, hNq, hNe, hpos,
    rfl⟩ := lamFine_some h
  obtain ⟨hp, hp2, hx0p, hS0p, hS0x, hpp2, hTp, hp4⟩ := posChecks_sound hpos
  have hpp := p_pos
  have hx := x₀_pos
  set s₀ : ℝ := (P.s0n : ℝ) / P.s0d with hs₀
  have hS0 : IV.Mem s₀ (s0Of P) := by
    have := IV.mem_ofFrac (P := 128) ⟨false, P.s0n⟩ hs0d
    exact mem_of_mem_iff this (by simp [hs₀])
  have hx0 := mem_x0Of hd
  have hs0 : 0 < s₀ := IV.posB_sound hS0p hS0
  have hs0x : s₀ < x₀ := IV.ltB_sound hS0x hS0 hx0
  have hT0 : IV.Mem (√(p ^ 2 + s₀ ^ 2)) (IV.ofNatPair (P := 128) l hh) :=
    IV.mem_sqrt_of_sqrtCheck hsq (IV.mem_add hd.mp2 (IV.mem_sq hS0))
  have ht0 : √(p ^ 2 + s₀ ^ 2) < R₀ := tt_lt_R₀ hs0.le hs0x
  -- the bounds, the range of `f₀''` near `p`, the point values
  obtain ⟨hC, hC', hE, hE'⟩ := bounds_of_lookup hc hF hrad hd hB
  have hYm : ∀ ξ ∈ Icc p (√(p ^ 2 + s₀ ^ 2)), IV.Mem (deriv (deriv f₀) ξ) (IV.addRad cY.f2 P.rad) := fun ξ hξ =>
    (lookup_exact hc hF hrad hY (Icc_p_R₀_sub ⟨hξ.1, hξ.2.trans ht0.le⟩)
      (mem_hull_between hd.mp hT0 hξ.1 hξ.2)).2.2.2.2.1
  have hFP := fPt_sound hc hF hrad h1 hd.mp
  have hFP1 := f1Pt_sound hc hF hrad h2 hd.mp
  have hFR := fPt_sound hc hF hrad h3 hd.mr0
  have hER := ePt_sound hc hF hrad h4 hd.mr0
  -- the three integrals
  have hI0 := originEnc_mem hd hs0 hS0 hT0 hFP1 hYm hp hp2 hpp2 hTp hp4
  have hIQ := qSum_sound hc hF (c := qCtxOf d P.Nq P.rad (s0Of P) cB FP) hrad hd.mp hd.mp2 hS0
    (IV.mem_sub hx0 hS0) hNq hs0 hs0x.le hFP (mem_magIV _) (mem_magIV _) hC hC' h5
  have hIE := eSum_sound hc hF (c := eCtxOf d P.Ne P.rad cB) hrad hd.mp hd.mp2
    (show IV.Mem (0 : ℝ) (IV.ofNat 0 : IV 128) by simpa using IV.mem_ofNat (P := 128) 0) hx0 hNe (mem_magIV _) (mem_magIV _) hE hE' h6
  -- assembly
  have hsplit : ∫ s in (0 : ℝ)..x₀, qq s = (∫ s in (0 : ℝ)..s₀, qq s) + ∫ s in s₀..x₀, qq s := by
    refine (intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_qq hs0.le) ?_).symm
    refine ContinuousOn.intervalIntegrable (continuousOn_qq.mono fun x hx => ?_)
    rw [uIcc_of_le hs0x.le] at hx
    exact lt_of_lt_of_le hs0 hx.1
  have hlam : Calibration.lam = ((f₀ R₀ - f₀ p) / x₀ - x₀ * e R₀ / p ^ 2 + (∫ s in (0 : ℝ)..s₀, qq s)
      + (∫ s in s₀..x₀, qq s) + (∫ s in (0 : ℝ)..x₀, e (tt p s)) / p ^ 2) / x₀ := by
    rw [eq_div_iff hx.ne', lam_mul_x₀, hsplit]
    ring
  rw [hlam]
  exact IV.mem_divPos hx0p (IV.mem_add (IV.mem_add (IV.mem_add (IV.mem_sub (IV.mem_divPos hx0p
    (IV.mem_sub hFR hFP) hx0) (IV.mem_divPos hp2 (IV.mem_mul hx0 hER) hd.mp2)) hI0) hIQ)
    (IV.mem_divPos hp2 hIE hd.mp2)) hx0

end SandierSerfaty.Certificate.Lambda
