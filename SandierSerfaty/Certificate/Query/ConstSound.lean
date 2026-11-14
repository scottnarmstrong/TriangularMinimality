/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Const
public import SandierSerfaty.Certificate.Basis.Sound
public import SandierSerfaty.Certificate.Table.Bridge
public import SandierSerfaty.Tails.ConstRegion
public import SandierSerfaty.Tails.Uniform

/-!
# Soundness of A4 and A6 (enclosures of `B(l)`, `f₀`, `e` at nodes, and the exterior signs)

* `mem_Trunc_B_l`, `mem_B_l` (A4, `comp:constant-B`): the basis evaluated at an enclosure `X ∋ l` on segment `5`
  (`Basis.basis_sound`) encloses `B̃(l) = Cal.Trunc.B l`, and `B(l)` is within `10⁻¹¹` of it
  (`Tails.abs_dB_l_lt_eps`);
* `mem_f0_exact`, `mem_e_exact`: an enclosure of the truncated `f̃₀(t)`, `ẽ(t)` (a node tuple of the table, the
  output of `Table.chunks_sound_trunc`) widened by `R ≥ 10⁻¹¹ · 2^128` encloses the exact `f₀(t)`, `e(t)` for
  `t ∈ [b, l]` (`Tails.uniform_error_of_finiteCore`);
* `fl_eq`, `fLEnc_mem`, `slopeEnc_mem`, `a6_sound` (A6): `f(l)` and `-π B(l) - λ/2` lie in the enclosures of
  `Query.Const`; if `a6Check` passes, both are positive.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Calibration SandierSerfaty.Tails

theorem l_mem_seg5 : Calibration.l ∈ seg 5 := by
  refine ⟨?_, le_rfl⟩
  have := Calibration.l_eq
  have hs : Calibration.hs = 3 / 40 := rfl
  show R₀ + Calibration.hs ≤ Calibration.l
  rw [hs]; linarith

/-- **A4**: the basis on segment `5` at an enclosure of `l` encloses `B̃(l)`. -/
theorem mem_Trunc_B_l {d : BasisData} (hd : d.Valid) {X : IV 128} (hX : IV.posB X = true)
    (hl : IV.Mem Calibration.l X) : IV.Mem (Trunc.B Calibration.l) (basis d 5 X).bsum.c0 := by
  have h := (basis_sound hd hX (j := 5) (by norm_num)).1.mem_c0 (t := Calibration.l) hl
  have e := trunc_B_eq_Bp (j := 5) (by norm_num) l_mem_seg5
  unfold Bp at e
  rw [e]; exact h

theorem mem_of_abs_lt {x y : ℝ} {I : IV 128} (hI : IV.Mem x I) {R : ℕ} (h : |y - x| < 1 / 10 ^ 11)
    (hR : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ R) : IV.Mem y (IV.addRad I R) := by
  refine IV.mem_addRad hI ?_
  have h2 : (0 : ℝ) < 2 ^ 128 := by positivity
  calc |y - x| * 2 ^ 128 ≤ 1 / 10 ^ 11 * 2 ^ 128 := mul_le_mul_of_nonneg_right h.le h2.le
    _ = 2 ^ 128 / 10 ^ 11 := by ring
    _ ≤ R := hR

/-- **A4**: `B(l)` lies in the enclosure widened by `R ≥ 10⁻¹¹ · 2^128`. -/
theorem mem_B_l {d : BasisData} (hd : d.Valid) {X : IV 128} (hX : IV.posB X = true)
    (hl : IV.Mem Calibration.l X) {R : ℕ} (hR : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ R) :
    IV.Mem (Calibration.B Calibration.l) (IV.addRad (basis d 5 X).bsum.c0 R) :=
  mem_of_abs_lt (mem_Trunc_B_l hd hX hl) abs_dB_l_lt_eps hR

theorem mem_f0_exact (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc Calibration.b Calibration.l) {I : IV 128}
    (hI : IV.Mem (Trunc.f₀ t) I) {R : ℕ} (hR : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ R) :
    IV.Mem (f₀ t) (IV.addRad I R) := by
  obtain ⟨h1, -⟩ := uniform_error_of_finiteCore hc ht
  exact mem_of_abs_lt hI h1 hR

theorem mem_e_exact (hc : FiniteCore) {t : ℝ} (ht : t ∈ Icc Calibration.b Calibration.l) {I : IV 128}
    (hI : IV.Mem (Trunc.e t) I) {R : ℕ} (hR : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ R) :
    IV.Mem (e t) (IV.addRad I R) := by
  obtain ⟨-, h2, -⟩ := uniform_error_of_finiteCore hc ht
  exact mem_of_abs_lt hI h2 hR

/-! ### A6 -/

theorem fl_eq : f Calibration.l = f₀ Calibration.l - f₀ R₀ + e R₀ / 3 -
    lam * (19 / 250 * (2 * R₀ + 19 / 250)) / 2 := by
  have hl : Calibration.l = R₀ + 19 / 250 := rfl
  unfold f mu
  rw [hl]
  ring

theorem lSqSubR2_mem {r0 : IV 128} (h : IV.Mem R₀ r0) :
    IV.Mem (19 / 250 * (2 * R₀ + 19 / 250)) (lSqSubR2 r0) := by
  have h1 := mem_frac_pos 19 250 (by norm_num)
  have h2 := IV.mem_add (IV.mem_mulNat h 2) h1
  have := IV.mem_mul h1 h2
  unfold lSqSubR2
  convert this using 2
  push_cast; ring

theorem fLEnc_mem {r0 f0l f0R eR lamI : IV 128} (hr0 : IV.Mem R₀ r0) (h1 : IV.Mem (f₀ Calibration.l) f0l)
    (h2 : IV.Mem (f₀ R₀) f0R) (h3 : IV.Mem (e R₀) eR) (h4 : IV.Mem lam lamI) :
    IV.Mem (f Calibration.l) (fLEnc r0 f0l f0R eR lamI) := by
  rw [fl_eq]
  have := IV.mem_sub (IV.mem_add (IV.mem_sub h1 h2) (IV.mem_divNat h3 (n := 3) (by norm_num)))
    (IV.mem_divPow2 (IV.mem_mul h4 (lSqSubR2_mem hr0)) 1)
  unfold fLEnc
  convert this using 2
  norm_num

theorem slopeEnc_mem {pi bl lamI : IV 128} (hpi : IV.Mem Real.pi pi) (hb : IV.Mem (B Calibration.l) bl)
    (hlam : IV.Mem lam lamI) :
    IV.Mem (-Real.pi * B Calibration.l - lam / 2) (slopeEnc pi bl lamI) := by
  have := IV.mem_sub (IV.mem_neg (IV.mem_mul hpi hb)) (IV.mem_divPow2 hlam 1)
  unfold slopeEnc
  convert this using 2
  · ring
  · norm_num

theorem muEnc_mem {r0 f0R eR lamI : IV 128} (hr0 : IV.Mem R₀ r0) (h2 : IV.Mem (f₀ R₀) f0R)
    (h3 : IV.Mem (e R₀) eR) (h4 : IV.Mem lam lamI) : IV.Mem mu (muEnc r0 f0R eR lamI) := by
  have := IV.mem_sub (IV.mem_sub h2 (IV.mem_divNat h3 (n := 3) (by norm_num)))
    (IV.mem_divPow2 (IV.mem_mul h4 (IV.mem_sq hr0)) 1)
  unfold muEnc
  convert this using 2
  unfold mu; norm_num

/-- **A6**: if `a6Check` passes on enclosures of `π`, `R₀`, `f₀(l)`, `f₀(R₀)`, `e(R₀)`, `B(l)`, `λ`, then
`f(l) > 0` and `-π B(l) - λ/2 > 0` (`comp:tail-signs`). -/
theorem a6_sound {pi r0 f0l f0R eR bl lamI : IV 128} (hc : a6Check pi r0 f0l f0R eR bl lamI = true)
    (hpi : IV.Mem Real.pi pi) (hr0 : IV.Mem R₀ r0) (h1 : IV.Mem (f₀ Calibration.l) f0l)
    (h2 : IV.Mem (f₀ R₀) f0R) (h3 : IV.Mem (e R₀) eR) (hb : IV.Mem (B Calibration.l) bl)
    (hlam : IV.Mem lam lamI) :
    0 < f Calibration.l ∧ 0 < -Real.pi * B Calibration.l - lam / 2 := by
  simp only [a6Check, Bool.and_eq_true] at hc
  exact ⟨IV.posB_sound hc.1 (fLEnc_mem hr0 h1 h2 h3 hlam),
    IV.posB_sound hc.2 (slopeEnc_mem hpi hb hlam)⟩

end SandierSerfaty.Certificate.Query
