/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.DerivG
public import SandierSerfaty.Certificate.Query.LamSound

/-!
# Soundness of the derivative-`G` queries

* `gd_eq`, `gs_eq`: the formulas `G_v = A_v f + A f' r_v + Z_v e + Z e' r_v` of `comp:G-derivatives` equal the
  exact `Calibration.Gd`, `Calibration.Gs` (the derivatives of `Calibration.G`, `Calibration.hasDerivAt_G_d`,
  `hasDerivAt_G_s`);
* `gdOf_mem`, `gsOf_mem`: if `DMem d s c` (the enclosures of the context hold at the point `(d, s)`), then
  `Gd d s ∈ gdOf c` and `Gs d s ∈ gsOf c`;
* `mkDCtx_sound`: if `mkDCtx T bI lI lamI muI rad Dd Ss = some c` (`bI ∋ b`, `lI ∋ l`, `lamI ∋ λ`, `muI ∋ μ`,
  `rad ≥ 10⁻¹¹ 2^128`, the table realized by real nodes, the finite-core premise), then `DMem d s c` at every
  `(d, s) ∈ Dd × Ss`. Consequently `Gd d s ∈ gdOf c` and `Gs d s ∈ gsOf c` on the whole rectangle.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Calibration
open SandierSerfaty.Tails

/-- The enclosures of the context hold at the point `(d, s)`. -/
structure DMem (d s : ℝ) (c : DCtx) : Prop where
  md : IV.Mem d c.d
  ms : IV.Mem s c.s
  mt : IV.Mem (tt d s) c.t
  mt2 : IV.Mem (d ^ 2 + s ^ 2) c.t2
  miT : IV.Mem (tt d s)⁻¹ c.iT
  miT2 : IV.Mem (d ^ 2 + s ^ 2)⁻¹ c.iT2
  miD : IV.Mem d⁻¹ c.iD
  mf : IV.Mem (f (tt d s)) c.f
  mf1 : IV.Mem (df (tt d s)) c.f1
  me : IV.Mem (e (tt d s)) c.e
  me1 : IV.Mem (deriv e (tt d s)) c.e1

/-! ### The formulas -/

theorem gd_eq {d s : ℝ} (hd : 0 < d) :
    Gd d s = ((1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * (2 : ℕ)) * (d ^ 2 + s ^ 2)⁻¹) * f (tt d s) +
      (d * (d ^ 2 + s ^ 2)⁻¹ * df (tt d s)) * (d * (tt d s)⁻¹) +
      (((1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * (2 : ℕ)) * (d ^ 2 + s ^ 2)⁻¹ + (d⁻¹) ^ 2) * e (tt d s) +
        (-(s ^ 2 * (d⁻¹ * (d ^ 2 + s ^ 2)⁻¹)) * deriv e (tt d s)) * (d * (tt d s)⁻¹)) := by
  have ht : 0 < tt d s := tt_pos hd
  have h2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd
  have hs : s ^ 2 = tt d s ^ 2 - d ^ 2 := by linarith
  have hT2 : d ^ 2 + s ^ 2 = tt d s ^ 2 := h2.symm
  unfold Gd
  rw [hT2]
  generalize tt d s = T at *
  rw [hs]
  push_cast
  field_simp
  ring

theorem gs_eq {d s : ℝ} (hd : 0 < d) :
    Gs d s = (-(d * s * (d ^ 2 + s ^ 2)⁻¹ ^ 2 * (2 : ℕ))) * f (tt d s) +
      (d * (d ^ 2 + s ^ 2)⁻¹ * df (tt d s)) * (s * (tt d s)⁻¹) +
      ((-(d * s * (d ^ 2 + s ^ 2)⁻¹ ^ 2 * (2 : ℕ))) * e (tt d s) +
        (-(s ^ 2 * (d⁻¹ * (d ^ 2 + s ^ 2)⁻¹)) * deriv e (tt d s)) * (s * (tt d s)⁻¹)) := by
  have ht : 0 < tt d s := tt_pos hd
  have h2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd
  have hs : s ^ 2 = tt d s ^ 2 - d ^ 2 := by linarith
  have hT2 : d ^ 2 + s ^ 2 = tt d s ^ 2 := h2.symm
  have hs3 : s ^ 3 = s * (tt d s ^ 2 - d ^ 2) := by rw [← hs]; ring
  unfold Gs
  rw [hT2]
  generalize tt d s = T at *
  rw [hs3, hs]
  push_cast
  field_simp
  ring

/-! ### Enclosures of the formulas -/

theorem gdOf_mem {d s : ℝ} (hd : 0 < d) {c : DCtx} (h : DMem d s c) : IV.Mem (Gd d s) (gdOf c) := by
  rw [gd_eq hd]
  have hA : IV.Mem (d * (d ^ 2 + s ^ 2)⁻¹) (aOf c) := IV.mem_mul h.md h.miT2
  have hAd : IV.Mem ((1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * (2 : ℕ)) * (d ^ 2 + s ^ 2)⁻¹) (adOf c) :=
    IV.mem_mul (IV.mem_sub (by simpa using IV.mem_ofNat (P := 128) 1) (IV.mem_mulNat (IV.mem_mul (IV.mem_sq h.md) h.miT2) 2))
      h.miT2
  have hZd : IV.Mem ((1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * (2 : ℕ)) * (d ^ 2 + s ^ 2)⁻¹ + (d⁻¹) ^ 2) (zdOf c) :=
    IV.mem_add hAd (IV.mem_sq h.miD)
  have hZ : IV.Mem (-(s ^ 2 * (d⁻¹ * (d ^ 2 + s ^ 2)⁻¹))) (zOf c) :=
    IV.mem_neg (IV.mem_mul (IV.mem_sq h.ms) (IV.mem_mul h.miD h.miT2))
  have hr : IV.Mem (d * (tt d s)⁻¹) (rdOf c) := IV.mem_mul h.md h.miT
  exact IV.mem_add (IV.mem_add (IV.mem_mul hAd h.mf) (IV.mem_mul (IV.mem_mul hA h.mf1) hr))
    (IV.mem_add (IV.mem_mul hZd h.me) (IV.mem_mul (IV.mem_mul hZ h.me1) hr))

theorem gsOf_mem {d s : ℝ} (hd : 0 < d) {c : DCtx} (h : DMem d s c) : IV.Mem (Gs d s) (gsOf c) := by
  rw [gs_eq hd]
  have hA : IV.Mem (d * (d ^ 2 + s ^ 2)⁻¹) (aOf c) := IV.mem_mul h.md h.miT2
  have hAs : IV.Mem (-(d * s * (d ^ 2 + s ^ 2)⁻¹ ^ 2 * (2 : ℕ))) (asOf c) :=
    IV.mem_neg (IV.mem_mulNat (IV.mem_mul (IV.mem_mul h.md h.ms) (IV.mem_sq h.miT2)) 2)
  have hZ : IV.Mem (-(s ^ 2 * (d⁻¹ * (d ^ 2 + s ^ 2)⁻¹))) (zOf c) :=
    IV.mem_neg (IV.mem_mul (IV.mem_sq h.ms) (IV.mem_mul h.miD h.miT2))
  have hr : IV.Mem (s * (tt d s)⁻¹) (rsOf c) := IV.mem_mul h.ms h.miT
  exact IV.mem_add (IV.mem_add (IV.mem_mul hAs h.mf) (IV.mem_mul (IV.mem_mul hA h.mf1) hr))
    (IV.mem_add (IV.mem_mul hAs h.me) (IV.mem_mul (IV.mem_mul hZ h.me1) hr))

/-! ### The context of a rectangle -/

theorem mkChk_some {T : ITable} {bI lI lamI muI : IV 128} {rad : ℕ} {Dd Ss t2 : IV 128} {lh : ℕ × ℕ} {c : DCtx}
    (h : mkChk T bI lI lamI muI rad Dd Ss t2 lh = some c) :
    IV.posB Dd = true ∧ IV.sqrtCheck t2 lh.1 lh.2 = true ∧ IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2) = true ∧
      SInt.ble bI.hi (IV.ofNatPair (P := 128) lh.1 lh.2).lo = true ∧
      SInt.ble (IV.ofNatPair (P := 128) lh.1 lh.2).hi lI.lo = true ∧
      ∃ c', lookup T (IV.ofNatPair lh.1 lh.2) = some c' ∧
        c = dctxOf Dd Ss (IV.ofNatPair lh.1 lh.2) t2 lamI muI rad c' := by
  unfold mkChk at h
  cases h1 : (and (IV.posB Dd) (and (IV.sqrtCheck t2 lh.1 lh.2) (and (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2))
      (and (SInt.ble bI.hi (IV.ofNatPair (P := 128) lh.1 lh.2).lo)
        (SInt.ble (IV.ofNatPair (P := 128) lh.1 lh.2).hi lI.lo)))))
  · simp [h1] at h
  · simp only [h1, Bool.cond_true] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1, h2, h3, h4, h5⟩ := h1
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    cases hl : lookup T (IV.ofNatPair lh.1 lh.2) with
    | none => simp [hl] at h
    | some c' =>
      simp only [hl, Option.some.injEq] at h
      exact ⟨c', rfl, h.symm⟩

/-- **Soundness of the context.** For `(d, s)` in the rectangle, all the enclosures of `DCtx` hold. -/
theorem mkDCtx_sound (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {bI lI lamI muI : IV 128}
    (hb : IV.Mem Calibration.b bI) (hl : IV.Mem Calibration.l lI) (hlam : IV.Mem lam lamI)
    (hmu : IV.Mem mu muI) {rad : ℕ} (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {Dd Ss : IV 128} {c : DCtx}
    (h : mkDCtx T bI lI lamI muI rad Dd Ss = some c) {d s : ℝ} (hd : IV.Mem d Dd) (hs : IV.Mem s Ss) :
    0 < d ∧ DMem d s c := by
  unfold mkDCtx at h
  obtain ⟨h1, h2, h3, h4, h5, c', hlk, hc'⟩ := mkChk_some h
  have hd0 : 0 < d := IV.posB_sound h1 hd
  have ht2 : IV.Mem (d ^ 2 + s ^ 2) (IV.add (IV.sq Dd) (IV.sq Ss)) := IV.mem_add (IV.mem_sq hd) (IV.mem_sq hs)
  set lh := IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss)) with hlh
  have htI : IV.Mem (tt d s) (IV.ofNatPair (P := 128) lh.1 lh.2) := IV.mem_sqrt_of_sqrtCheck h2 ht2
  have hbt : Calibration.b ≤ tt d s := IV.leB_sound h4 hb htI
  have htl : tt d s ≤ Calibration.l := IV.leB_sound h5 htI hl
  have ht : tt d s ∈ Icc Calibration.b Calibration.l := ⟨hbt, htl⟩
  have htt2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd0
  obtain ⟨c1, hc1, m1⟩ := lookup_f0 hT ht htI
  obtain ⟨c2, hc2, m2⟩ := lookup_f1 hT ht htI
  obtain ⟨c3, hc3, m3⟩ := lookup_e0 hT ht htI
  obtain ⟨c4, hc4, m4⟩ := lookup_e1 hT ht htI
  rw [hlk] at hc1 hc2 hc3 hc4
  rw [← Option.some.inj hc1] at m1
  rw [← Option.some.inj hc2] at m2
  rw [← Option.some.inj hc3] at m3
  rw [← Option.some.inj hc4] at m4
  obtain ⟨uf, ue, uf1, ue1, -⟩ := uniform_error_of_finiteCore hc ht
  have e0 := mem_of_abs_lt m1 uf hrad
  have e1 := mem_of_abs_lt m2 uf1 hrad
  have e2 := mem_of_abs_lt m3 ue hrad
  have e3 := mem_of_abs_lt m4 ue1 hrad
  subst hc'
  refine ⟨hd0, ⟨hd, hs, htI, ht2, Jet.mem_invPos h3 htI, ?_, Jet.mem_invPos h1 hd, ?_, ?_, e2, e3⟩⟩
  · have := IV.mem_sq (Jet.mem_invPos h3 htI)
    have e : (d ^ 2 + s ^ 2)⁻¹ = (tt d s)⁻¹ ^ 2 := by rw [← htt2, inv_pow]
    rw [e]
    exact this
  · have := IV.mem_sub (IV.mem_sub e0 (IV.mem_divPow2 (IV.mem_mul hlam ht2) 1)) hmu
    have e : f (tt d s) = f₀ (tt d s) - lam * (d ^ 2 + s ^ 2) / 2 ^ 1 - mu := by
      unfold f
      rw [htt2]
      ring
    rw [e]
    exact this
  · have := IV.mem_sub e1 (IV.mem_mul hlam htI)
    unfold df
    exact this

end SandierSerfaty.Certificate.Query
