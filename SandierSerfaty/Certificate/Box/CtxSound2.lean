/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxSound
public import SandierSerfaty.Certificate.Box.SecondDeriv

/-!
# Soundness of the second-derivative queries on a rectangle (A7, A10)

* `mkDCtx2_sound`: if `mkDCtx2 … = some c`, then for every `(d, s) ∈ Dd × Ss` with `d ≥ b` the enclosures of `c`
  hold at `(d, s)` (`DMem2`: the first-order data of `Query.DMem`, plus `f''(t) = f₀''(t) - λ ∈ c.f2` and a right
  derivative `E ∈ c.e2` of `e'` at `t = √(d² + s²)`); the table is realized in `Encl2` form and the exterior tuple
  replaces the table beyond `l`.
* `gssOf_mem`, `gddOf_mem`: for `DMem2 d s c`, `s ↦ G_s(d, s)` has a right derivative in `gssOf c` at `s`, and
  `d ↦ G_d(d, s)` one in `gddOf c` at `d` (`Box.SecondDeriv`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The enclosures of a second-order context hold at the point `(d, s)`. -/
structure DMem2 (d s : ℝ) (c : DCtx2) : Prop extends DMem d s c.toDCtx where
  /-- `f''(t) = f₀''(t) - λ ∈ c.f2`. -/
  mf2 : IV.Mem (deriv (deriv f₀) (tt d s) - lam) c.f2
  /-- A right derivative of `e'` at `t`, enclosed by `c.e2`. -/
  me2 : ∃ E, HasDerivWithinAt (deriv e) E (Ici (tt d s)) (tt d s) ∧ IV.Mem E c.e2

theorem mkChk2_some {T : ITable} {f0lI k0I lsqI lI lamI muI : IV 128} {rad : ℕ} {Dd Ss t2 : IV 128} {lh : ℕ × ℕ}
    {c : DCtx2} (h : mkChk2 T f0lI k0I lsqI lI lamI muI rad Dd Ss t2 lh = some c) :
    IV.posB Dd = true ∧ IV.sqrtCheck t2 lh.1 lh.2 = true ∧ IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2) = true ∧
      ∃ c', lookupX T f0lI k0I lsqI lI (IV.ofNatPair lh.1 lh.2) = some c' ∧
        c = dctx2Of Dd Ss (IV.ofNatPair lh.1 lh.2) t2 lamI muI rad c' := by
  unfold mkChk2 at h
  cases h1 : (and (IV.posB Dd) (and (IV.sqrtCheck t2 lh.1 lh.2) (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2))))
  · simp [h1] at h
  · simp only [h1, Bool.cond_true] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1, h2, h3⟩ := h1
    refine ⟨h1, h2, h3, ?_⟩
    cases hl : lookupX T f0lI k0I lsqI lI (IV.ofNatPair lh.1 lh.2) with
    | none => simp [hl] at h
    | some c' =>
      simp only [hl, Option.some.injEq] at h
      exact ⟨c', rfl, h.symm⟩

/-- **Soundness of the second-order context** of a rectangle. -/
theorem mkDCtx2_sound (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (H : Encl2 T a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {f0lI k0I lsqI lI lamI muI : IV 128} (hl : IV.Mem Calibration.l lI)
    (hf0l : IV.Mem (f₀ Calibration.l) f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) lsqI) (hlam : IV.Mem lam lamI) (hmu : IV.Mem mu muI) {Dd Ss : IV 128}
    {c : DCtx2} (h : mkDCtx2 T f0lI k0I lsqI lI lamI muI rad Dd Ss = some c) {d s : ℝ}
    (hbd : Calibration.b ≤ d) (hd : IV.Mem d Dd) (hs : IV.Mem s Ss) : 0 < d ∧ DMem2 d s c := by
  unfold mkDCtx2 at h
  obtain ⟨h1, h2, h3, c', hlk, hc'⟩ := mkChk2_some h
  have hd0 : 0 < d := lt_of_lt_of_le Calibration.b_pos hbd
  have ht2 : IV.Mem (d ^ 2 + s ^ 2) (IV.add (IV.sq Dd) (IV.sq Ss)) := IV.mem_add (IV.mem_sq hd) (IV.mem_sq hs)
  set lh := IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss)) with hlh
  have htI : IV.Mem (tt d s) (IV.ofNatPair (P := 128) lh.1 lh.2) := IV.mem_sqrt_of_sqrtCheck h2 ht2
  have hdt : d ≤ tt d s := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
  have hbt : Calibration.b ≤ tt d s := hbd.trans hdt
  have htt2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd0
  obtain ⟨c'', hlk', hex⟩ := lookupX_sound hc H hrad hbt htI hl hf0l hk0 hlsq
  rw [hlk] at hlk'
  cases hlk'
  obtain ⟨e0, e1, e2, e3, e4, E, hE, hE2⟩ := hex
  subst hc'
  refine ⟨hd0, ⟨⟨hd, hs, htI, ht2, Jet.mem_invPos h3 htI, ?_, Jet.mem_invPos h1 hd, ?_, ?_, e2, e3⟩, ?_, E, hE, hE2⟩⟩
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
  · exact IV.mem_sub e4 hlam

/-! ### The formulas on the context -/

section formulas

variable {d s : ℝ} {c : DCtx2}

theorem mem_rs (h : DMem2 d s c) : IV.Mem (s * (tt d s)⁻¹) (rsOf c.toDCtx) := IV.mem_mul h.ms h.miT

theorem mem_rd (h : DMem2 d s c) : IV.Mem (d * (tt d s)⁻¹) (rdOf c.toDCtx) := IV.mem_mul h.md h.miT

theorem mem_rp {r : ℝ} {rI : IV 128} (hr : IV.Mem r rI) {ti : ℝ} {tI : IV 128} (ht : IV.Mem ti tI) :
    IV.Mem ((1 - r ^ 2) * ti) (rpOf rI tI) :=
  IV.mem_mul (IV.mem_sub (by simpa using IV.mem_ofNat (P := 128) 1) (IV.mem_sq hr)) ht

theorem mem_As (h : DMem2 d s c) :
    IV.Mem (-(d * s * ((d ^ 2 + s ^ 2)⁻¹) ^ 2 * 2)) (asOf c.toDCtx) := by
  have := IV.mem_neg (IV.mem_mulNat (IV.mem_mul (IV.mem_mul h.md h.ms) (IV.mem_sq h.miT2)) 2)
  exact memEq this (by push_cast; ring)

theorem mem_Ass (h : DMem2 d s c) :
    IV.Mem (-(d * ((d ^ 2 + s ^ 2)⁻¹) ^ 2 * 2) + 8 * d * s ^ 2 * ((d ^ 2 + s ^ 2)⁻¹) ^ 3) (assOf c) := by
  have h1 := IV.mem_neg (IV.mem_mulNat (IV.mem_mul h.md (IV.mem_sq h.miT2)) 2)
  have h2 := IV.mem_mulNat (IV.mem_mul (IV.mem_mul h.md (IV.mem_sq h.ms)) (IV.mem_mul (IV.mem_sq h.miT2) h.miT2)) 8
  refine memEq (IV.mem_add h1 h2) ?_
  push_cast; ring

theorem mem_A (h : DMem2 d s c) : IV.Mem (d * (d ^ 2 + s ^ 2)⁻¹) (aOf c.toDCtx) := IV.mem_mul h.md h.miT2

theorem mem_Z (h : DMem2 d s c) :
    IV.Mem (-(s ^ 2 * (d⁻¹ * (d ^ 2 + s ^ 2)⁻¹))) (zOf c.toDCtx) :=
  IV.mem_neg (IV.mem_mul (IV.mem_sq h.ms) (IV.mem_mul h.miD h.miT2))

theorem mem_Ad (h : DMem2 d s c) :
    IV.Mem ((1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * 2) * (d ^ 2 + s ^ 2)⁻¹) (adOf c.toDCtx) := by
  have := IV.mem_mul (IV.mem_sub (by simpa using IV.mem_ofNat (P := 128) 1)
    (IV.mem_mulNat (IV.mem_mul (IV.mem_sq h.md) h.miT2) 2)) h.miT2
  exact memEq this (by push_cast; ring)

theorem mem_Zd (h : DMem2 d s c) :
    IV.Mem ((1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * 2) * (d ^ 2 + s ^ 2)⁻¹ + (d⁻¹) ^ 2) (zdOf c.toDCtx) :=
  IV.mem_add (mem_Ad h) (IV.mem_sq h.miD)

theorem mem_Add (h : DMem2 d s c) :
    IV.Mem (2 * d * (d ^ 2 - 3 * s ^ 2) * ((d ^ 2 + s ^ 2)⁻¹) ^ 3) (addOf c) := by
  have := IV.mem_mulNat (IV.mem_mul (IV.mem_mul h.md (IV.mem_sub (IV.mem_sq h.md)
    (IV.mem_mulNat (IV.mem_sq h.ms) 3))) (IV.mem_mul (IV.mem_sq h.miT2) h.miT2)) 2
  refine memEq this ?_
  push_cast; ring

theorem mem_Zdd (h : DMem2 d s c) :
    IV.Mem (2 * d * (d ^ 2 - 3 * s ^ 2) * ((d ^ 2 + s ^ 2)⁻¹) ^ 3 - 2 * (d⁻¹) ^ 3) (zddOf c) := by
  have := IV.mem_sub (mem_Add h) (IV.mem_mulNat (IV.mem_mul (IV.mem_sq h.miD) h.miD) 2)
  refine memEq this ?_
  push_cast; ring

/-- **`G_ss`** encloses the right derivative of `G_s(d, ·)`. -/
theorem gssOf_mem (h : DMem2 d s c) (hd : 0 < d) (hs : 0 ≤ s) :
    ∃ F, HasDerivWithinAt (Gs d) F (Ici s) s ∧ IV.Mem F (gssOf c) := by
  obtain ⟨E, hE, hE2⟩ := h.me2
  have ht0 : 0 < tt d s := tt_pos hd
  have hF2 := hasDerivAt_deriv_f₀ ht0
  refine ⟨_, hasDerivWithinAt_Gs hd hs hF2 hE, ?_⟩
  have mrs := mem_rs h
  have mrp := mem_rp mrs h.miT
  have mAs := mem_As h
  have t1 := IV.mem_mul (mem_Ass h) h.mf
  have t2 := IV.mem_mul (IV.mem_mul (IV.mem_mulNat mAs 2) h.mf1) mrs
  have t3 := IV.mem_mul (mem_A h) (IV.mem_add (IV.mem_mul (IV.mem_mul h.mf2 mrs) mrs) (IV.mem_mul h.mf1 mrp))
  have t4 := IV.mem_mul (mem_Ass h) h.me
  have t5 := IV.mem_mul (IV.mem_mul (IV.mem_mulNat mAs 2) h.me1) mrs
  have t6 := IV.mem_mul (mem_Z h) (IV.mem_add (IV.mem_mul (IV.mem_mul hE2 mrs) mrs) (IV.mem_mul h.me1 mrp))
  unfold gssOf
  refine memEq (IV.mem_add (IV.mem_add (IV.mem_add (IV.mem_add (IV.mem_add t1 t2) t3) t4) t5) t6) ?_
  unfold GssF
  push_cast
  ring

/-- **`G_dd`** encloses the right derivative of `G_d(·, s)`. -/
theorem gddOf_mem (h : DMem2 d s c) (hd : 0 < d) :
    ∃ F, HasDerivWithinAt (fun u => Gd u s) F (Ici d) d ∧ IV.Mem F (gddOf c) := by
  obtain ⟨E, hE, hE2⟩ := h.me2
  have ht0 : 0 < tt d s := tt_pos hd
  have hF2 := hasDerivAt_deriv_f₀ ht0
  refine ⟨_, hasDerivWithinAt_Gd hd hF2 hE, ?_⟩
  have mrd := mem_rd h
  have mrp := mem_rp mrd h.miT
  have mAd := mem_Ad h
  have t1 := IV.mem_mul (mem_Add h) h.mf
  have t2 := IV.mem_mul (IV.mem_mul (IV.mem_mulNat mAd 2) h.mf1) mrd
  have t3 := IV.mem_mul (mem_A h) (IV.mem_add (IV.mem_mul (IV.mem_mul h.mf2 mrd) mrd) (IV.mem_mul h.mf1 mrp))
  have t4 := IV.mem_mul (mem_Zdd h) h.me
  have t5 := IV.mem_mul (IV.mem_mul (IV.mem_mulNat (mem_Zd h) 2) h.me1) mrd
  have t6 := IV.mem_mul (mem_Z h) (IV.mem_add (IV.mem_mul (IV.mem_mul hE2 mrd) mrd) (IV.mem_mul h.me1 mrp))
  unfold gddOf
  refine memEq (IV.mem_add (IV.mem_add (IV.mem_add (IV.mem_add (IV.mem_add t1 t2) t3) t4) t5) t6) ?_
  unfold GddF
  push_cast
  ring

end formulas

end SandierSerfaty.Certificate.Box
