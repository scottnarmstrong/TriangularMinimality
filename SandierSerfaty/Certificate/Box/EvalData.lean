/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.EvalSound
public import SandierSerfaty.Certificate.Box.CtxDef
public import SandierSerfaty.Certificate.Box.A7
public import SandierSerfaty.Certificate.Query.Table
public import SandierSerfaty.Certificate.Query.ConstSound

/-!
# The hypotheses of the evaluator from the finite data (`EvalHyp` from literals)

`evalHyp_of_data` derives `Box.EvalHyp E rf re rlam rmu rκ rc` (the hypotheses of the static error budget of the box
evaluator) from

* `QRealizes E.T rf re`: every cell of the query table is the output of a passing `Query.cellCheck` against realized
  table nodes (the content of the table chunks, `Table.TableEncloses`; `cellCheck_sound` gives `CellValid`);
* enclosures `lamI ∋ λ`, `muI ∋ μ`, `κI ∋ κ = -π B(l) - λ/2`, `cI ∋ c = f(l) - κ l²`, `lsqI ∋ l²` (they are produced
  by `Query.lamEnc_sound`, `muEnc_mem`, `slopeEnc_mem`, `fLEnc_mem`);
* the Boolean `evalHypCheck E lamI muI κI cI lsqI rf re`, a finite test on literals: the dyadic constants `λ̂, μ̂, κ̂, ĉ`
  of `E` lie in their enclosures, `|λ̂|, |μ̂| ≤ 8`, `|c| ≤ 1`, the radii are small, `lsq ≥ l² + 2⁻¹²⁷` and `lsq ≥ 1/4`.

The radii are the widths of the enclosures (`widthR`), so `|λ - λ̂| ≤ widthR lamI` etc. is automatic.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The real width of an enclosure, `(hi - lo)/2^128` (as a magnitude). -/
@[expose] noncomputable def widthR (I : IV 128) : ℝ := ((SInt.sub I.hi I.lo).mag : ℝ) / 2 ^ 128

/-- **Realization of the query table by the table chunks**: each cell passes `cellCheck` against realized table
nodes of a segment `j ≤ 6`. -/
@[expose] def QRealizes (Q : QTable) (rf re : ℕ) : Prop :=
  ∀ i < Q.n, ∃ j : ℕ, j ≤ 6 ∧ ∃ (a b : ℝ) (v u : IV 128) (ct nt : Tup),
    cellCheck v u ct nt (Q.cell i) rf re = true ∧ Icc a b ⊆ seg j ∧
    TupEncl (Icc a b) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) ct ∧
    TupEncl {b} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) nt ∧ IV.Mem a v ∧ IV.Mem b u ∧
    Calibration.b ≤ a ∧ b ≤ Calibration.l

theorem QRealizes.valid {Q : QTable} {rf re : ℕ} (h : QRealizes Q rf re) :
    ∀ i < Q.n, CellValid (Q.cell i) rf re := by
  intro i hi
  obtain ⟨j, hj, a, b, v, u, ct, nt, hc, hseg, hct, hnt, hv, hu, hab, hbl⟩ := h i hi
  exact cellCheck_sound hj hc hseg hct hnt hv hu hab hbl

theorem abs_sub_le_widthR {x y : ℝ} {I : IV 128} (hx : IV.Mem x I) (hy : IV.Mem y I) : |x - y| ≤ widthR I := by
  have hN := two_pow_pos'
  have hmag : ((SInt.sub I.hi I.lo).mag : ℝ) = ((I.hi.toInt : ℤ) : ℝ) - ((I.lo.toInt : ℤ) : ℝ) := by
    have h1 : (0 : ℤ) ≤ I.hi.toInt - I.lo.toInt := by
      have a1 : ((I.lo.toInt : ℤ) : ℝ) ≤ ((I.hi.toInt : ℤ) : ℝ) := by linarith [hx.1, hx.2]
      have : I.lo.toInt ≤ I.hi.toInt := by exact_mod_cast a1
      omega
    have h2 : ((SInt.sub I.hi I.lo).mag : ℤ) = I.hi.toInt - I.lo.toInt := by
      have := SInt.abs_toInt (SInt.sub I.hi I.lo)
      rw [SInt.toInt_sub, abs_of_nonneg h1] at this
      exact this.symm
    have := congrArg (fun z : ℤ => (z : ℝ)) h2
    simpa using this
  unfold widthR
  rw [hmag]
  have e1 : (x - y) * 2 ^ 128 = x * 2 ^ 128 - y * 2 ^ 128 := by ring
  have e2 : (y - x) * 2 ^ 128 = y * 2 ^ 128 - x * 2 ^ 128 := by ring
  refine abs_sub_le_iff.2 ⟨by rw [le_div_iff₀ hN]; linarith [hx.1, hx.2, hy.1, hy.2],
    by rw [le_div_iff₀ hN]; linarith [hx.1, hx.2, hy.1, hy.2]⟩

theorem fx_mem_of_ble {x : Fx 128} {I : IV 128}
    (h : SInt.ble I.lo x.v = true ∧ SInt.ble x.v I.hi = true) : IV.Mem x.val I := by
  obtain ⟨h1, h2⟩ := h
  rw [SInt.ble_iff] at h1 h2
  have hN := two_pow_pos'
  rw [Fx.val_def]
  constructor
  · rw [div_mul_cancel₀ _ hN.ne']; exact_mod_cast h1
  · rw [div_mul_cancel₀ _ hN.ne']; exact_mod_cast h2

/-- **The finite test** of the evaluator hypotheses. -/
@[expose] def evalHypCheck (E : EvalData) (lamI muI κI cI lsqI : IV 128) (rf re : Nat) : Bool :=
  and (and (and (and (SInt.ble lamI.lo E.lam.v) (SInt.ble E.lam.v lamI.hi))
            (and (SInt.ble muI.lo E.mu.v) (SInt.ble E.mu.v muI.hi)))
          (and (and (SInt.ble κI.lo E.kap.v) (SInt.ble E.kap.v κI.hi))
            (and (SInt.ble cI.lo E.cc.v) (SInt.ble E.cc.v cI.hi))))
    (and (and (and (Nat.ble E.lam.v.mag (Nat.shiftLeft 1 131)) (Nat.ble E.mu.v.mag (Nat.shiftLeft 1 131)))
          (Nat.ble (Nat.add (Nat.add rf re) (Nat.add (SInt.sub lamI.hi lamI.lo).mag (SInt.sub muI.hi muI.lo).mag))
            (Nat.shiftLeft 1 127)))
      (and (absLe cI (Nat.shiftLeft 1 128))
        (and (SInt.ble (SInt.add lsqI.hi ⟨false, 2⟩) E.lsq.v) (SInt.ble ⟨false, Nat.shiftLeft 1 126⟩ E.lsq.v))))

/-- **`EvalHyp` from the finite data.** -/
theorem evalHyp_of_data {E : EvalData} {rf re : ℕ} {lamI muI κI cI lsqI : IV 128} (hQ : QRealizes E.T rf re)
    (hlam : IV.Mem Calibration.lam lamI) (hmu : IV.Mem Calibration.mu muI) (hκ : IV.Mem extSlope κI)
    (hc : IV.Mem extConst cI) (hlsq : IV.Mem (Calibration.l ^ 2) lsqI)
    (hchk : evalHypCheck E lamI muI κI cI lsqI rf re = true) :
    EvalHyp E rf re (widthR lamI) (widthR muI) (widthR κI) (widthR cI) := by
  simp only [evalHypCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨hl1, hm1⟩, hk1, hc1⟩, ⟨⟨hl8, hm8⟩, hsm⟩, hcabs, hlsq1, hlsq2⟩ := hchk
  have hN := two_pow_pos'
  refine ⟨hQ.valid, abs_sub_le_widthR hlam (fx_mem_of_ble hl1), abs_sub_le_widthR hmu (fx_mem_of_ble hm1),
    abs_term hl8, abs_term hm8, ?_, abs_sub_le_widthR hκ (fx_mem_of_ble hk1),
    abs_sub_le_widthR hc (fx_mem_of_ble hc1), ?_, ?_, ?_⟩
  · -- the radii are small
    have h := Nat.ble_eq.mp hsm
    rw [SInt.nat_shiftLeft_eq, one_mul] at h
    have h' : ((rf + re + ((SInt.sub lamI.hi lamI.lo).mag + (SInt.sub muI.hi muI.lo).mag) : ℕ) : ℝ) ≤ 2 ^ 127 := by
      exact_mod_cast h
    push_cast at h'
    unfold widthR
    have e : (rf : ℝ) / 2 ^ 128 + re / 2 ^ 128 + (SInt.sub lamI.hi lamI.lo).mag / 2 ^ 128 +
        (SInt.sub muI.hi muI.lo).mag / 2 ^ 128 =
        ((rf : ℝ) + re + ((SInt.sub lamI.hi lamI.lo).mag + (SInt.sub muI.hi muI.lo).mag)) / 2 ^ 128 := by ring
    rw [e, div_le_iff₀ hN]
    have : (2 : ℝ) ^ 127 * 2 = 2 ^ 128 := by norm_num
    nlinarith
  · -- `|c| ≤ 1`
    have := absLe_sound hcabs hc
    have e : ((Nat.shiftLeft 1 128 : ℕ) : ℝ) / 2 ^ 128 = 1 := by
      rw [SInt.nat_shiftLeft_eq, one_mul]; norm_num
    rwa [e] at this
  · -- `lsq ≥ l² + 2⁻¹²⁷`
    have h1 := (SInt.ble_iff _ _).1 hlsq1
    rw [SInt.toInt_add, SInt.toInt_false] at h1
    have hhi := hlsq.2
    have h1' : ((lsqI.hi.toInt : ℤ) : ℝ) + 2 ≤ ((E.lsq.v.toInt : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Fx.val_def]
    rw [le_div_iff₀ hN]
    have : (1 : ℝ) / 2 ^ 127 * 2 ^ 128 = 2 := by norm_num
    nlinarith
  · -- `lsq ≥ 1/4`
    have h2 := (SInt.ble_iff _ _).1 hlsq2
    rw [SInt.toInt_false, SInt.nat_shiftLeft_eq, one_mul] at h2
    have h2' : ((2 ^ 126 : ℕ) : ℝ) ≤ ((E.lsq.v.toInt : ℤ) : ℝ) := by exact_mod_cast h2
    rw [Fx.val_def, le_div_iff₀ hN]
    push_cast at h2'
    have : (1 : ℝ) / 4 * 2 ^ 128 = 2 ^ 126 := by norm_num
    linarith
where
  abs_term {x : Fx 128} (h : Nat.ble x.v.mag (Nat.shiftLeft 1 131) = true) : |x.val| ≤ 8 := by
    have := Query.abs_val_le_of_mag (k := 3) (x := x) h
    norm_num at this
    exact this

end SandierSerfaty.Certificate.Box
