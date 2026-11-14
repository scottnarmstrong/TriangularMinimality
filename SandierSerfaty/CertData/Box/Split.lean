/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumCheckIdx

/-!
# Splitting the box checks into kernel shards

The Booleans of `Box.certificateGoal_of_checks` are whole-grid conjunctions (`outerGridB` contains the rows of
the outer grid, `a7B` all the A7 rectangles, `hessB` all the Hessian rows); one `decide +kernel` per Boolean is
far beyond the per-declaration budget (at most about 500 queries per declaration are
practical). This module splits them, with literal checkpoints proposed by the generator:

* `allFrom f a n` (`f a ∧ … ∧ f (a + n - 1)`) and `allLt_add`: blocks of rows;
* `outerSeg`, `negSeg`, `sumSeg`: the passes of `outerLoop`, `negLoop`, `sumLoop` over `n` cells ending in a
  literal accumulator `acc'` (structural equality `sEq`), and `outerLoop_of_seg`, `negLoop_of_seg`,
  `sumLoop_of_seg`: a row from its segments;
* `bothLoop`, `bothSeg`: the outer and negative-part passes of one row of a common grid with each value
  computed once, and `bothLoop_sound`, `bothSeg_sound`: the two passes from them;
* `hessSeg`, `rowAux_of_seg`: the same for the Hessian rows (`HessData.rowAuxG`, interval accumulator), for any
  context function (the scanning `H.ctx` or the checked-index `H.ctxI ix`);
* `outerPre`, `negPre`, `kPre`, `a7Pre`, `hessPre`: the conjuncts of `outerGridB`, `negGridB`, `kRowB`, `a7B`,
  `hessB` other than the rows, and `outerGridB_of`, …, `hessB_of`, `a7BI_of`, `hessBI_of` (the checked-index
  `a7BI`, `hessBI` of `Box.NumCheckIdx`).

No new mathematics: every statement is about the Boolean definitions only. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query

/-- Structural equality of two sign-magnitude integers. -/
def sEq (a b : SInt) : Bool := and (cond a.isNeg b.isNeg (not b.isNeg)) (Nat.beq a.mag b.mag)

theorem eq_of_sEq {a b : SInt} (h : sEq a b = true) : a = b := by
  obtain ⟨an, am⟩ := a
  obtain ⟨bn, bm⟩ := b
  simp only [sEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h1, rfl⟩ := h
  cases an <;> cases bn <;> simp_all

/-- `f a ∧ f (a + 1) ∧ … ∧ f (a + n - 1)`. -/
def allFrom (f : Nat → Bool) (a : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ n => and (f a) (allFrom f (Nat.succ a) n)

theorem allLt_add {f : Nat → Bool} : ∀ {n m : Nat}, allLt f n = true → allFrom f n m = true →
    allLt f (n + m) = true
  | _, 0, h1, _ => h1
  | n, m + 1, h1, h2 => by
    simp only [allFrom, Bool.and_eq_true] at h2
    have h3 : allLt f (n + 1) = true := by simp only [allLt, Bool.and_eq_true]; exact ⟨h1, h2.1⟩
    have := allLt_add h3 h2.2
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

/-! ### Row segments with checkpoints -/

/-- The pass of `outerLoop` over the cells `k, …, k + n - 1` (testing the nodes `k, …, k + n - 1`), ending in the
accumulator `acc'`. -/
def outerSeg (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (thr : SInt) (inRow : Bool)
    (kl kr : Nat) : Nat → Nat → SInt → SInt → Bool
  | 0, _, acc, acc' => sEq acc acc'
  | Nat.succ n, k, acc, acc' =>
    and (and (nodeOK thr (skipB inRow kl kr k) acc) (Nat.ble (sm k) (sm (Nat.succ k))))
      (match midVal E idx dm sm k with
        | none => false
        | some v => outerSeg E idx dm sm thr inRow kl kr n (Nat.succ k)
            (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ v.v)) acc')

/-- The pass of `negLoop` over the cells `k, …, k + n - 1`, ending in the accumulator `acc'`. -/
def negSeg (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) : Nat → Nat → SInt → SInt → Bool
  | 0, _, acc, acc' => sEq acc acc'
  | Nat.succ n, k, acc, acc' =>
    and (Nat.ble (sm k) (sm (Nat.succ k)))
      (match midVal E idx dm sm k with
        | none => false
        | some v => negSeg E idx dm sm n (Nat.succ k) (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ (negPart v))) acc')

/-- The pass of `sumLoop` over the cells `k, …, k + n - 1`, ending in the accumulator `acc'`. -/
def sumSeg (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) : Nat → Nat → SInt → SInt → Bool
  | 0, _, acc, acc' => sEq acc acc'
  | Nat.succ n, k, acc, acc' =>
    and (Nat.ble (sm k) (sm (Nat.succ k)))
      (match midVal E idx dm sm k with
        | none => false
        | some v => sumSeg E idx dm sm n (Nat.succ k) (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ v.v)) acc')

theorem outerLoop_of_seg {E : EvalData} {idx : Nat → Nat} {dm : Nat} {sm : Nat → Nat} {thr : SInt} {inRow : Bool}
    {kl kr m : Nat} : ∀ {n k : Nat} {acc acc' : SInt},
    outerSeg E idx dm sm thr inRow kl kr n k acc acc' = true →
    outerLoop E idx dm sm thr inRow kl kr m (k + n) acc' = true →
    outerLoop E idx dm sm thr inRow kl kr (n + m) k acc = true
  | 0, k, acc, acc', h1, h2 => by
    rw [eq_of_sEq h1]; simpa using h2
  | n + 1, k, acc, acc', h1, h2 => by
    rw [Nat.add_right_comm]
    simp only [outerSeg, outerLoop, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ?_⟩
    have h3 := h1.2
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at h3
    | some v =>
      simp only [hv] at h3 ⊢
      exact outerLoop_of_seg h3 (by rwa [show k + (n + 1) = k + 1 + n by omega] at h2)

theorem negLoop_of_seg {E : EvalData} {idx : Nat → Nat} {dm : Nat} {sm : Nat → Nat} {thr : SInt} {m : Nat} :
    ∀ {n k : Nat} {acc acc' : SInt}, negSeg E idx dm sm n k acc acc' = true →
    negLoop E idx dm sm thr m (k + n) acc' = true → negLoop E idx dm sm thr (n + m) k acc = true
  | 0, k, acc, acc', h1, h2 => by
    rw [eq_of_sEq h1]; simpa using h2
  | n + 1, k, acc, acc', h1, h2 => by
    rw [Nat.add_right_comm]
    simp only [negSeg, negLoop, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ?_⟩
    have h3 := h1.2
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at h3
    | some v =>
      simp only [hv] at h3 ⊢
      exact negLoop_of_seg h3 (by rwa [show k + (n + 1) = k + 1 + n by omega] at h2)

theorem sumLoop_of_seg {E : EvalData} {idx : Nat → Nat} {dm : Nat} {sm : Nat → Nat} {thr : SInt} {m : Nat} :
    ∀ {n k : Nat} {acc acc' : SInt}, sumSeg E idx dm sm n k acc acc' = true →
    sumLoop E idx dm sm thr m (k + n) acc' = true → sumLoop E idx dm sm thr (n + m) k acc = true
  | 0, k, acc, acc', h1, h2 => by
    rw [eq_of_sEq h1]; simpa using h2
  | n + 1, k, acc, acc', h1, h2 => by
    rw [Nat.add_right_comm]
    simp only [sumSeg, sumLoop, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ?_⟩
    have h3 := h1.2
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at h3
    | some v =>
      simp only [hv] at h3 ⊢
      exact sumLoop_of_seg h3 (by rwa [show k + (n + 1) = k + 1 + n by omega] at h2)

/-! ### Outer and negative-part rows together (one value per query) -/

/-- The outer and the negative-part pass over the cells `k, …, k + n - 1` of one row of a common grid, each value
computed once; at the end the outer node test and the negative threshold. -/
def bothLoop (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (thr : SInt) (inRow : Bool)
    (kl kr : Nat) (thrN : SInt) : Nat → Nat → SInt → SInt → Bool
  | 0, k, acc, accN => and (nodeOK thr (skipB inRow kl kr k) acc) (SInt.ble accN thrN)
  | Nat.succ n, k, acc, accN =>
    and (and (nodeOK thr (skipB inRow kl kr k) acc) (Nat.ble (sm k) (sm (Nat.succ k))))
      (match midVal E idx dm sm k with
        | none => false
        | some v => bothLoop E idx dm sm thr inRow kl kr thrN n (Nat.succ k)
            (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ v.v)) (SInt.add accN (SInt.mul ⟨false, widthM sm k⟩ (negPart v))))

/-- The two passes over the cells `k, …, k + n - 1`, ending in the accumulators `acc'`, `accN'`. -/
def bothSeg (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (thr : SInt) (inRow : Bool)
    (kl kr : Nat) : Nat → Nat → SInt → SInt → SInt → SInt → Bool
  | 0, _, acc, accN, acc', accN' => and (sEq acc acc') (sEq accN accN')
  | Nat.succ n, k, acc, accN, acc', accN' =>
    and (and (nodeOK thr (skipB inRow kl kr k) acc) (Nat.ble (sm k) (sm (Nat.succ k))))
      (match midVal E idx dm sm k with
        | none => false
        | some v => bothSeg E idx dm sm thr inRow kl kr n (Nat.succ k)
            (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ v.v)) (SInt.add accN (SInt.mul ⟨false, widthM sm k⟩ (negPart v)))
            acc' accN')

theorem bothLoop_sound {E : EvalData} {idx : Nat → Nat} {dm : Nat} {sm : Nat → Nat} {thr : SInt} {inRow : Bool}
    {kl kr : Nat} {thrN : SInt} : ∀ {n k : Nat} {acc accN : SInt},
    bothLoop E idx dm sm thr inRow kl kr thrN n k acc accN = true →
    outerLoop E idx dm sm thr inRow kl kr n k acc = true ∧ negLoop E idx dm sm thrN n k accN = true
  | 0, k, acc, accN, h => by
    simp only [bothLoop, Bool.and_eq_true] at h
    exact ⟨by simpa [outerLoop] using h.1, by simpa [negLoop] using h.2⟩
  | n + 1, k, acc, accN, h => by
    simp only [bothLoop, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at h3
    | some v =>
      simp only [hv] at h3
      obtain ⟨r1, r2⟩ := bothLoop_sound h3
      refine ⟨?_, ?_⟩
      · simp only [outerLoop, Bool.and_eq_true, hv]; exact ⟨⟨h1, h2⟩, r1⟩
      · simp only [negLoop, Bool.and_eq_true, hv]; exact ⟨h2, r2⟩

theorem bothSeg_sound {E : EvalData} {idx : Nat → Nat} {dm : Nat} {sm : Nat → Nat} {thr : SInt} {inRow : Bool}
    {kl kr : Nat} : ∀ {n k : Nat} {acc accN acc' accN' : SInt},
    bothSeg E idx dm sm thr inRow kl kr n k acc accN acc' accN' = true →
    outerSeg E idx dm sm thr inRow kl kr n k acc acc' = true ∧ negSeg E idx dm sm n k accN accN' = true
  | 0, k, acc, accN, acc', accN', h => by
    simp only [bothSeg, Bool.and_eq_true] at h
    exact ⟨by simpa [outerSeg] using h.1, by simpa [negSeg] using h.2⟩
  | n + 1, k, acc, accN, acc', accN', h => by
    simp only [bothSeg, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases hv : midVal E idx dm sm k with
    | none => simp [hv] at h3
    | some v =>
      simp only [hv] at h3
      obtain ⟨r1, r2⟩ := bothSeg_sound h3
      refine ⟨?_, ?_⟩
      · simp only [outerSeg, Bool.and_eq_true, hv]; exact ⟨⟨h1, h2⟩, r1⟩
      · simp only [negSeg, Bool.and_eq_true, hv]; exact ⟨h2, r2⟩

/-! ### Hessian row segments -/

/-- The pass of `HessData.rowAuxG H ctxf` over the cells `i, …, i + n - 1` of the row `a`, ending in the
accumulator `acc'` (for the scanning `H.ctx` or the checked-index `H.ctxI ix`). -/
def hessSeg (H : HessData) (ctxf : Nat → Nat → Option DCtx2) (a : Nat) : Nat → Nat → IV 128 → IV 128 → Bool
  | 0, _, acc, acc' => and (sEq acc.lo acc'.lo) (sEq acc.hi acc'.hi)
  | Nat.succ n, i, acc, acc' =>
    match ctxf a i with
    | none => false
    | some c =>
      and (and (Nat.ble (H.sp i) (H.sp (Nat.succ i)))
          (or (Nat.blt i H.jmin)
            (hessTest (IV.add acc (IV.mul (IV.ofNatPair 0 (widthN H.sp i)) (gddOf c))) (gdOf c.toDCtx)
              (gsOf c.toDCtx))))
        (hessSeg H ctxf a n (Nat.succ i)
          (IV.add acc (IV.mul (IV.ofNatPair (widthN H.sp i) (widthN H.sp i)) (gddOf c))) acc')

theorem rowAux_of_seg {H : HessData} {ctxf : Nat → Nat → Option DCtx2} {a m : Nat} :
    ∀ {n i : Nat} {acc acc' : IV 128}, hessSeg H ctxf a n i acc acc' = true →
    H.rowAuxG ctxf a m (i + n) acc' = true → H.rowAuxG ctxf a (n + m) i acc = true
  | 0, i, acc, acc', h1, h2 => by
    simp only [hessSeg, Bool.and_eq_true] at h1
    have e : acc = acc' := by
      obtain ⟨l, h⟩ := acc
      obtain ⟨l', h'⟩ := acc'
      have e1 : l = l' := eq_of_sEq h1.1
      have e2 : h = h' := eq_of_sEq h1.2
      rw [e1, e2]
    rw [e]; simpa using h2
  | n + 1, i, acc, acc', h1, h2 => by
    rw [Nat.add_right_comm]
    simp only [hessSeg, HessData.rowAuxG] at h1 ⊢
    cases hc : ctxf a i with
    | none => simp [hc] at h1
    | some c =>
      simp only [hc, Bool.and_eq_true] at h1 ⊢
      exact ⟨h1.1, rowAux_of_seg h1.2 (by rwa [show i + (n + 1) = i + 1 + n by omega] at h2)⟩

theorem row_of_rowAux {H : HessData} {ctxf : Nat → Nat → Option DCtx2} {a : Nat}
    (h1 : Nat.ble (H.dp a) (H.dp (Nat.succ a)) = true)
    (h2 : H.rowAuxG ctxf a H.nx 0 (IV.ofNatPair 0 0) = true) : H.rowG ctxf a = true := by
  simp only [HessData.rowG, Bool.and_eq_true]; exact ⟨h1, h2⟩

/-- Structural equality of two intervals. -/
def ivEq (a b : IV 128) : Bool := and (sEq a.lo b.lo) (sEq a.hi b.hi)

theorem eq_of_ivEq {a b : IV 128} (h : ivEq a b = true) : a = b := by
  obtain ⟨l, u⟩ := a
  obtain ⟨l', u'⟩ := b
  simp only [ivEq, Bool.and_eq_true] at h
  have e1 : l = l' := eq_of_sEq h.1
  have e2 : u = u' := eq_of_sEq h.2
  rw [e1, e2]

theorem allFrom_zero (f : Nat → Bool) (a : Nat) : allFrom f a 0 = true := by simp only [allFrom]

theorem allFrom_cons {f : Nat → Bool} {a n : Nat} (h1 : f a = true) (h2 : allFrom f (a + 1) n = true) :
    allFrom f a (n + 1) = true := by
  simp only [allFrom, Bool.and_eq_true]; exact ⟨h1, h2⟩

theorem allLt_zero (f : Nat → Bool) : allLt f 0 = true := by simp only [allLt]

theorem rowsG_eq_allLt (H : HessData) (ctxf : Nat → Nat → Option DCtx2) :
    ∀ n, H.rowsG ctxf n = allLt (H.rowG ctxf) n
  | 0 => rfl
  | n + 1 => by simp only [HessData.rowsG, allLt, rowsG_eq_allLt H ctxf n]

theorem rows_eq_allLt (H : HessData) (n : Nat) : H.rows n = allLt H.row n := rowsG_eq_allLt H H.ctx n

theorem rowsI_eq_allLt (H : HessData) (ix : Nat → Nat → Nat × Nat) (n : Nat) :
    H.rowsI ix n = allLt (H.rowI ix) n := rowsG_eq_allLt H (H.ctxI ix) n

theorem a7row_eq_allLt (D : A7Data) (j : Nat) : ∀ n, D.row j n = allLt (D.rect j) n
  | 0 => rfl
  | n + 1 => by simp only [A7Data.row, allLt, a7row_eq_allLt D j n]

theorem a7rowI_eq_allLt (D : A7Data) (ix : Nat → Nat → Nat × Nat) (j : Nat) :
    ∀ n, D.rowI ix j n = allLt (D.rectI ix j) n
  | 0 => rfl
  | n + 1 => by simp only [A7Data.rowI, allLt, a7rowI_eq_allLt D ix j n]

/-! ### The non-row conjuncts -/

/-- The conjuncts of `outerGridB` other than the rows. -/
def outerPre (A : A7Data) (G : OuterGrid) (par : NumFree) : Bool :=
  andL [Nat.ble (G.dm G.nd) (A.dp A.nj), Nat.ble (G.sm G.nx) (A.sp A.nk), monoB G.dm G.nd,
    geLitB (G.dm 0) 28209 100000, subLeB (G.dm 0) 28209 100000 par.oRho, stepB G.dm G.nd par.oDh,
    geLitB (G.dm G.nd) 697 1000, Nat.ble (G.dm G.nd) bigP, Nat.beq (G.sm 0) 0, monoB G.sm G.nx,
    stepB G.sm G.nx par.oSh, geLitB (G.sm G.nx) 65 100, Nat.blt 0 G.jl, Nat.ble G.jl G.nd, Nat.blt G.jr G.nd,
    Nat.blt 0 G.kl, Nat.ble G.kl G.nx, Nat.blt G.kr G.nx, geLitB (G.dm G.jl) 52528 100000,
    leLitB (G.dm G.jr) 54930 100000, geLitB (G.sm G.kl) 29420 100000, leLitB (G.sm G.kr) 32621 100000]

/-- The conjuncts of `negGridB` other than the rows. -/
def negPre (A : A7Data) (G : NegGrid) (par : NumFree) : Bool :=
  andL [Nat.ble (G.dm G.nd) (A.dp A.nj), Nat.ble (G.sm G.nx) (A.sp A.nk), monoB G.dm G.nd,
    geLitB (G.dm 0) 28209 100000, nearB (G.dm 0) 28209 100000 par.nDh, stepB G.dm G.nd par.nDh,
    geLitB (G.dm G.nd) 697 1000, Nat.ble (G.dm G.nd) bigP, Nat.beq (G.sm 0) 0, monoB G.sm G.nx,
    stepB G.sm G.nx par.nSh, geLitB (G.sm G.nx) 65 100]

/-- The conjuncts of `kRowB` other than the row. -/
def kPre (G : KGrid) (par : NumFree) : Bool :=
  andL [geLitB G.dm 28209 100000, leLitB G.dm 697 1000, Nat.beq (G.sm 0) 0,
    leLitB (G.sm G.nx) 65 100, stepB G.sm G.nx par.kSh, closeLoB G.dm par.kRd 12, closeHiB G.dm par.kRd 12,
    closeLoB (G.sm G.nx) par.kRx 108, closeHiB (G.sm G.nx) 0 108]

/-- The conjuncts of `a7B` other than the rectangles. -/
def a7Pre (A : A7Data) : Bool :=
  andL [Nat.blt 0 A.nj, Nat.blt 0 A.nk, leLitB (A.dp 0) 28209 100000, Nat.beq (A.sp 0) 0,
    geLitB (A.dp A.nj) 697 1000, geLitB (A.sp A.nk) 65 100]

/-- The conjuncts of `hessB` other than the rows. -/
def hessPre (H : HessData) : Bool :=
  andL [Nat.blt 0 H.nd, Nat.blt H.jmin H.nx, geLitB (H.dp 0) 28209 100000, Nat.beq (H.sp 0) 0,
    leLitB (H.dp 0) 52528 100000, geLitB (H.dp H.nd) 54930 100000, leLitB (H.sp H.jmin) 29420 100000,
    geLitB (H.sp H.nx) 32621 100000]

theorem outerGridB_of {A : A7Data} {G : OuterGrid} {E : EvalData} {par : NumFree} (h : outerPre A G par = true)
    (hr : allLt (fun j => G.row E j) (Nat.succ G.nd) = true) : outerGridB A G E par = true := by
  simp only [outerPre, outerGridB, andL, Bool.and_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hr⟩

theorem negGridB_of {A : A7Data} {G : NegGrid} {E : EvalData} {par : NumFree} (h : negPre A G par = true)
    (hr : allLt (fun j => G.row E j) (Nat.succ G.nd) = true) : negGridB A G E par = true := by
  simp only [negPre, negGridB, andL, Bool.and_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2, hr⟩

theorem kRowB_of {G : KGrid} {E : EvalData} {par : NumFree} (h : kPre G par = true) (hr : G.row E = true) :
    kRowB G E par = true := by
  simp only [kPre, kRowB, andL, Bool.and_true, Bool.and_eq_true] at h ⊢
  exact ⟨hr, h⟩

theorem a7B_of {A : A7Data} (h : a7Pre A = true) (hr : allLt (fun j => A.row j A.nk) A.nj = true) :
    a7B A = true := by
  simp only [a7Pre, a7B, andL, Bool.and_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hr, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem hessB_of {H : HessData} (h : hessPre H = true) (hr : allLt H.row H.nd = true) : hessB H = true := by
  simp only [hessPre, hessB, andL, Bool.and_true, Bool.and_eq_true, rows_eq_allLt] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hr, h.2.2.2.2⟩

theorem a7BI_of {A : A7Data} {ix : Nat → Nat → Nat × Nat} (h : a7Pre A = true)
    (hr : allLt (fun j => A.rowI ix j A.nk) A.nj = true) : a7BI A ix = true := by
  simp only [a7Pre, a7BI, andL, Bool.and_true, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hr, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem hessBI_of {H : HessData} {ix : Nat → Nat → Nat × Nat} (h : hessPre H = true)
    (hr : allLt (H.rowI ix) H.nd = true) : hessBI H ix = true := by
  simp only [hessPre, hessBI, andL, Bool.and_true, Bool.and_eq_true, rowsI_eq_allLt] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hr, h.2.2.2.2⟩

end SandierSerfaty.Certificate.Box
