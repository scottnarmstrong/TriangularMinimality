/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Lookup

/-!
# The checked-index interval lookup

`Query.lookup` scans *all* cells of the table for every derivative query. The checked-index lookup replaces the scan
by an index range `[i0, i1]` proposed by the untrusted generator and checked by the kernel with two node
comparisons:

* `coverOK T X i0 i1`: `i0 ≤ i1 < n`; **lower side** `i0 = 0` or `node_{i0}.hi ≤ X.lo` (so the real node `a_{i0}`
  is at most every `t ∈ X`; for `i0 = 0`, `a_0 = b` is at most every `t ≥ b`); **upper side** `i1 + 1 = n` or
  `X.hi < node_{i1+1}.lo` (so every `t ∈ X` lies *strictly* below the real node `a_{i1+1}`, or below `a_n = l`;
  the strict test puts `t` in a right cell `[a_i, a_{i+1})` with `i ≤ i1`, which the right derivative of `ẽ'` needs);
* `lookupIdx T X i0 i1`: the hull of the cells `i0, …, i1` if `coverOK` holds, else `none`.

The hull may be a proper subset of the cells met by `X` (the scan also takes the cells whose outward node range
touches `X`); the generator proposes the tightest range. A single index is the case `i0 = i1`; a query interval that
straddles a node needs a range. Soundness: `Query.LookupIdxSound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table

/-- The hull of the tuples of the cells `i, i + 1, …, i + k`. -/
def hullCells (T : ITable) (i : Nat) : Nat → Tup
  | 0 => T.cell i
  | Nat.succ k => hullTup (T.cell i) (hullCells T (Nat.succ i) k)

/-- The lower coverage test: `i0 = 0` or `node_{i0}.hi ≤ X.lo`. -/
def coverLo (T : ITable) (X : IV 128) (i0 : Nat) : Bool :=
  cond (Nat.beq i0 0) true (SInt.ble (T.node i0).hi X.lo)

/-- The upper coverage test: `i1 + 1 = n` or `X.hi < node_{i1+1}.lo`. -/
def coverHi (T : ITable) (X : IV 128) (i1 : Nat) : Bool :=
  cond (Nat.beq (Nat.succ i1) T.n) true (SInt.blt X.hi (T.node (Nat.succ i1)).lo)

/-- **The checks of the proposed index range** `[i0, i1]`. -/
def coverOK (T : ITable) (X : IV 128) (i0 i1 : Nat) : Bool :=
  cond (Nat.ble i0 i1) (cond (Nat.blt i1 T.n) (cond (coverLo T X i0) (coverHi T X i1) false) false) false

/-- **The checked-index lookup**: the hull of the cells `i0, …, i1` if they cover `X ∩ [b, l)`. -/
def lookupIdx (T : ITable) (X : IV 128) (i0 i1 : Nat) : Option Tup :=
  cond (coverOK T X i0 i1) (some (hullCells T i0 (Nat.sub i1 i0))) none

end SandierSerfaty.Certificate.Query
