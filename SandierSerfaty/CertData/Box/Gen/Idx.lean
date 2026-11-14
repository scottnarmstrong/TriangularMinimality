/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumCheckIdx

/-!
# Index-range proposals of the checked-index lookup (untrusted)

For a rectangle `Dd × Ss` the context `Box.mkDCtx2I` reads the table at the `t`-range `X = [l, h]/2^128`, `(l, h) =
IV.sqrtProposal (Dd² + Ss²)`, through a proposed index range `[i0, i1]`, which the kernel checks
(`Query.coverOK`). `proposeIdx` gives the tightest range allowed by the check: `i0` the largest cell with
`node_{i0}.hi ≤ X.lo` (`0` if none), `i1` the smallest cell `≥ i0` with `i1 + 1 = n` or `X.hi < node_{i1+1}.lo`; on the
exterior (`lI.hi ≤ X.lo`) the range is not read and `(0, 0)` is proposed. `a7Ix`, `hessIx` are the proposals of the A7
rectangles and of the Hessian cells. Nothing here is trusted: a wrong range only makes a check fail.
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Certificate.Box

/-- The largest `i < hi` in `[lo, hi)` with `node_i.hi ≤ x`, assuming `node_lo.hi ≤ x` (binary search). -/
def findLoAux (T : ITable) (x : SInt) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if SInt.ble (T.node mid).hi x then findLoAux T x fuel mid hi else findLoAux T x fuel lo mid

/-- The largest cell `i < n` with `node_i.hi ≤ x` (`0` if none). -/
def findLo (T : ITable) (x : SInt) : Nat :=
  if SInt.ble (T.node 0).hi x then findLoAux T x 64 0 T.n else 0

/-- The smallest `i ∈ [lo, hi]` with `i + 1 = n` or `x < node_{i+1}.lo`, assuming it holds at `hi` (binary search). -/
def findHiAux (T : ITable) (x : SInt) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    if hi ≤ lo then hi
    else
      let mid := (lo + hi) / 2
      if mid + 1 == T.n || SInt.blt x (T.node (mid + 1)).lo then findHiAux T x fuel lo mid
      else findHiAux T x fuel (mid + 1) hi

/-- The smallest cell `i ≥ i0` with `i + 1 = n` or `x < node_{i+1}.lo`. -/
def findHi (T : ITable) (x : SInt) (i0 : Nat) : Nat := findHiAux T x 64 i0 (T.n - 1)

/-- The proposed index range for the `t`-range `X` (`(0, 0)` on the exterior, where the table is not read). -/
def proposeIdx (T : ITable) (lI X : IV 128) : Nat × Nat :=
  if SInt.ble lI.hi X.lo then (0, 0)
  else
    let i0 := findLo T X.lo
    (i0, findHi T X.hi i0)

/-- The `t`-range read by `mkDCtx2I` for the rectangle `Dd × Ss`. -/
def rectX (Dd Ss : IV 128) : IV 128 :=
  let lh := IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss))
  IV.ofNatPair lh.1 lh.2

/-- The proposal for the A7 rectangle `(j, k)`. -/
def a7Ix (A : A7Data) (j k : Nat) : Nat × Nat :=
  proposeIdx A.T A.lI (rectX (IV.ofNatPair (A.dp j) (A.dp (j + 1))) (IV.ofNatPair (A.sp k) (A.sp (k + 1))))

/-- The proposal for the Hessian cell `(a, i)`. -/
def hessIx (H : HessData) (a i : Nat) : Nat × Nat :=
  proposeIdx H.T H.lI (rectX (IV.ofNatPair (H.dp a) (H.dp (a + 1))) (IV.ofNatPair (H.sp i) (H.sp (i + 1))))

/-- The proposals of a whole grid, as arrays by row (for the emitter and to avoid recomputation). -/
def ixTable (nr nc : Nat) (f : Nat → Nat → Nat × Nat) : Array (Array (Nat × Nat)) :=
  (Array.range nr).map fun a => (Array.range nc).map fun i => f a i

end CertGen.Box
