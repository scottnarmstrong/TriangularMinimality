/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.HessDef
public import SandierSerfaty.Certificate.Box.CtxIdx

/-!
# The Hessian assertion A10 with the checked-index lookup

`HessData.ctxI H ix a i` is the context of the rectangle `D_a × S_i` read through the proposed index range
`ix a i = (i0, i1)` (`mkDCtx2I`); `HessData.rowI`, `HessData.rowsI` are the row checks of `Box.HessDef` (`rowG`,
`rowsG`) with this context function. The scanning checks `HessData.row`, `HessData.rows` are kept. Soundness:
`Box.HessIdxSound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query

/-- The context of the rectangle `D_a × S_i` with the proposed index range `ix a i`. -/
def HessData.ctxI (H : HessData) (ix : Nat → Nat → Nat × Nat) (a i : Nat) : Option DCtx2 :=
  match ix a i with
  | (i0, i1) =>
    mkDCtx2I H.T H.f0lI H.k0I H.lsqI H.lI H.lamI H.muI H.rad
      (IV.ofNatPair (H.dp a) (H.dp (Nat.succ a))) (IV.ofNatPair (H.sp i) (H.sp (Nat.succ i))) i0 i1

/-- **The check of the row `a`** with the checked-index lookup. -/
def HessData.rowI (H : HessData) (ix : Nat → Nat → Nat × Nat) (a : Nat) : Bool := H.rowG (H.ctxI ix) a

/-- The rows `0, …, n - 1` with the checked-index lookup. -/
def HessData.rowsI (H : HessData) (ix : Nat → Nat → Nat × Nat) (n : Nat) : Bool := H.rowsG (H.ctxI ix) n

end SandierSerfaty.Certificate.Box
