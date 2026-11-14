/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumCheck
public import SandierSerfaty.Certificate.Box.HessIdx

/-!
# The A7 and Hessian checks with the checked-index lookup as Booleans

`a7BI A ix` and `hessBI H hix` are `Box.a7B` and `Box.hessB` with the rectangle rows `A7Data.rowI A ix` and the
Hessian rows `HessData.rowsI H hix` (the table read through the proposed index ranges `ix`, `hix`, untrusted data
checked by `Query.coverOK`) in place of the scanning rows `A7Data.row`, `HessData.rows`. The other conjuncts are
those of `a7B`, `hessB`, in the same order. Soundness: `Lambda.GoalIdx`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

/-- The A7 rectangles (checked index) cover the boxes and reach `d = .697`, `s = .65`. -/
def a7BI (A : A7Data) (ix : Nat → Nat → Nat × Nat) : Bool :=
  andL [Nat.blt 0 A.nj, Nat.blt 0 A.nk, leLitB (A.dp 0) 28209 100000, Nat.beq (A.sp 0) 0,
    allLt (fun j => A.rowI ix j A.nk) A.nj, geLitB (A.dp A.nj) 697 1000, geLitB (A.sp A.nk) 65 100]

/-- The Hessian rows (checked index). -/
def hessBI (H : HessData) (hix : Nat → Nat → Nat × Nat) : Bool :=
  andL [Nat.blt 0 H.nd, Nat.blt H.jmin H.nx, geLitB (H.dp 0) 28209 100000, Nat.beq (H.sp 0) 0, H.rowsI hix H.nd,
    leLitB (H.dp 0) 52528 100000, geLitB (H.dp H.nd) 54930 100000, leLitB (H.sp H.jmin) 29420 100000,
    geLitB (H.sp H.nx) 32621 100000]

end SandierSerfaty.Certificate.Box
