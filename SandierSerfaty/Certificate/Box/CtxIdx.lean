/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxDef
public import SandierSerfaty.Certificate.Query.LookupIdx

/-!
# The derivative contexts with the checked-index lookup

The variants of `lookupX`, `mkChk2`, `mkDCtx2` and of the A7 rectangle check `A7Data.rect` (`Box.CtxDef`) that read
the table through the checked index range `[i0, i1]` (`Query.lookupIdx`) proposed per query by the untrusted
generator, instead of scanning every cell. The old definitions are kept.

* `lookupXI`: if the query interval `X` lies in `[l, ∞)` (`lI.hi ≤ X.lo`) the exterior tuple alone; otherwise the
  checked-index hull of the cells `i0..i1` (failing if the coverage check fails), joined with the exterior tuple if
  `X` reaches `l`;
* `mkChk2I`, `mkDCtx2I`: the context of a rectangle with the index range as arguments;
* `A7Data.rectI D ix j k`, `A7Data.rowI D ix j n`: the rectangle checks with `ix j k = (i0, i1)` the proposed range
  of the rectangle `(j, k)`.

Soundness: `Box.CtxIdxSound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query

/-- **The radial lookup with the exterior, with a checked index range**. -/
def lookupXI (T : ITable) (f0lI k0I lsqI lI X : IV 128) (i0 i1 : Nat) : Option Tup :=
  cond (SInt.ble lI.hi X.lo)
    (some (extTup f0lI k0I lsqI X))
    (match lookupIdx T X i0 i1 with
      | none => none
      | some c =>
        cond (SInt.ble lI.lo X.hi) (some (hullTup c (extTup f0lI k0I lsqI X))) (some c))

/-- `mkChk2` with the checked-index lookup. -/
def mkChk2I (T : ITable) (f0lI k0I lsqI lI lamI muI : IV 128) (rad : Nat) (Dd Ss t2 : IV 128) (lh : Nat × Nat)
    (i0 i1 : Nat) : Option DCtx2 :=
  cond (and (IV.posB Dd) (and (IV.sqrtCheck t2 lh.1 lh.2) (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2))))
    (match lookupXI T f0lI k0I lsqI lI (IV.ofNatPair lh.1 lh.2) i0 i1 with
      | none => none
      | some c => some (dctx2Of Dd Ss (IV.ofNatPair lh.1 lh.2) t2 lamI muI rad c))
    none

/-- **The context of a rectangle** `Dd × Ss` with the proposed index range `[i0, i1]` of its `t`-range. -/
def mkDCtx2I (T : ITable) (f0lI k0I lsqI lI lamI muI : IV 128) (rad : Nat) (Dd Ss : IV 128) (i0 i1 : Nat) :
    Option DCtx2 :=
  mkChk2I T f0lI k0I lsqI lI lamI muI rad Dd Ss (IV.add (IV.sq Dd) (IV.sq Ss))
    (IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss))) i0 i1

/-- The four bounds of a context. -/
def A7Data.test (D : A7Data) (o : Option DCtx2) : Bool :=
  match o with
  | none => false
  | some c => and (and (absLe (gdOf c.toDCtx) D.L1) (absLe (gsOf c.toDCtx) D.L2))
      (and (absLe (gddOf c) D.L3) (absLe (gssOf c) D.L4))

/-- **The check of one rectangle** `[dp j, dp (j+1)] × [sp k, sp (k+1)]` with the index range `ix j k`. -/
def A7Data.rectI (D : A7Data) (ix : Nat → Nat → Nat × Nat) (j k : Nat) : Bool :=
  match ix j k with
  | (i0, i1) =>
    D.test (mkDCtx2I D.T D.f0lI D.k0I D.lsqI D.lI D.lamI D.muI D.rad
      (IV.ofNatPair (D.dp j) (D.dp (Nat.succ j))) (IV.ofNatPair (D.sp k) (D.sp (Nat.succ k))) i0 i1)

/-- The rectangles `(j, 0), …, (j, n - 1)`, checked with the index ranges `ix`. -/
def A7Data.rowI (D : A7Data) (ix : Nat → Nat → Nat × Nat) (j : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ k => and (A7Data.rowI D ix j k) (D.rectI ix j k)

end SandierSerfaty.Certificate.Box
