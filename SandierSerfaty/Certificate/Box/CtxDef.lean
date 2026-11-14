/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.DerivG

/-!
# The derivative contexts with second derivatives and the exterior (A7, A10)

paper `comp:rational-derivatives`, `comp:G-derivatives`, `comp:global-derivative-bounds` (`comp:rational-derivatives`, `comp:G-derivatives`,
`comp:global-derivative-bounds`). `Query.DerivG` builds the enclosures of the first derivatives `G_d`, `G_s` on a
rectangle `Dd × Ss` whose `t`-range lies in the table `[b, l]`. This module extends it:

* the radial lookup `lookupX` adds the *exterior tuple* `extTup` (the exact `f₀(t) = f₀(l) + κ₀ (t² - l²)`,
  `κ₀ = -π B(l)`, `e ≡ 0` for `t ≥ l`, `tail:exterior-formula`) to the hull of the table cells when the query interval
  reaches `l`;
* `mkDCtx2` is the context of a rectangle: positivity of `Dd` and the checked square root of `d² + s²` (the point
  `d ≥ b` makes `t ≥ b`; no range check), the lookup and the enclosures of `f''`, `e''` (`DCtx2`);
* `gssOf`, `gddOf` evaluate the formulas `GssF`, `GddF` (`Box.SecondDeriv`) on the context.

Kernel rules: strict. Soundness: `Box.CtxSound`.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query

/-- The exterior tuple on `t ∈ X`, `t ≥ l`: `f₀ = f₀(l) + κ₀ (t² - l²)`, `f₀' = 2 κ₀ t`, `f₀'' = 2 κ₀`, `e ≡ 0`,
for enclosures `f0lI ∋ f₀(l)`, `k0I ∋ κ₀ = -π B(l)`, `lsqI ∋ l²`. -/
def extTup (f0lI k0I lsqI X : IV 128) : Tup :=
  ⟨IV.add f0lI (IV.mul k0I (IV.sub (IV.sq X) lsqI)), IV.mulNat (IV.mul k0I X) 2, IV.mulNat k0I 2, IV.ofNat 0,
    IV.ofNat 0, IV.ofNat 0⟩

/-- **The radial lookup with the exterior**: the hull of the table cells meeting `X`, joined with the exterior tuple
if `X` reaches `l` (`lI ∋ l`). -/
def lookupX (T : ITable) (f0lI k0I lsqI lI X : IV 128) : Option Tup :=
  cond (SInt.ble lI.lo X.hi)
    (match lookup T X with
      | none => some (extTup f0lI k0I lsqI X)
      | some c => some (hullTup c (extTup f0lI k0I lsqI X)))
    (lookup T X)

/-- The enclosures of a rectangle, with the second derivatives of the radial functions. -/
structure DCtx2 extends DCtx where
  /-- `f''(t) = f₀''(t) - λ`. -/
  f2 : IV 128
  /-- `e''(t)` (a right derivative of `e'`). -/
  e2 : IV 128
deriving Inhabited

/-- The context from the rectangle, the checked root `tI` of `t2`, the constants and the lookup tuple. -/
def dctx2Of (Dd Ss tI t2 lamI muI : IV 128) (rad : Nat) (c : Tup) : DCtx2 :=
  ⟨dctxOf Dd Ss tI t2 lamI muI rad c, IV.sub (IV.addRad c.f2 rad) lamI, IV.addRad c.e2 rad⟩

/-- The checks (`Dd > 0`, `t² ∈` root, `tI > 0`) and the lookup. -/
def mkChk2 (T : ITable) (f0lI k0I lsqI lI lamI muI : IV 128) (rad : Nat) (Dd Ss t2 : IV 128) (lh : Nat × Nat) :
    Option DCtx2 :=
  cond (and (IV.posB Dd) (and (IV.sqrtCheck t2 lh.1 lh.2) (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2))))
    (match lookupX T f0lI k0I lsqI lI (IV.ofNatPair lh.1 lh.2) with
      | none => none
      | some c => some (dctx2Of Dd Ss (IV.ofNatPair lh.1 lh.2) t2 lamI muI rad c))
    none

/-- **The context of a rectangle** `Dd × Ss` (for points with `d ≥ b`). -/
def mkDCtx2 (T : ITable) (f0lI k0I lsqI lI lamI muI : IV 128) (rad : Nat) (Dd Ss : IV 128) : Option DCtx2 :=
  mkChk2 T f0lI k0I lsqI lI lamI muI rad Dd Ss (IV.add (IV.sq Dd) (IV.sq Ss))
    (IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss)))

/-- `y² `. -/
def y2Of (c : DCtx2) : IV 128 := IV.sq c.iT2

/-- `y³`. -/
def y3Of (c : DCtx2) : IV 128 := IV.mul (IV.sq c.iT2) c.iT2

/-- `A_ss = -2 d y² + 8 d s² y³`. -/
def assOf (c : DCtx2) : IV 128 :=
  IV.add (IV.neg (IV.mulNat (IV.mul c.d (y2Of c)) 2))
    (IV.mulNat (IV.mul (IV.mul c.d (IV.sq c.s)) (y3Of c)) 8)

/-- `(1 - r²)/t` with `r = v/t`. -/
def rpOf (r iT : IV 128) : IV 128 := IV.mul (IV.sub (IV.ofNat 1) (IV.sq r)) iT

/-- **`G_ss`** on the rectangle (`comp:G-derivatives`). -/
def gssOf (c : DCtx2) : IV 128 :=
  IV.add
    (IV.add
      (IV.add
        (IV.add
          (IV.add (IV.mul (assOf c) c.f) (IV.mul (IV.mul (IV.mulNat (asOf c.toDCtx) 2) c.f1) (rsOf c.toDCtx)))
          (IV.mul (aOf c.toDCtx) (IV.add (IV.mul (IV.mul c.f2 (rsOf c.toDCtx)) (rsOf c.toDCtx))
            (IV.mul c.f1 (rpOf (rsOf c.toDCtx) c.iT)))))
        (IV.mul (assOf c) c.e))
      (IV.mul (IV.mul (IV.mulNat (asOf c.toDCtx) 2) c.e1) (rsOf c.toDCtx)))
    (IV.mul (zOf c.toDCtx) (IV.add (IV.mul (IV.mul c.e2 (rsOf c.toDCtx)) (rsOf c.toDCtx))
      (IV.mul c.e1 (rpOf (rsOf c.toDCtx) c.iT))))

/-- `A_dd = 2 d (d² - 3 s²) y³`. -/
def addOf (c : DCtx2) : IV 128 :=
  IV.mulNat (IV.mul (IV.mul c.d (IV.sub (IV.sq c.d) (IV.mulNat (IV.sq c.s) 3))) (y3Of c)) 2

/-- `Z_dd = A_dd - 2/d³`. -/
def zddOf (c : DCtx2) : IV 128 := IV.sub (addOf c) (IV.mulNat (IV.mul (IV.sq c.iD) c.iD) 2)

/-- **`G_dd`** on the rectangle (`comp:G-derivatives`). -/
def gddOf (c : DCtx2) : IV 128 :=
  IV.add
    (IV.add
      (IV.add
        (IV.add
          (IV.add (IV.mul (addOf c) c.f) (IV.mul (IV.mul (IV.mulNat (adOf c.toDCtx) 2) c.f1) (rdOf c.toDCtx)))
          (IV.mul (aOf c.toDCtx) (IV.add (IV.mul (IV.mul c.f2 (rdOf c.toDCtx)) (rdOf c.toDCtx))
            (IV.mul c.f1 (rpOf (rdOf c.toDCtx) c.iT)))))
        (IV.mul (zddOf c) c.e))
      (IV.mul (IV.mul (IV.mulNat (zdOf c.toDCtx) 2) c.e1) (rdOf c.toDCtx)))
    (IV.mul (zOf c.toDCtx) (IV.add (IV.mul (IV.mul c.e2 (rdOf c.toDCtx)) (rdOf c.toDCtx))
      (IV.mul c.e1 (rpOf (rdOf c.toDCtx) c.iT))))

/-- `|I| ≤ L/2^128`: the enclosure `I` lies in `[-L, L]` (`L` a magnitude, scaled by `2^128`). -/
def absLe (I : IV 128) (L : Nat) : Bool := and (SInt.ble ⟨true, L⟩ I.lo) (SInt.ble I.hi ⟨false, L⟩)

/-- The literal data of the derivative assertion A7: the table (interval form), the enclosures of the constants, the
partitions `dp`, `sp` (mantissas) of the `d` and `s` axes into `nj`, `nk` cells, and the bounds `L1, …, L4`
(mantissas, scaled by `2^128`) of `|G_d|, |G_s|, |G_dd|, |G_ss|`. -/
structure A7Data where
  /-- The table of cells. -/
  T : ITable
  /-- An enclosure of `f₀(l)`. -/
  f0lI : IV 128
  /-- An enclosure of `-π B(l)`. -/
  k0I : IV 128
  /-- An enclosure of `l²`. -/
  lsqI : IV 128
  /-- An enclosure of `l`. -/
  lI : IV 128
  /-- An enclosure of `λ`. -/
  lamI : IV 128
  /-- An enclosure of `μ`. -/
  muI : IV 128
  /-- The widening of the table cells (`≥ 10⁻¹¹ 2^128`). -/
  rad : Nat
  /-- The bound of `|G_d|`. -/
  L1 : Nat
  /-- The bound of `|G_s|`. -/
  L2 : Nat
  /-- The bound of `|G_dd|`. -/
  L3 : Nat
  /-- The bound of `|G_ss|`. -/
  L4 : Nat
  /-- The number of `d` cells. -/
  nj : Nat
  /-- The number of `s` cells. -/
  nk : Nat
  /-- The mantissas of the `d` partition. -/
  dp : Nat → Nat
  /-- The mantissas of the `s` partition. -/
  sp : Nat → Nat

/-- **The check of one rectangle** `[dp j, dp (j+1)] × [sp k, sp (k+1)]`. -/
def A7Data.rect (D : A7Data) (j k : Nat) : Bool :=
  match mkDCtx2 D.T D.f0lI D.k0I D.lsqI D.lI D.lamI D.muI D.rad
      (IV.ofNatPair (D.dp j) (D.dp (Nat.succ j))) (IV.ofNatPair (D.sp k) (D.sp (Nat.succ k))) with
  | none => false
  | some c => and (and (absLe (gdOf c.toDCtx) D.L1) (absLe (gsOf c.toDCtx) D.L2))
      (and (absLe (gddOf c) D.L3) (absLe (gssOf c) D.L4))

/-- The rectangles `(j, 0), …, (j, n - 1)`. -/
def A7Data.row (D : A7Data) (j : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ k => and (A7Data.row D j k) (D.rect j k)

end SandierSerfaty.Certificate.Box
