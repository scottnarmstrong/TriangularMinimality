/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Lookup
public import SandierSerfaty.Certificate.Basis.Eval

/-!
# The derivative-`G` queries on a rectangle (first derivatives, interval arithmetic)

paper `comp:rational-derivatives`, `comp:G-derivatives`: with `t = √(d² + s²)`,
`A = d/t²`, `Z = -s²/(d t²)`, `r_d = d/t`, `r_s = s/t`, `f' = f₀' - λ t`,

  `G_v = A_v f + A f' r_v + Z_v e + Z e' r_v`,   `A_d = (1 - 2d²/t²)/t²`, `Z_d = A_d + 1/d²`,
  `A_s = Z_s = -2ds/t⁴`.

`mkDCtx` builds, for a rectangle `Dd × Ss` of `(d, s)` (intervals), the enclosures `DCtx` of `t`, `t²`, `1/t`,
`1/t²` (as `(1/t)²`), `1/d`, and (from the table lookup hull of the cells meeting the checked enclosure `tI` of `t`, widened by
the infinite-mode error `rad`) of `f(t)`, `f'(t)`, `e(t)`, `e'(t)`; it checks that `t ∈ [b, l]` (against the
enclosures `bI ∋ b`, `lI ∋ l`), that `Dd` is positive and that the square root is correct. `gdOf`, `gsOf`
evaluate the two formulas. The exterior continuation (`t ≥ l`) and the second derivatives `G_dd`, `G_ss`
(`e''` is only piecewise defined) are not part of this module. Kernel rules: strict. Soundness:
`SandierSerfaty.Certificate.Query.DerivGSound`.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table

/-- The enclosures needed by the formulas of `G_d`, `G_s` on a rectangle. -/
structure DCtx where
  /-- `d`. -/
  d : IV 128
  /-- `s`. -/
  s : IV 128
  /-- `t = √(d² + s²)`. -/
  t : IV 128
  /-- `d² + s²`. -/
  t2 : IV 128
  /-- `1/t`. -/
  iT : IV 128
  /-- `1/t²`. -/
  iT2 : IV 128
  /-- `1/d`. -/
  iD : IV 128
  /-- `f(t) = f₀(t) - λ t²/2 - μ`. -/
  f : IV 128
  /-- `f'(t) = f₀'(t) - λ t`. -/
  f1 : IV 128
  /-- `e(t)`. -/
  e : IV 128
  /-- `e'(t)`. -/
  e1 : IV 128
deriving Inhabited

/-- The context from the rectangle, the checked root `tI` of `t2`, the constants and the lookup tuple. -/
def dctxOf (Dd Ss tI t2 lamI muI : IV 128) (rad : Nat) (c : Tup) : DCtx :=
  ⟨Dd, Ss, tI, t2, IV.invPos tI, IV.sq (IV.invPos tI), IV.invPos Dd,
    IV.sub (IV.sub (IV.addRad c.f0 rad) (IV.divPow2 (IV.mul lamI t2) 1)) muI,
    IV.sub (IV.addRad c.f1 rad) (IV.mul lamI tI), IV.addRad c.e0 rad, IV.addRad c.e1 rad⟩

/-- The checks (`Dd > 0`, `t² ∈` root, `tI > 0`, `b ≤ tI ≤ l`) and the lookup. -/
def mkChk (T : ITable) (bI lI lamI muI : IV 128) (rad : Nat) (Dd Ss t2 : IV 128) (lh : Nat × Nat) :
    Option DCtx :=
  cond (and (IV.posB Dd) (and (IV.sqrtCheck t2 lh.1 lh.2) (and (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2))
      (and (SInt.ble bI.hi (IV.ofNatPair (P := 128) lh.1 lh.2).lo)
        (SInt.ble (IV.ofNatPair (P := 128) lh.1 lh.2).hi lI.lo)))))
    (match lookup T (IV.ofNatPair lh.1 lh.2) with
      | none => none
      | some c => some (dctxOf Dd Ss (IV.ofNatPair lh.1 lh.2) t2 lamI muI rad c))
    none

/-- **The context of a rectangle** `Dd × Ss`. -/
def mkDCtx (T : ITable) (bI lI lamI muI : IV 128) (rad : Nat) (Dd Ss : IV 128) : Option DCtx :=
  mkChk T bI lI lamI muI rad Dd Ss (IV.add (IV.sq Dd) (IV.sq Ss))
    (IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss)))

/-- `A = d/t²`. -/
def aOf (c : DCtx) : IV 128 := IV.mul c.d c.iT2

/-- `A_d = (1 - 2d²/t²)/t²`. -/
def adOf (c : DCtx) : IV 128 :=
  IV.mul (IV.sub (IV.ofNat 1) (IV.mulNat (IV.mul (IV.sq c.d) c.iT2) 2)) c.iT2

/-- `Z_d = A_d + 1/d²`. -/
def zdOf (c : DCtx) : IV 128 := IV.add (adOf c) (IV.sq c.iD)

/-- `Z = -s²/(d t²)`. -/
def zOf (c : DCtx) : IV 128 := IV.neg (IV.mul (IV.sq c.s) (IV.mul c.iD c.iT2))

/-- `A_s = Z_s = -2ds/t⁴`. -/
def asOf (c : DCtx) : IV 128 := IV.neg (IV.mulNat (IV.mul (IV.mul c.d c.s) (IV.sq c.iT2)) 2)

/-- `r_d = d/t`. -/
def rdOf (c : DCtx) : IV 128 := IV.mul c.d c.iT

/-- `r_s = s/t`. -/
def rsOf (c : DCtx) : IV 128 := IV.mul c.s c.iT

/-- **`G_d`** on the rectangle: `A_d f + A f' r_d + Z_d e + Z e' r_d`. -/
def gdOf (c : DCtx) : IV 128 :=
  IV.add (IV.add (IV.mul (adOf c) c.f) (IV.mul (IV.mul (aOf c) c.f1) (rdOf c)))
    (IV.add (IV.mul (zdOf c) c.e) (IV.mul (IV.mul (zOf c) c.e1) (rdOf c)))

/-- **`G_s`** on the rectangle: `A_s f + A f' r_s + A_s e + Z e' r_s`. -/
def gsOf (c : DCtx) : IV 128 :=
  IV.add (IV.add (IV.mul (asOf c) c.f) (IV.mul (IV.mul (aOf c) c.f1) (rsOf c)))
    (IV.add (IV.mul (asOf c) c.e) (IV.mul (IV.mul (zOf c) c.e1) (rsOf c)))

end SandierSerfaty.Certificate.Query
