/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.IV

/-!
# The midpoint fixed point `Fx` for the hot loop

`Fx P` is a sign-magnitude integer `v` denoting `v / 2^P`, with no runtime radius (the value-G queries of the outer grid carry a proved static error
budget instead of intervals). Addition, negation, multiplication by naturals and by powers of two are exact;
the product and the quotient truncate toward zero and are within one ulp `2^-P` of the exact result; the
square root is proposed and checked (`sqrtCheck`). The error laws are in
`SandierSerfaty.Certificate.Arith.FxLemmas`, which also makes `Fx P` a lawful `CertArith` backend.

The definitions follow the kernel rules of `SandierSerfaty.Certificate.Arith.SInt`. No Mathlib import.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Arith

/-- A fixed-point number `v / 2^P` with a sign-magnitude mantissa. -/
structure Fx (P : Nat) where
  /-- The mantissa. -/
  v : SInt
deriving Inhabited, Repr

namespace Fx

variable {P : Nat}

/-- The exact value `v / 2^P`. -/
def ofSInt (v : SInt) : Fx P := ⟨v⟩

/-- The natural number `n` (exact). -/
def ofNat (n : Nat) : Fx P := ⟨⟨false, Nat.shiftLeft n P⟩⟩

-- kernel-rules: exempt (conversion of a literal parameter, outside hot loops)
/-- The integer `z` (exact). -/
def ofInt (z : Int) : Fx P :=
  ⟨⟨decide (z < 0), Nat.shiftLeft z.natAbs P⟩⟩

-- kernel-rules: exempt (conversion of a literal parameter, outside hot loops)
/-- The rational `q` rounded down to the grid `2^-P`. -/
def ofRatDown (q : Rat) : Fx P :=
  ⟨SInt.fdiv ⟨decide (q.num < 0), Nat.shiftLeft q.num.natAbs P⟩ q.den⟩

/-- Sum (exact). -/
def add (a b : Fx P) : Fx P := ⟨SInt.add a.v b.v⟩

/-- Negation (exact). -/
def neg (a : Fx P) : Fx P := ⟨SInt.neg a.v⟩

/-- Difference (exact). -/
def sub (a b : Fx P) : Fx P := ⟨SInt.sub a.v b.v⟩

/-- Absolute value (exact). -/
def abs (a : Fx P) : Fx P := ⟨⟨false, a.v.mag⟩⟩

/-- Product, truncated toward zero (error below one ulp). -/
def mul (a b : Fx P) : Fx P := ⟨SInt.tshift (SInt.mul a.v b.v) P⟩

/-- Multiplication by a natural number (exact). -/
def mulNat (a : Fx P) (n : Nat) : Fx P := ⟨SInt.mulNat a.v n⟩

/-- Division by `2^k`, truncated toward zero (error below one ulp). -/
def divPow2 (a : Fx P) (k : Nat) : Fx P := ⟨SInt.tshift a.v k⟩

/-- Quotient, truncated toward zero (error below one ulp; the law assumes a nonzero divisor). -/
def div (a b : Fx P) : Fx P :=
  ⟨⟨SInt.xorSign a.v.isNeg b.v.isNeg, Nat.div (Nat.shiftLeft a.v.mag P) b.v.mag⟩⟩

/-- `a ≤ b` (exact). -/
def ble (a b : Fx P) : Bool := SInt.ble a.v b.v

/-- `a < b` (exact). -/
def blt (a b : Fx P) : Bool := SInt.blt a.v b.v

/-- `a = b` (exact; the two zeros are equal). -/
def beq (a b : Fx P) : Bool := and (SInt.ble a.v b.v) (SInt.ble b.v a.v)

/-- The check that `s / 2^P` is within one ulp of `√(a)`: `a ≥ 0` and `s² ≤ a·2^(2P) < (s+1)²`. -/
def sqrtCheck (a : Fx P) (s : Nat) : Bool :=
  and (SInt.nonneg a.v)
    (and (Nat.ble (Nat.mul s s) (Nat.shiftLeft a.v.mag P))
      (Nat.blt (Nat.shiftLeft a.v.mag P) (Nat.mul (Nat.add s 1) (Nat.add s 1))))

/-- A proposal for `⌊√a·2^P⌋` (Newton from `IV.isqrtSeed`, unproved; `sqrtCheck` certifies it). -/
def sqrtProposal (a : Fx P) : Nat := IV.isqrt (Nat.shiftLeft a.v.mag P)

end Fx

end SandierSerfaty.Certificate.Arith
