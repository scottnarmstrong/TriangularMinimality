/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

/-!
# Sign-magnitude integers for kernel evaluation

`SInt` is an integer stored as a sign bit and a natural magnitude, `⟨isNeg, mag⟩ ↦ ±mag` (the two zeros
`⟨false, 0⟩` and `⟨true, 0⟩` both denote `0`). It is the endpoint and midpoint type of the certificate
arithmetic: the kernel accelerates `Nat` primitives with GMP but
not `Int`, so every operation here is written with `Nat` primitives and `Bool` case splits only.

## Kernel rules

The definitions of this file, and of every certificate module that evaluates in the kernel, follow the
kernel rules checked by `scripts/check_kernel_rules.py`:

* arithmetic calls the `Nat` primitives by name (`Nat.add`, `Nat.mul`, `Nat.shiftRight`, `Nat.ble`, ...),
  never the notation `+`, `*`, `>>>`, `≤`: the notation unfolds through `HAdd`/`instHAdd`/`instAddNat`
  before the kernel's GMP extension fires, which measured about 2.5× slower per primitive;
* branches are `cond` on a `Bool` (`Nat.ble`, `Nat.beq`, a sign bit), never `if` on a `Prop` with a
  `Decidable` instance, and never `Int` arithmetic, `Int` powers or `Nat.sqrt` (well-founded);
* no well-founded recursion; recursion is structural on a `Nat` fuel or depth argument.

Only the computational definitions live here (no Mathlib); their laws are in
`SandierSerfaty.Certificate.Arith.SIntLemmas`.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Arith

/-- A sign-magnitude integer: `⟨isNeg, mag⟩` denotes `-mag` if `isNeg` and `mag` otherwise. -/
structure SInt where
  /-- The sign bit (`true` for a nonpositive value). -/
  isNeg : Bool
  /-- The magnitude. -/
  mag : Nat
deriving Inhabited, Repr

namespace SInt

-- kernel-rules: exempt (specification only, never evaluated in a check)
/-- The integer denoted by a sign-magnitude integer. -/
def toInt (a : SInt) : Int := cond a.isNeg (Int.neg (Int.ofNat a.mag)) (Int.ofNat a.mag)

/-- The nonnegative integer `n`. -/
def ofNat (n : Nat) : SInt := ⟨false, n⟩

/-- Zero. -/
def zero : SInt := ⟨false, 0⟩

/-- Negation (exact). -/
def neg (a : SInt) : SInt := ⟨not a.isNeg, a.mag⟩

/-- Signed sum of magnitudes with opposite signs: `am` with sign `an` plus `bm` with sign `!an`. -/
def subMag (an : Bool) (am bm : Nat) : SInt :=
  cond (Nat.ble bm am) ⟨an, Nat.sub am bm⟩ ⟨not an, Nat.sub bm am⟩

/-- Addition (exact). -/
def add (a b : SInt) : SInt :=
  cond a.isNeg
    (cond b.isNeg ⟨true, Nat.add a.mag b.mag⟩ (subMag true a.mag b.mag))
    (cond b.isNeg (subMag false a.mag b.mag) ⟨false, Nat.add a.mag b.mag⟩)

/-- Subtraction (exact). -/
def sub (a b : SInt) : SInt := add a (neg b)

/-- The sign bit of a product. -/
def xorSign (an bn : Bool) : Bool := cond an (not bn) bn

/-- Multiplication (exact). -/
def mul (a b : SInt) : SInt := ⟨xorSign a.isNeg b.isNeg, Nat.mul a.mag b.mag⟩

/-- Multiplication by a natural number (exact). -/
def mulNat (a : SInt) (n : Nat) : SInt := ⟨a.isNeg, Nat.mul a.mag n⟩

/-- Multiplication by `2 ^ k` (exact). -/
def shiftLeft (a : SInt) (k : Nat) : SInt := ⟨a.isNeg, Nat.shiftLeft a.mag k⟩

/-- Ceiling division of naturals, `⌈m / d⌉` (for `0 < d`). -/
def cdivNat (m d : Nat) : Nat := Nat.div (Nat.sub (Nat.add m d) 1) d

/-- Floor division by a positive natural, `⌊a / d⌋`. -/
def fdiv (a : SInt) (d : Nat) : SInt :=
  cond a.isNeg ⟨true, cdivNat a.mag d⟩ ⟨false, Nat.div a.mag d⟩

/-- Ceiling division by a positive natural, `⌈a / d⌉`. -/
def cdiv (a : SInt) (d : Nat) : SInt :=
  cond a.isNeg ⟨true, Nat.div a.mag d⟩ ⟨false, cdivNat a.mag d⟩

/-- Ceiling of `m / 2 ^ k` for naturals. -/
def cshiftNat (m k : Nat) : Nat :=
  Nat.shiftRight (Nat.sub (Nat.add m (Nat.shiftLeft 1 k)) 1) k

/-- Floor of `a / 2 ^ k`. -/
def fshift (a : SInt) (k : Nat) : SInt :=
  cond a.isNeg ⟨true, cshiftNat a.mag k⟩ ⟨false, Nat.shiftRight a.mag k⟩

/-- Ceiling of `a / 2 ^ k`. -/
def cshift (a : SInt) (k : Nat) : SInt :=
  cond a.isNeg ⟨true, Nat.shiftRight a.mag k⟩ ⟨false, cshiftNat a.mag k⟩

/-- Truncation of `a / 2 ^ k` toward zero (the midpoint rounding of `Fx`; error below one unit). -/
def tshift (a : SInt) (k : Nat) : SInt := ⟨a.isNeg, Nat.shiftRight a.mag k⟩

/-- `a ≤ b`. -/
def ble (a b : SInt) : Bool :=
  cond a.isNeg
    (cond b.isNeg (Nat.ble b.mag a.mag) true)
    (cond b.isNeg (Nat.beq (Nat.add a.mag b.mag) 0) (Nat.ble a.mag b.mag))

/-- `a < b`. -/
def blt (a b : SInt) : Bool := not (ble b a)

/-- `0 ≤ a`. -/
def nonneg (a : SInt) : Bool := cond a.isNeg (Nat.beq a.mag 0) true

/-- `0 < a`. -/
def pos (a : SInt) : Bool := cond a.isNeg false (Nat.blt 0 a.mag)

/-- The smaller of two values. -/
def min (a b : SInt) : SInt := cond (ble a b) a b

/-- The larger of two values. -/
def max (a b : SInt) : SInt := cond (ble a b) b a

/-- Absolute value as a natural. -/
def natAbs (a : SInt) : Nat := a.mag

end SInt

end SandierSerfaty.Certificate.Arith
