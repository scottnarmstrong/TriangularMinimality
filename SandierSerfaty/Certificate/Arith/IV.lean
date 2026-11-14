/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.SInt

/-!
# Exact-endpoint intervals for kernel evaluation

`IV P` is a closed interval `[lo / 2^P, hi / 2^P]` with sign-magnitude integer endpoints, the Lean analogue
of the C++ `IV` of the paper's verification code. A real `x`
lies in `I` when `I.lo ≤ x·2^P ≤ I.hi` (`IV.Mem`, in `SandierSerfaty.Certificate.Arith.IVLemmas`, with the
inclusion law of every operation). Addition, negation and scaling by powers of two are exact; products and
quotients round the lower endpoint down and the upper endpoint up; the product dispatches on the endpoint
signs (nine cases, two corner products each except the straddling case); square roots are proposed and
checked by squaring; comparisons are one-sided tests.

The definitions follow the kernel rules of `SandierSerfaty.Certificate.Arith.SInt` (direct `Nat` primitives,
`cond` branches, structural recursion only). This file has no Mathlib import.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Arith

/-- An interval `[lo / 2^P, hi / 2^P]` with sign-magnitude endpoints. -/
structure IV (P : Nat) where
  /-- The lower endpoint, scaled by `2 ^ P`. -/
  lo : SInt
  /-- The upper endpoint, scaled by `2 ^ P`. -/
  hi : SInt
deriving Inhabited, Repr

namespace IV

variable {P : Nat}

/-- The exact point `a / 2^P`. -/
def point (a : SInt) : IV P := ⟨a, a⟩

/-- The natural number `n` (exact). -/
def ofNat (n : Nat) : IV P := point ⟨false, Nat.shiftLeft n P⟩

/-- The rational `num / den` (`0 < den`), rounded outward to the grid `2^-P`. -/
def ofFrac (num : SInt) (den : Nat) : IV P :=
  ⟨SInt.fdiv (SInt.shiftLeft num P) den, SInt.cdiv (SInt.shiftLeft num P) den⟩

/-- Sum (exact). -/
def add (a b : IV P) : IV P := ⟨SInt.add a.lo b.lo, SInt.add a.hi b.hi⟩

/-- Negation (exact). -/
def neg (a : IV P) : IV P := ⟨SInt.neg a.hi, SInt.neg a.lo⟩

/-- Difference (exact). -/
def sub (a b : IV P) : IV P := ⟨SInt.sub a.lo b.hi, SInt.sub a.hi b.lo⟩

/-- Widening by `r / 2^P` on both sides (`[lo - r, hi + r]`). -/
def addRad (a : IV P) (r : Nat) : IV P :=
  ⟨SInt.sub a.lo ⟨false, r⟩, SInt.add a.hi ⟨false, r⟩⟩

/-- Multiplication by `2 ^ k` (exact). -/
def mulPow2 (a : IV P) (k : Nat) : IV P := ⟨SInt.shiftLeft a.lo k, SInt.shiftLeft a.hi k⟩

/-- Division by `2 ^ k`, rounded outward. -/
def divPow2 (a : IV P) (k : Nat) : IV P := ⟨SInt.fshift a.lo k, SInt.cshift a.hi k⟩

/-- Multiplication by a natural number (exact). -/
def mulNat (a : IV P) (n : Nat) : IV P := ⟨SInt.mulNat a.lo n, SInt.mulNat a.hi n⟩

/-- Division by a positive natural number, rounded outward. -/
def divNat (a : IV P) (n : Nat) : IV P := ⟨SInt.fdiv a.lo n, SInt.cdiv a.hi n⟩

/-- Rescaling of a pair of corner products `(L, H)` (scaled by `2^(2P)`) to an interval scaled by `2^P`. -/
def ofCorners (L H : SInt) : IV P := ⟨SInt.fshift L P, SInt.cshift H P⟩

/-- Product, dispatched on the endpoint signs. The sign bits classify each factor as nonnegative
(`lo.isNeg = false`), nonpositive (`hi.isNeg = true`) or straddling; in each of the nine cases the lower and
upper endpoints are the corner products that are extremal for that sign pattern, and only in the
straddle-straddle case are four products compared. -/
def mul (a b : IV P) : IV P :=
  cond a.lo.isNeg
    (cond a.hi.isNeg
      (cond b.lo.isNeg
        (cond b.hi.isNeg
          (ofCorners (SInt.mul a.hi b.hi) (SInt.mul a.lo b.lo))
          (ofCorners (SInt.mul a.lo b.hi) (SInt.mul a.lo b.lo)))
        (ofCorners (SInt.mul a.lo b.hi) (SInt.mul a.hi b.lo)))
      (cond b.lo.isNeg
        (cond b.hi.isNeg
          (ofCorners (SInt.mul a.hi b.lo) (SInt.mul a.lo b.lo))
          (ofCorners (SInt.min (SInt.mul a.lo b.hi) (SInt.mul a.hi b.lo))
            (SInt.max (SInt.mul a.lo b.lo) (SInt.mul a.hi b.hi))))
        (ofCorners (SInt.mul a.lo b.hi) (SInt.mul a.hi b.hi))))
    (cond b.lo.isNeg
      (cond b.hi.isNeg
        (ofCorners (SInt.mul a.hi b.lo) (SInt.mul a.lo b.hi))
        (ofCorners (SInt.mul a.hi b.lo) (SInt.mul a.hi b.hi)))
      (ofCorners (SInt.mul a.lo b.lo) (SInt.mul a.hi b.hi)))

/-- Square: `[0, max(lo², hi²)]` when the interval straddles `0`, exact corners otherwise. -/
def sq (a : IV P) : IV P :=
  cond a.lo.isNeg
    (cond a.hi.isNeg
      (ofCorners (SInt.mul a.hi a.hi) (SInt.mul a.lo a.lo))
      (ofCorners SInt.zero (SInt.max (SInt.mul a.lo a.lo) (SInt.mul a.hi a.hi))))
    (ofCorners (SInt.mul a.lo a.lo) (SInt.mul a.hi a.hi))

/-- Quotient by an interval with positive lower endpoint (`IV.mem_divPos` assumes `0 < b.lo`, which
`IV.posB` checks), dispatched on the sign of the numerator. -/
def divPos (a b : IV P) : IV P :=
  cond a.lo.isNeg
    (cond a.hi.isNeg
      ⟨SInt.fdiv (SInt.shiftLeft a.lo P) b.lo.mag, SInt.cdiv (SInt.shiftLeft a.hi P) b.hi.mag⟩
      ⟨SInt.fdiv (SInt.shiftLeft a.lo P) b.lo.mag, SInt.cdiv (SInt.shiftLeft a.hi P) b.lo.mag⟩)
    ⟨SInt.fdiv (SInt.shiftLeft a.lo P) b.hi.mag, SInt.cdiv (SInt.shiftLeft a.hi P) b.lo.mag⟩

/-- Reciprocal of an interval with positive lower endpoint: `[⌊2^(2P)/hi⌋, ⌈2^(2P)/lo⌉]`. -/
def invPos (b : IV P) : IV P :=
  ⟨⟨false, Nat.div (Nat.shiftLeft 1 (Nat.add P P)) b.hi.mag⟩,
    ⟨false, SInt.cdivNat (Nat.shiftLeft 1 (Nat.add P P)) b.lo.mag⟩⟩

/-- Convex hull. -/
def hull (a b : IV P) : IV P := ⟨SInt.min a.lo b.lo, SInt.max a.hi b.hi⟩

/-- `∀ x ∈ a, ∀ y ∈ b, x < y`. -/
def ltB (a b : IV P) : Bool := SInt.blt a.hi b.lo

/-- `∀ x ∈ a, ∀ y ∈ b, x ≤ y`. -/
def leB (a b : IV P) : Bool := SInt.ble a.hi b.lo

/-- `∀ x ∈ a, 0 < x`. -/
def posB (a : IV P) : Bool := SInt.pos a.lo

/-- `a ⊆ b`. -/
def subsetB (a b : IV P) : Bool := and (SInt.ble b.lo a.lo) (SInt.ble a.hi b.hi)

/-! ### Square roots, proposed and checked by squaring -/

/-- Newton iteration `x ↦ ⌊(x + ⌊n/x⌋)/2⌋` from `x`, stopped when it no longer decreases or after `fuel`
steps. It only proposes a root; nothing about it is proved (the check `sqrtCheck` is). -/
def isqrtNewton (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    cond (Nat.beq x 0) 0
      (cond (Nat.blt (Nat.shiftRight (Nat.add x (Nat.div n x)) 1) x)
        (isqrtNewton n fuel (Nat.shiftRight (Nat.add x (Nat.div n x)) 1)) x)

/-- A Newton seed `2^(⌊log₂ n⌋/2 + 1) ≥ √n`. -/
def isqrtSeed (n : Nat) : Nat := Nat.shiftLeft 1 (Nat.add (Nat.shiftRight (Nat.log2 n) 1) 1)

/-- A proposal for `⌊√n⌋` (Newton from `isqrtSeed`, at most 200 steps). -/
def isqrt (n : Nat) : Nat := isqrtNewton n 200 (isqrtSeed n)

/-- The check that `[l/2^P, h/2^P]` encloses `√x` for every `x ∈ a`: `a.hi ≥ 0` with `(a.hi·2^P) ≤ h²`, and
either `a.lo ≤ 0` with `l = 0` or `l² ≤ a.lo·2^P`. -/
def sqrtCheck (a : IV P) (l h : Nat) : Bool :=
  and (cond a.hi.isNeg (Nat.beq a.hi.mag 0) true)
    (and (Nat.ble (Nat.shiftLeft a.hi.mag P) (Nat.mul h h))
      (cond a.lo.isNeg (Nat.beq l 0) (Nat.ble (Nat.mul l l) (Nat.shiftLeft a.lo.mag P))))

/-- The interval `[l/2^P, h/2^P]` proposed for a square root. -/
def ofNatPair (l h : Nat) : IV P := ⟨⟨false, l⟩, ⟨false, h⟩⟩

/-- Proposed square-root endpoints of `a`: `⌊√(lo·2^P)⌋` (or `0`) and `⌊√(hi·2^P)⌋ + 1`. -/
def sqrtProposal (a : IV P) : Nat × Nat :=
  (cond a.lo.isNeg 0 (isqrt (Nat.shiftLeft a.lo.mag P)),
    Nat.add (isqrt (Nat.shiftLeft a.hi.mag P)) 1)

end IV

end SandierSerfaty.Certificate.Arith
