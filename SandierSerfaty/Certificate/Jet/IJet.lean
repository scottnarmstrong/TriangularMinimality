/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.Log

/-!
# Interval Taylor jets of order three for kernel evaluation

`IJet P` is the Lean analogue of the C++ jet `J` of the paper's verification code (`verification/core.hpp`,
struct `J` and its operators): four intervals `c0, c1, c2, c3`
that enclose, at every point `t` of a cell, the Taylor coefficients `F t`, `F' t`, `F'' t / 2`, `F''' t / 6`
of a real function `F` (the predicate `JetEncl` of `SandierSerfaty.Certificate.Jet.Encl`). Every coefficient
encloses the derivative over the whole cell, not at a centre.

Operations (each has a soundness law in `SandierSerfaty.Certificate.Jet.Encl`, `.Comp` or `.Poly`):

* constructors `const`, `var` (the identity on a cell);
* exact or outward-rounded arithmetic: `add`, `sub`, `neg`, `addIV`, `subIV`, `scale` (by an interval
  constant), `mul` (the truncated Cauchy product of `core.hpp`), `sq`, `pow`;
* composition `comp G A` with an outer jet `G` enclosing `g, g', g''/2, g'''/6` over the range of `A.c0`
  (the order-three Faà di Bruno formula), and the outer jets `invOuter`, `logOuter`, `sqrtOuter`, giving
  `invPos`, `divPos` (division by a positive jet), `log` (at `P = 128`, through `IV.logPos`) and `sqrtWith`
  (square root through the checked Newton proposal of `IV.sqrtProposal`, accepted only if `sqrtOK`);
* polynomials: `horner` (coefficients lowest degree first), the Taylor shift `tshift`, and `cpol`, which
  re-expands a polynomial about the midpoint of the cell before Horner evaluation, as the C++ `cpol`;
* `der`: the derivative, which returns an *order-two* jet `IJet2` (the third coefficient of the derivative is
  not known from an order-three jet; returning an order-two type rules out the use of that unknown coefficient by construction);
* `hull`, `subsetB` and the tests `posB`.

The C++ evaluates `inv`, `log` and `sqrt` of jets by coefficient recurrences; here they are compositions with
an outer jet (the same expressions after expanding the recurrences, written once in `comp`).

The definitions follow the kernel rules of `SandierSerfaty.Certificate.Arith.SInt` (direct `Nat` primitives,
`cond` branches, structural recursion only, no `let`). No Mathlib import.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Jet

open SandierSerfaty.Certificate.Arith

/-- The exact interval `[0, 0]`. -/
def ivZero {P : Nat} : IV P := ⟨⟨false, 0⟩, ⟨false, 0⟩⟩

/-- The exact interval `[1, 1]`. -/
def ivOne {P : Nat} : IV P := IV.ofNat 1

/-- The midpoint `⌊(lo + hi) / 2⌋ / 2^P` of an interval, as an exact point interval. -/
def ivMid {P : Nat} (a : IV P) : IV P := IV.point (SInt.fshift (SInt.add a.lo a.hi) 1)

/-- An interval Taylor jet of order three: `c0, c1, c2, c3` enclose `F, F', F''/2, F'''/6` on a cell. -/
structure IJet (P : Nat) where
  /-- The value. -/
  c0 : IV P
  /-- The first derivative. -/
  c1 : IV P
  /-- Half the second derivative. -/
  c2 : IV P
  /-- A sixth of the third derivative. -/
  c3 : IV P
deriving Inhabited, Repr

/-- An interval Taylor jet of order two: `c0, c1, c2` enclose `F, F', F''/2` on a cell. -/
structure IJet2 (P : Nat) where
  /-- The value. -/
  c0 : IV P
  /-- The first derivative. -/
  c1 : IV P
  /-- Half the second derivative. -/
  c2 : IV P
deriving Inhabited, Repr

namespace IJet

variable {P : Nat}

/-! ### Constructors and linear operations -/

/-- The constant jet of an interval constant. -/
def const (a : IV P) : IJet P := ⟨a, ivZero, ivZero, ivZero⟩

/-- The jet of the identity `t ↦ t` on the cell `x`. -/
def var (x : IV P) : IJet P := ⟨x, ivOne, ivZero, ivZero⟩

/-- Sum. -/
def add (a b : IJet P) : IJet P :=
  ⟨IV.add a.c0 b.c0, IV.add a.c1 b.c1, IV.add a.c2 b.c2, IV.add a.c3 b.c3⟩

/-- Difference. -/
def sub (a b : IJet P) : IJet P :=
  ⟨IV.sub a.c0 b.c0, IV.sub a.c1 b.c1, IV.sub a.c2 b.c2, IV.sub a.c3 b.c3⟩

/-- Negation. -/
def neg (a : IJet P) : IJet P := ⟨IV.neg a.c0, IV.neg a.c1, IV.neg a.c2, IV.neg a.c3⟩

/-- Adding an interval constant. -/
def addIV (a : IJet P) (c : IV P) : IJet P := ⟨IV.add a.c0 c, a.c1, a.c2, a.c3⟩

/-- Subtracting an interval constant. -/
def subIV (a : IJet P) (c : IV P) : IJet P := ⟨IV.sub a.c0 c, a.c1, a.c2, a.c3⟩

/-- Multiplication by an interval constant. -/
def scale (c : IV P) (a : IJet P) : IJet P :=
  ⟨IV.mul c a.c0, IV.mul c a.c1, IV.mul c a.c2, IV.mul c a.c3⟩

/-! ### Products -/

/-- Product: the Cauchy product of the Taylor coefficients, truncated at order three. -/
def mul (a b : IJet P) : IJet P :=
  ⟨IV.mul a.c0 b.c0,
    IV.add (IV.mul a.c0 b.c1) (IV.mul a.c1 b.c0),
    IV.add (IV.add (IV.mul a.c0 b.c2) (IV.mul a.c1 b.c1)) (IV.mul a.c2 b.c0),
    IV.add (IV.add (IV.mul a.c0 b.c3) (IV.mul a.c1 b.c2)) (IV.add (IV.mul a.c2 b.c1) (IV.mul a.c3 b.c0))⟩

/-- Square: `(a0², 2 a0 a1, 2 a0 a2 + a1², 2 a0 a3 + 2 a1 a2)` with `IV.sq` for the squares. -/
def sq (a : IJet P) : IJet P :=
  ⟨IV.sq a.c0,
    IV.mulPow2 (IV.mul a.c0 a.c1) 1,
    IV.add (IV.mulPow2 (IV.mul a.c0 a.c2) 1) (IV.sq a.c1),
    IV.mulPow2 (IV.add (IV.mul a.c0 a.c3) (IV.mul a.c1 a.c2)) 1⟩

/-- Natural power by repeated multiplication, `a ^ (n + 1) = a ^ n · a`. -/
def pow (a : IJet P) : Nat → IJet P
  | 0 => const ivOne
  | n + 1 => mul (pow a n) a

/-! ### Composition with an outer function -/

/-- Composition `g ∘ F`: `G` encloses `g, g', g''/2, g'''/6` over the range of `F` on the cell and `A` is the
jet of `F`. The coefficients are the order-three Faà di Bruno formula
`(g0, g1 a1, g1 a2 + g2 a1², g1 a3 + 2 g2 a1 a2 + g3 a1³)`. -/
def comp (G A : IJet P) : IJet P :=
  ⟨G.c0,
    IV.mul G.c1 A.c1,
    IV.add (IV.mul G.c1 A.c2) (IV.mul G.c2 (IV.sq A.c1)),
    IV.add (IV.add (IV.mul G.c1 A.c3) (IV.mulPow2 (IV.mul G.c2 (IV.mul A.c1 A.c2)) 1))
      (IV.mul G.c3 (IV.mul (IV.sq A.c1) A.c1))⟩

/-- The outer jet of `y ↦ 1/y` from an enclosure `h` of `1/y`: `(h, -h², h³, -h⁴)`. -/
def invOuterOf (h : IV P) : IJet P :=
  ⟨h, IV.neg (IV.sq h), IV.mul (IV.sq h) h, IV.neg (IV.sq (IV.sq h))⟩

/-- The outer jet of `y ↦ 1/y` over a positive interval `x` (`0 < x.lo`). -/
def invOuter (x : IV P) : IJet P := invOuterOf (IV.invPos x)

/-- Reciprocal of a positive jet (`0 < a.c0.lo`, checked by `posB`). -/
def invPos (a : IJet P) : IJet P := comp (invOuter a.c0) a

/-- Quotient by a positive jet (`0 < b.c0.lo`, checked by `posB`). -/
def divPos (a b : IJet P) : IJet P := mul a (invPos b)

/-- The outer jet of `y ↦ √y` from an enclosure `s` of `√y` with `0 < s.lo` (`k` encloses `1/√y`):
`(s, k/2, -k³/8, k⁵/16)`. -/
def sqrtOuterOf (s k : IV P) : IJet P :=
  ⟨s, IV.divPow2 k 1, IV.neg (IV.divPow2 (IV.mul (IV.sq k) k) 3),
    IV.divPow2 (IV.mul (IV.sq (IV.sq k)) k) 4⟩

/-- The outer jet of `y ↦ √y` from a checked enclosure `s` of `√y` (`0 < s.lo`). -/
def sqrtOuter (s : IV P) : IJet P := sqrtOuterOf s (IV.invPos s)

/-- Square root of a jet from proposed endpoints `l, h` of `√(a.c0)` (scaled by `2^P`); sound when `sqrtOK`. -/
def sqrtWith (a : IJet P) (l h : Nat) : IJet P := comp (sqrtOuter (IV.ofNatPair l h)) a

/-- The check accepting the proposal `l, h` for `sqrtWith`: `[l, h]/2^P` encloses `√y` for every `y ∈ a.c0`
(`IV.sqrtCheck`), and `0 < l`. -/
def sqrtOK (a : IJet P) (l h : Nat) : Bool := and (IV.sqrtCheck a.c0 l h) (Nat.blt 0 l)

/-- Square root of a jet with the Newton proposal of `IV.sqrtProposal`; sound when `sqrtB`. -/
def sqrt (a : IJet P) : IJet P := sqrtWith a (IV.sqrtProposal a.c0).1 (IV.sqrtProposal a.c0).2

/-- The check of `sqrt`: the Newton proposal passes `sqrtOK`. -/
def sqrtB (a : IJet P) : Bool := sqrtOK a (IV.sqrtProposal a.c0).1 (IV.sqrtProposal a.c0).2

/-- The outer jet of `log` from enclosures `L` of `log y` and `h` of `1/y`: `(L, h, -h²/2, h³/3)`. -/
def logOuterOf (L h : IV P) : IJet P :=
  ⟨L, h, IV.neg (IV.divNat (IV.sq h) 2), IV.divNat (IV.mul (IV.sq h) h) 3⟩

/-- The outer jet of `log` over a positive interval `x` (`0 < x.lo`), at `P = 128`. -/
def logOuter (x : IV 128) : IJet 128 := logOuterOf (IV.logPos x) (IV.invPos x)

/-- Logarithm of a positive jet (`0 < a.c0.lo`, checked by `posB`), at `P = 128`. -/
def log (a : IJet 128) : IJet 128 := comp (logOuter a.c0) a

/-! ### Polynomials -/

/-- Horner evaluation `c₀ + x (c₁ + x (c₂ + …))` of a polynomial with interval coefficients (lowest degree
first) at a jet. -/
def horner (x : IJet P) : List (IV P) → IJet P
  | [] => const ivZero
  | c :: cs => addIV (mul (horner x cs) x) c

/-- One step of the Taylor shift: from the coefficients `S` of `q(y + m)` and the constant `prev`, the
coefficients of `prev + (y + m) q(y + m)`: `prev + m S₀, S₀ + m S₁, …, S_{n-1}`. -/
def shiftAdd (m prev : IV P) : List (IV P) → List (IV P)
  | [] => [prev]
  | s :: ss => IV.add prev (IV.mul m s) :: shiftAdd m s ss

/-- The Taylor shift: the coefficients of `y ↦ p(y + m)` from those of `p` (lowest degree first). -/
def tshift (m : IV P) : List (IV P) → List (IV P)
  | [] => []
  | c :: cs => shiftAdd m c (tshift m cs)

/-- A polynomial at a jet, re-expanded about the midpoint `m` of the cell `x.c0` and evaluated by Horner at
`x - m` (the C++ `cpol`). -/
def cpol (cs : List (IV P)) (x : IJet P) : IJet P := horner (subIV x (ivMid x.c0)) (tshift (ivMid x.c0) cs)

/-! ### Derivative, hull, tests -/

/-- The derivative: the order-two jet `(c1, 2 c2, 3 c3)`. -/
def der (a : IJet P) : IJet2 P := ⟨a.c1, IV.mulNat a.c2 2, IV.mulNat a.c3 3⟩

/-- Truncation to order two. -/
def trunc (a : IJet P) : IJet2 P := ⟨a.c0, a.c1, a.c2⟩

/-- Coefficientwise convex hull. -/
def hull (a b : IJet P) : IJet P :=
  ⟨IV.hull a.c0 b.c0, IV.hull a.c1 b.c1, IV.hull a.c2 b.c2, IV.hull a.c3 b.c3⟩

/-- Coefficientwise inclusion `a ⊆ b`. -/
def subsetB (a b : IJet P) : Bool :=
  and (and (IV.subsetB a.c0 b.c0) (IV.subsetB a.c1 b.c1)) (and (IV.subsetB a.c2 b.c2) (IV.subsetB a.c3 b.c3))

/-- The value is positive on the cell (the side condition of `invPos`, `divPos`, `log`). -/
def posB (a : IJet P) : Bool := IV.posB a.c0

end IJet

namespace IJet2

variable {P : Nat}

/-- The constant order-two jet. -/
def const (a : IV P) : IJet2 P := ⟨a, ivZero, ivZero⟩

/-- Sum. -/
def add (a b : IJet2 P) : IJet2 P := ⟨IV.add a.c0 b.c0, IV.add a.c1 b.c1, IV.add a.c2 b.c2⟩

/-- Difference. -/
def sub (a b : IJet2 P) : IJet2 P := ⟨IV.sub a.c0 b.c0, IV.sub a.c1 b.c1, IV.sub a.c2 b.c2⟩

/-- Negation. -/
def neg (a : IJet2 P) : IJet2 P := ⟨IV.neg a.c0, IV.neg a.c1, IV.neg a.c2⟩

/-- Multiplication by an interval constant. -/
def scale (c : IV P) (a : IJet2 P) : IJet2 P := ⟨IV.mul c a.c0, IV.mul c a.c1, IV.mul c a.c2⟩

/-- Product, truncated at order two. -/
def mul (a b : IJet2 P) : IJet2 P :=
  ⟨IV.mul a.c0 b.c0,
    IV.add (IV.mul a.c0 b.c1) (IV.mul a.c1 b.c0),
    IV.add (IV.add (IV.mul a.c0 b.c2) (IV.mul a.c1 b.c1)) (IV.mul a.c2 b.c0)⟩

/-- Coefficientwise convex hull. -/
def hull (a b : IJet2 P) : IJet2 P := ⟨IV.hull a.c0 b.c0, IV.hull a.c1 b.c1, IV.hull a.c2 b.c2⟩

/-- Coefficientwise inclusion `a ⊆ b`. -/
def subsetB (a b : IJet2 P) : Bool :=
  and (IV.subsetB a.c0 b.c0) (and (IV.subsetB a.c1 b.c1) (IV.subsetB a.c2 b.c2))

end IJet2

end SandierSerfaty.Certificate.Jet
