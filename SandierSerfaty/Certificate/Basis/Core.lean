/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Eval

/-!
# The finite-core test (assertion A2, evaluator)

paper `tail:finite-core-premise`, §7.2, the C++ `core_test`
(`verification/core.hpp`): on cells covering each segment `[κ_j, κ_{j+1}]` of `[b, l]`,

  `|B̃₁|_{2,t} < 6000`  and  `∑_{i ≤ 38} (k_i + 1)³ |D̃_i|_{3,t} < 2·10⁶`,

with `|F|_{n,t} = ∑_{q ≤ n} |F^{(q)}(t)|/q!` on the pieces of the segment. The jet of `B̃₁ = B̃' + 1/t` is the
derivative of the jet of `B̃ + log t` (`b1Jet`); the norms are bounded by the magnitudes of the interval
endpoints (`magHi`, scaled by `2^128`), compared with literal bounds.

* `coreCellCheck d j X`: the cell `X` is positive and nondegenerate and passes both bounds on segment `j`;
* `coverB a b cells`: the cells cover `[a, b]/2^128` (consecutive cells overlap or abut; untrusted cells,
  checked by comparisons only);
* `knotIV d j`: an enclosure of the knot `κ_j` from the basis constants;
* `coreSegCheck d j cells`: the cells cover `[κ_j, κ_{j+1}]` and each passes `coreCellCheck`.

Soundness: `SandierSerfaty.Certificate.Basis.CoreSound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet

/-- `max (|lo|, |hi|)`: every `x` in the interval has `|x| 2^P ≤ magHi`. -/
def magHi {P : Nat} (a : IV P) : Nat := cond (Nat.ble a.lo.mag a.hi.mag) a.hi.mag a.lo.mag

/-- `∑_{q ≤ 3} max |c_q|` (scaled by `2^P`). -/
def norm3 {P : Nat} (J : IJet P) : Nat :=
  Nat.add (Nat.add (magHi J.c0) (magHi J.c1)) (Nat.add (magHi J.c2) (magHi J.c3))

/-- `∑_{q ≤ 2} max |c_q|` (scaled by `2^P`). -/
def norm2 {P : Nat} (J : IJet2 P) : Nat := Nat.add (Nat.add (magHi J.c0) (magHi J.c1)) (magHi J.c2)

/-- The order-two jet of `B̃₁ = (B̃ + log t)'`. -/
def b1Jet (out : BasisOut) (X : IV 128) : IJet2 128 := IJet.der (IJet.add out.bsum (IJet.log (IJet.var X)))

/-- `∑_i (k_i + 1)³ ∑_{q ≤ 3} max |c_q(D_i)|` (scaled by `2^128`). -/
def dsumLoop : List Nat → List (IJet 128) → Nat
  | k :: ks, D :: ds => Nat.add (Nat.mul (Nat.pow (Nat.add k 1) 3) (norm3 D)) (dsumLoop ks ds)
  | _, _ => 0

/-- The two bounds of the finite core on a computed basis. -/
def coreOutCheck (out : BasisOut) (X : IV 128) : Bool :=
  and (Nat.blt (norm2 (b1Jet out X)) (Nat.mul 6000 (Nat.shiftLeft 1 128)))
    (Nat.blt (dsumLoop out.ks out.ds) (Nat.mul 2000000 (Nat.shiftLeft 1 128)))

/-- **The core test of one cell** `X` of segment `j`: `X` positive and nondegenerate, both bounds. -/
def coreCellCheck (d : BasisData) (j : Nat) (X : IV 128) : Bool :=
  and (and (IV.posB X) (SInt.blt X.lo X.hi)) (coreOutCheck (basis d j X) X)

/-- The cells cover `[a, b]/2^P`: the first starts at or below `a`, and either reaches `b` or the rest covers
from its upper end. -/
def coverB {P : Nat} (a b : SInt) : List (IV P) → Bool
  | [] => false
  | X :: rest => and (SInt.ble X.lo a) (or (SInt.ble b X.hi) (coverB X.hi b rest))

/-- Every cell passes the core test. -/
def allCells (d : BasisData) (j : Nat) : List (IV 128) → Bool
  | [] => true
  | X :: rest => and (coreCellCheck d j X) (allCells d j rest)

/-- An enclosure of the knot `κ_j` (`b, p - c, p, R₀, R₀ + .001, R₀ + h_s, l`). -/
def knotIV (d : BasisData) (j : Nat) : IV 128 :=
  cond (Nat.beq j 0) (frac false 28209 100000)
    (cond (Nat.beq j 1) d.pc
      (cond (Nat.beq j 2) d.p
        (cond (Nat.beq j 3) d.r0
          (cond (Nat.beq j 4) d.r1
            (cond (Nat.beq j 5) (IV.add d.r0 (frac false 3 40)) (IV.add d.r0 (frac false 19 250)))))))

/-- **Assertion A2 on segment `j`**: the cells cover `[κ_j, κ_{j+1}]` and pass the core test. -/
def coreSegCheck (d : BasisData) (j : Nat) (cells : List (IV 128)) : Bool :=
  and (coverB (knotIV d j).lo (knotIV d (Nat.add j 1)).hi cells) (allCells d j cells)

end SandierSerfaty.Certificate.Basis
