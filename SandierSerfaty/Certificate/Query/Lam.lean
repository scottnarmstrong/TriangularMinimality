/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Lookup
public import SandierSerfaty.Certificate.Basis.Eval

/-!
# An enclosure of `λ` by a rectangle rule with interval hulls (assertion A5, coarse)

`λ x₀ = ∫₀^{x₀} Φ(s) ds` with `Φ(s) = f₀'(t)/t - s² e'(t)/(p² t)`, `t = √(p² + s²)`
(`cal:stationarity`: the integral `∫₀^{x₀} (Φ - λ) ds` is the first-integral identity of the proof of
stationarity, `Calibration.integral_Aint_eq_zero`). `Φ` is continuous with no singularity.

On the subinterval `[s_j, s_{j+1}]`, `s_j = j x₀/N`, the evaluator encloses `s` by the hull of the two node
intervals, `t² = p² + s²`, `t` by a checked square root, `f₀'(t)` and `e'(t)` by the table lookup hull widened by
`rad` (the infinite-mode error, `Tails.uniform_error_of_finiteCore`), and `Φ` by interval arithmetic; the term is
`(x₀/N)·Φ_j`. Their sum divided by `x₀` encloses `λ`. The error is `O(1/N)` (the hull width of the derivative
data over a subinterval), enough for the signs `f(l) > 0`, `-π B(l) - λ/2 > 0` (`Query.Const`: about `0.05`
needed, `N ≈ 30`) but *not* the `10⁻⁶` the hot loop needs (that is the midpoint rule of paper `comp:lambda-derivatives`, a later
package). Kernel rules: strict. Soundness: `Query.LamSound`.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table

/-- `s_j = j x₀/N`. -/
def sNode (x0 : IV 128) (N j : Nat) : IV 128 := IV.divNat (IV.mulNat x0 j) N

/-- The enclosure of `s` on `[s_j, s_{j+1}]`. -/
def sHull (x0 : IV 128) (N j : Nat) : IV 128 := IV.hull (sNode x0 N j) (sNode x0 N (Nat.succ j))

/-- `Φ = f₀'/t - s² e'/(p² t)` on the enclosures `F1 ∋ f₀'`, `E1 ∋ e'`, `S2 ∋ s²`, `tI ∋ t`, `p2 ∋ p²`. -/
def phiOf (p2 S2 F1 E1 tI : IV 128) : IV 128 :=
  IV.sub (IV.mul F1 (IV.invPos tI)) (IV.divPos (IV.mul S2 (IV.mul E1 (IV.invPos tI))) p2)

/-- The term `(x₀/N) Φ_j` from the lookup tuple. -/
def termFrom (p2 x0 : IV 128) (N rad : Nat) (Xs tI : IV 128) : Option Tup → Option (IV 128)
  | none => none
  | some c => some (IV.mul (IV.divNat x0 N)
      (phiOf p2 (IV.sq Xs) (IV.addRad c.f1 rad) (IV.addRad c.e1 rad) tI))

/-- The term `j`, from the checked root `[l, h]` of `t²`. -/
def termChk (T : ITable) (p2 x0 : IV 128) (N rad : Nat) (Xs t2 : IV 128) (lh : Nat × Nat) :
    Option (IV 128) :=
  cond (and (IV.sqrtCheck t2 lh.1 lh.2) (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2)))
    (termFrom p2 x0 N rad Xs (IV.ofNatPair lh.1 lh.2) (lookup T (IV.ofNatPair lh.1 lh.2))) none

/-- The term `j` of the sum. -/
def phiTerm (T : ITable) (p2 x0 : IV 128) (N rad j : Nat) : Option (IV 128) :=
  termChk T p2 x0 N rad (sHull x0 N j) (IV.add p2 (IV.sq (sHull x0 N j)))
    (IV.sqrtProposal (IV.add p2 (IV.sq (sHull x0 N j))))

/-- The sum of the terms `0, …, k - 1`. -/
def phiSum (T : ITable) (p2 x0 : IV 128) (N rad : Nat) : Nat → Option (IV 128)
  | 0 => some (IV.ofNat 0)
  | Nat.succ k =>
    match phiSum T p2 x0 N rad k, phiTerm T p2 x0 N rad k with
    | some a, some b => some (IV.add a b)
    | _, _ => none

/-- Division of the sum by `x₀`. -/
def lamDiv (x0 : IV 128) : Option (IV 128) → Option (IV 128)
  | none => none
  | some S => cond (IV.posB x0) (some (IV.divPos S x0)) none

/-- **The coarse enclosure of `λ`** with `N` subintervals and widening `rad` (`≥ 10⁻¹¹·2^128`). -/
def lamEnc (T : ITable) (d : BasisData) (N rad : Nat) : Option (IV 128) :=
  lamDiv (IV.divPow2 d.r0 1) (phiSum T d.p2 (IV.divPow2 d.r0 1) N rad N)

end SandierSerfaty.Certificate.Query
