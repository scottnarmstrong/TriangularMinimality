/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Eval
public import SandierSerfaty.Certificate.Basis.CoeffEval

/-!
# The interval constants of the basis, computed from `π`, `p`, `R₀` and the coefficients

`mkData piI pI rI cos` builds the `BasisData` of `SandierSerfaty.Certificate.Basis.Eval` from enclosures of
`π`, `p`, `R₀` and of the coefficients `c_1, …, c_38` (the A1 output), as the C++ `init_after_co` does:

* `p - c`, `p²`, `R₀ + .001`;
* `γ(R₀), γ'(R₀), γ''(R₀)` from the jet of `γ` on the (nondegenerate) cell `rI` of `R₀`;
* per mode `i` (exponent `k = 6i`): `s_i = (-1)^i c_i`, `T₀ = c_i p^k`, `T₁ = -k(k-1) T₀/p`,
  `T₂ = k(k-1)((k-2)(k-3) - 3) T₀/(6p²)`, the edge coefficients `c_i (-1)^j C(k, 2j) p^{k-2j}` (binomials by the
  exact recurrence `C(k, 2j+2) = C(k, 2j)(k-2j)(k-2j-1)/((2j+1)(2j+2))`), and `V_i(R₀), V_i'(R₀), V_i''(R₀)`
  from the jet of the edge polynomial on the cell `rI`.

`dataOK piI pI rI cos` checks the side conditions: `pI ∋ p` and `rI ∋ R₀` through fourth powers
(`p⁴ = 1/12`, `R₀⁴ = 4/27`), positivity, nondegeneracy of `rI`, and 38 coefficients. The validity theorem
`mkData_valid` is in `SandierSerfaty.Certificate.Basis.DataSound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet

/-- `(-1)^j x`. -/
def sgnIV (j : Nat) (x : IV 128) : IV 128 := cond (Nat.beq (Nat.mod j 2) 1) (IV.neg x) x

/-- The binomial step `C(k, 2j) ↦ C(k, 2j + 2)` (exact division). -/
def choose2Step (cb k j : Nat) : Nat :=
  Nat.div (Nat.mul (Nat.mul cb (Nat.sub k (Nat.mul 2 j))) (Nat.sub k (Nat.add (Nat.mul 2 j) 1)))
    (Nat.mul (Nat.add (Nat.mul 2 j) 1) (Nat.add (Nat.mul 2 j) 2))

/-- The edge coefficients `c (-1)^j C(k, 2j) p^{k-2j}` for `j, j + 1, …` (`cnt` of them), from
`cb = C(k, 2j)`. -/
def edgeAux (co pI : IV 128) (k : Nat) : Nat → Nat → Nat → List (IV 128)
  | _, _, 0 => []
  | j, cb, cnt + 1 =>
    IV.mul co (sgnIV j (IV.mul (IV.ofNat cb) (ivPow pI (Nat.sub k (Nat.mul 2 j))))) ::
      edgeAux co pI k (Nat.add j 1) (choose2Step cb k j) cnt

/-- The edge coefficients of a mode with exponent `k` and coefficient enclosure `co`. -/
def edgeList (co pI : IV 128) (k : Nat) : List (IV 128) :=
  edgeAux co pI k 0 1 (Nat.add (Nat.div k 2) 1)

/-- `z = t² - p²` on the cell `rI`. -/
def zAt (p2 rI : IV 128) : IJet 128 := IJet.subIV (IJet.sq (IJet.var rI)) p2

/-- A mode from its exponent `k`, `T₀`, the edge coefficients and the jet `VJ` of `V_i` on the cell of `R₀`. -/
def mkModeOf (pI p2 co : IV 128) (i k : Nat) (t0 : IV 128) (edge : List (IV 128)) (VJ : IJet 128) :
    ModeData :=
  ⟨k, sgnIV i co, t0, IV.neg (IV.divPos (IV.mulNat t0 (Nat.mul k (Nat.sub k 1))) pI),
    IV.divPos (IV.divNat (IV.mulNat t0
      (Nat.mul (Nat.mul k (Nat.sub k 1)) (Nat.sub (Nat.mul (Nat.sub k 2) (Nat.sub k 3)) 3))) 6) p2,
    edge, VJ.c0, VJ.c1, IV.mulNat VJ.c2 2⟩

/-- Mode `i` from the enclosure `co` of `c_i`, with the edge list passed explicitly. -/
def mkModeE (pI p2 rI co : IV 128) (i k : Nat) (edge : List (IV 128)) : ModeData :=
  mkModeOf pI p2 co i k (IV.mul co (ivPow pI k)) edge (IJet.horner (zAt p2 rI) edge)

/-- Mode `i` (exponent `k = 6i`). -/
def mkMode (pI p2 rI co : IV 128) (i : Nat) : ModeData :=
  mkModeE pI p2 rI co i (Nat.mul 6 i) (edgeList co pI (Nat.mul 6 i))

/-- The modes `i, i + 1, …` from the coefficient enclosures. -/
def modesFrom (pI p2 rI : IV 128) : Nat → List (IV 128) → List ModeData
  | _, [] => []
  | i, co :: cs => mkMode pI p2 rI co i :: modesFrom pI p2 rI (Nat.add i 1) cs

/-- The basis constants from the jet `G` of `γ` on the cell of `R₀`. -/
def mkDataG (piI pI rI : IV 128) (cos : List (IV 128)) (p2 : IV 128) (G : IJet 128) : BasisData :=
  ⟨piI, pI, IV.sub pI (frac false 3 50), p2, rI, IV.add rI (frac false 1 1000), G.c0, G.c1,
    IV.mulNat G.c2 2, modesFrom pI p2 rI 1 cos⟩

/-- **The basis constants** from enclosures of `π`, `p`, `R₀` and `c_1, …, c_38`. -/
def mkData (piI pI rI : IV 128) (cos : List (IV 128)) : BasisData :=
  mkDataG piI pI rI cos (IV.sq pI) (gammaPi piI (IJet.var rI))

/-- `x ∈ [lo, hi]/2^128` with `x⁴ = num/den` and `x ≥ 0`: `0 ≤ lo`, `den lo⁴ ≤ num 2^512 ≤ den hi⁴`. -/
def fourthRootOK (num den : Nat) (a : IV 128) : Bool :=
  and (and (cond a.lo.isNeg false true) (cond a.hi.isNeg false true))
    (and (Nat.ble (Nat.mul den (Nat.pow a.lo.mag 4)) (Nat.mul num (Nat.shiftLeft 1 512)))
      (Nat.ble (Nat.mul num (Nat.shiftLeft 1 512)) (Nat.mul den (Nat.pow a.hi.mag 4))))

/-- The side conditions of `mkData`: `pI ∋ p` (`p⁴ = 1/12`), `rI ∋ R₀` (`R₀⁴ = 4/27`), `rI` positive and
nondegenerate, `p²` positive, 38 coefficients. -/
def dataOK (pI rI : IV 128) (cos : List (IV 128)) : Bool :=
  and (and (fourthRootOK 1 12 pI) (fourthRootOK 4 27 rI))
    (and (and (IV.posB rI) (SInt.blt rI.lo rI.hi))
      (and (and (IV.posB pI) (IV.posB (IV.sq pI))) (Nat.beq cos.length 38)))

/-! ### Transfer to literal constants -/

/-- `a ⊆ b` elementwise for lists of equal length. -/
def subList : List (IV 128) → List (IV 128) → Bool
  | [], [] => true
  | a :: as, b :: bs => and (IV.subsetB a b) (subList as bs)
  | _, _ => false

/-- The constants of a mode are contained in those of `b` (same exponent). -/
def modeSubB (a b : ModeData) : Bool :=
  and (and (and (Nat.beq a.k b.k) (IV.subsetB a.sc b.sc)) (and (IV.subsetB a.t0 b.t0) (IV.subsetB a.t1 b.t1)))
    (and (and (IV.subsetB a.t2 b.t2) (subList a.edge b.edge))
      (and (IV.subsetB a.vr b.vr) (and (IV.subsetB a.va b.va) (IV.subsetB a.vb b.vb))))

/-- Elementwise `modeSubB`. -/
def modesSubB : List ModeData → List ModeData → Bool
  | [], [] => true
  | a :: as, b :: bs => and (modeSubB a b) (modesSubB as bs)
  | _, _ => false

/-- The constants of `a` are contained in those of `b`: a valid computed `a` makes the literal `b` valid
(`BasisData.Valid.of_subB`). -/
def dataSubB (a b : BasisData) : Bool :=
  and (and (and (IV.subsetB a.pi b.pi) (IV.subsetB a.p b.p)) (and (IV.subsetB a.pc b.pc) (IV.subsetB a.p2 b.p2)))
    (and (and (and (IV.subsetB a.r0 b.r0) (IV.subsetB a.r1 b.r1))
      (and (IV.subsetB a.g0 b.g0) (IV.subsetB a.g1 b.g1)))
      (and (IV.subsetB a.g2 b.g2) (modesSubB a.modes b.modes)))

end SandierSerfaty.Certificate.Basis
