/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumCheck
public import SandierSerfaty.Certificate.Query.Lam
public import SandierSerfaty.Certificate.Query.Const
public import SandierSerfaty.CertData.Box.Nodes

/-!
# The box-assertion data of the certificate: proposals (untrusted)

The data of `Box.certificateGoal_of_checks` (A7–A10, the `K` row, the query cells, the scalar side conditions),
proposed by natively compiled calls of the *same* definitions the kernel checks (`Box.Eval`, `Box.CtxDef`,
`Box.HessDef`, `Box.KRowDef`, `Box.NumCheck`, `Query.*`); nothing here is trusted and `native_decide` is not
involved. The few checks that live in Mathlib-importing modules (`Box.NumScalar`: `kcB`, `outThrB`, `negThrB`,
`deltaB`; `Box.EvalData`/`Box.Cert`: `evalHypCheck`, `evalCheckOf`, `cEnc`) are transcribed here as `…N`
for the dry run; the real definitions are run by the kernel on the emitted scalar module.

* query cells (`QCell`) from the table cells, with the global radii `rf`, `re` (`cellCheck`);
* the grids of the default mesh parameters (`Spec`): outer and negative-part grids (C++ `global_grid`), the A7
  rectangles (`bdsup`), the Hessian rows (`inside_hess`), the `K` row (`calcK`) at the dyadic node `⌊p 2^128⌋`;
* the cell-index proposals of every value query, the thresholds, the derivative bounds `L₁, …, L₄`;
* a fine *proposal* `λ̂` of `λ` (midpoint rule on cubic Hermite interpolants of the node data), used only as
  the evaluator constant `E.lam`; the certified enclosure `lamI` is an input (`lamEnc`, or a hypothetical width).
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-! ### Numbers -/

def NN : Nat := 2 ^ 128

def sintOfInt (z : Int) : SInt := if z < 0 then ⟨true, z.natAbs⟩ else ⟨false, z.toNat⟩

def fxOfInt (z : Int) : Fx 128 := ⟨sintOfInt z⟩

/-- A point of an interval (the midpoint, rounded down). -/
def midS (I : IV 128) : SInt := sintOfInt ((I.lo.toInt + I.hi.toInt) / 2)

def midF (I : IV 128) : Fx 128 := ⟨midS I⟩

def ptIV (x : Fx 128) : IV 128 := IV.point x.v

def wdt (I : IV 128) : Nat := (SInt.sub I.hi I.lo).mag

def flS (a : SInt) : Float := Float.ofInt a.toInt / 2.0 ^ 128.0

def flI (z : Int) (sc : Nat := 128) : Float := Float.ofInt z / 2.0 ^ sc.toFloat

def flN (n : Nat) : Float := flI (Int.ofNat n)

def flQ (q : Rat) : Float := Float.ofInt q.num / q.den.toFloat

def floorQ (q : Rat) : Int := q.num / q.den

def ceilQ (q : Rat) : Int := -((-q.num) / q.den)

/-- The mantissa `⌊q 2^128⌋`, `⌈q 2^128⌉` (for `q ≥ 0`). -/
def mFl (q : Rat) : Nat := (floorQ (q * (NN : Rat))).toNat

def mCl (q : Rat) : Nat := (ceilQ (q * (NN : Rat))).toNat

def evenFl (m : Nat) : Nat := m - m % 2

def evenCl (m : Nat) : Nat := m + m % 2

def qd (n : Nat) : Rat := (n : Rat) / (NN : Rat)

def qInt (z : Int) (sc : Nat) : Rat := (z : Rat) / ((2 ^ sc : Nat) : Rat)

/-- The C++ `nsamp`: `⌈(b - a)/h⌉`, at least `1`. -/
def nsamp (a b h : Rat) : Nat := max 1 (ceilQ ((b - a) / h)).toNat

def bQ : Rat := 28209 / 100000
def dlQ : Rat := 52528 / 100000
def duQ : Rat := 54930 / 100000
def slQ : Rat := 29420 / 100000
def suQ : Rat := 32621 / 100000
def dTopQ : Rat := 697 / 1000
def sTopQ : Rat := 65 / 100

/-! ### Query cells -/

/-- The literal radius `⌈chanErr/2^257⌉` of one channel (`chanCheck` needs `chanErr ≤ 2 r 2^256`). -/
def chanR (v u c2 n0 n1 : IV 128) (f1 : Fx 128) : Nat := (chanErr v u c2 n0 n1 f1 + 2 ^ 257 - 1) / 2 ^ 257

/-- The query cell of the table cell `[v, u]`: the range `[v.hi, u.lo]`, expansion at `u.lo`, the node values at
`u` (midpoints of the node enclosures), and its two radii. -/
def mkQCell (v u : IV 128) (ct nt : Tup) : QCell × Nat × Nat :=
  let c : QCell := ⟨⟨v.hi⟩, ⟨u.lo⟩, ⟨u.lo⟩, midF nt.f0, midF nt.f1, midF nt.e0, midF nt.e1⟩
  (c, chanR v u ct.f2 nt.f0 nt.f1 c.f1, chanR v u ct.e2 nt.e0 nt.e1 c.e1)

structure QOut where
  cells : Array QCell
  rfs : Array Nat
  res : Array Nat
  rf : Nat
  re : Nat

def buildQ (nodes : Array (IV 128)) (cts nts : Array Tup) : QOut := Id.run do
  let mut cells := #[]
  let mut rfs := #[]
  let mut res := #[]
  for i in [0:cts.size] do
    let (c, a, b) := mkQCell nodes[i]! nodes[i + 1]! cts[i]! nts[i]!
    cells := cells.push c
    rfs := rfs.push a
    res := res.push b
  return ⟨cells, rfs, res, rfs.foldl max 0, res.foldl max 0⟩

/-- The first cell `i` with `t + 16 ≤ hi_i` (binary search; `cells.size` if none). -/
def searchHi (cells : Array QCell) (t : Fx 128) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo then lo
    else
      let mid := (lo + hi) / 2
      if Fx.ble (Fx.add t margin) cells[mid]!.hi then searchHi cells t fuel lo mid
      else searchHi cells t fuel (mid + 1) hi

/-- The cell proposed for the checked root `t` (`none` if `t` is in no range: a gap at a node). -/
def findCell (cells : Array QCell) (t : Fx 128) : Option Nat :=
  let i := searchHi cells t 64 0 cells.size
  if i < cells.size && inRange cells[i]! t then some i else none

/-- The cell index for the value query at `(dm, smid)` (`some 0` on the exterior, where it is not read). -/
def propose (E : EvalData) (cells : Array QCell) (dm smid : Nat) : Option Nat :=
  if Fx.ble E.lsq (t2Of (fxM dm) (fxM smid)) then some 0
  else findCell cells (Fx.ofSInt ⟨false, Fx.sqrtProposal (t2Of (fxM dm) (fxM smid))⟩)

/-! ### The fine proposal `λ̂` (not certified) -/

/-- The node index `i` with `t ∈ [a_i, a_{i+1}]` by node midpoints (binary search). -/
def nodeSearch (nm : Array Int) (t : Int) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if nm[mid]! ≤ t then nodeSearch nm t fuel mid hi else nodeSearch nm t fuel lo mid

def fxMul (a b : Fx 128) : Fx 128 := Fx.mul a b

/-- `a·m/n` (truncated toward zero). -/
def fxScale (a : Fx 128) (m n : Nat) : Fx 128 := ⟨⟨a.v.isNeg, a.v.mag * m / n⟩⟩

/-- Cubic Hermite interpolation of `g` with `g'` on `[a, b]` at `t`. -/
def hermite (a b ga dga gb dgb t : Fx 128) : Fx 128 :=
  let h := Fx.sub b a
  let th := Fx.div (Fx.sub t a) h
  let th2 := fxMul th th
  let th3 := fxMul th2 th
  let h00 := Fx.add (Fx.sub (Fx.mulNat th3 2) (Fx.mulNat th2 3)) (Fx.ofNat 1)
  let h10 := Fx.add (Fx.sub th3 (Fx.mulNat th2 2)) th
  let h01 := Fx.sub (Fx.mulNat th2 3) (Fx.mulNat th3 2)
  let h11 := Fx.sub th3 th2
  Fx.add (Fx.add (fxMul h00 ga) (fxMul (fxMul h10 h) dga)) (Fx.add (fxMul h01 gb) (fxMul (fxMul h11 h) dgb))

/-- `λ̂ = (1/M) ∑ Φ(s_i)`, `s_i = x₀ (i + 1/2)/M`, `Φ = f₀'/t - s² e'/(p² t)` with Hermite interpolants of `f₀'`,
`ẽ'` between the node tuples (`nts i` is at the node `i + 1`). -/
def lamHat (d : BasisData) (nodes : Array (IV 128)) (nts : Array Tup) (M : Nat) : Fx 128 := Id.run do
  let nm : Array Int := nodes.map fun v => (v.lo.toInt + v.hi.toInt) / 2
  let x0 := midF (IV.divPow2 d.r0 1)
  let p := midF d.p
  let p2 := fxMul p p
  let mut acc : Fx 128 := ⟨SInt.zero⟩
  for i in [0:M] do
    let s := fxScale x0 (2 * i + 1) (2 * M)
    let s2 := fxMul s s
    let T2 := Fx.add p2 s2
    let t : Fx 128 := Fx.ofSInt ⟨false, Fx.sqrtProposal T2⟩
    let k := nodeSearch nm t.v.toInt 64 0 nm.size
    -- the node tuples at `k` and `k + 1` (indices `k - 1`, `k` of `nts`)
    let A := nts[k - 1]!
    let B := nts[k]!
    let a : Fx 128 := ⟨sintOfInt nm[k]!⟩
    let b : Fx 128 := ⟨sintOfInt nm[k + 1]!⟩
    let g := hermite a b (midF A.f1) (midF A.f2) (midF B.f1) (midF B.f2) t
    let ge := hermite a b (midF A.e1) (midF A.e2) (midF B.e1) (midF B.e2) t
    let phi := Fx.sub (Fx.div g t) (Fx.div (fxMul s2 (Fx.div ge t)) p2)
    acc := Fx.add acc phi
  return fxScale acc 1 M

/-! ### Enclosures of the constants -/

/-- The enclosures of the primitives (`CertPrem`): `π`, `R₀`, `f₀(l)`, `f₀(R₀)`, `e(R₀)`, `B(l)`, `l²`, `l`. -/
structure Prims where
  piI : IV 128
  r0I : IV 128
  f0lI : IV 128
  f0RI : IV 128
  eRI : IV 128
  blI : IV 128
  lsqI : IV 128
  lI : IV 128
  rad : Nat
  /-- The node indices of `l` and `R₀` in `nts`. -/
  iL : Nat
  iR : Nat

def mkPrims (d : BasisData) (nts : Array Tup) (knot : List Nat) (rad : Nat) : Prims :=
  let n := nts.size
  let iR := knot.getD 3 0 - 1
  ⟨d.pi, d.r0, IV.addRad nts[n - 1]!.f0 rad, IV.addRad nts[iR]!.f0 rad, IV.addRad nts[iR]!.e0 rad,
    IV.addRad (basis d 5 (knotIV d 6)).bsum.c0 rad, IV.sq (knotIV d 6), knotIV d 6, rad, n - 1, iR⟩

/-- `cEnc` (`Box.Cert`, transcribed). -/
def cEncN (r0 f0l f0R eR lamI pi bl lsq : IV 128) : IV 128 :=
  IV.sub (fLEnc r0 f0l f0R eR lamI) (IV.mul (slopeEnc pi bl lamI) lsq)

def muOf (P : Prims) (lamI : IV 128) : IV 128 := muEnc P.r0I P.f0RI P.eRI lamI
def kapOf (P : Prims) (lamI : IV 128) : IV 128 := slopeEnc P.piI P.blI lamI
def ccOf (P : Prims) (lamI : IV 128) : IV 128 := cEncN P.r0I P.f0lI P.f0RI P.eRI lamI P.piI P.blI P.lsqI

/-- The evaluator data with the constants computed from the proposal `λ̂`. -/
def mkEval (Q : QOut) (P : Prims) (lamH : Fx 128) : EvalData :=
  ⟨⟨Q.cells.size, fun i => Q.cells[i]!⟩, lamH, midF (muOf P (ptIV lamH)), midF (kapOf P (ptIV lamH)),
    midF (ccOf P (ptIV lamH)), ⟨SInt.add P.lsqI.hi ⟨false, 2⟩⟩⟩

/-- `evalHypCheck` (`Box.EvalData`, transcribed). -/
def evalHypCheckN (E : EvalData) (lamI muI κI cI lsqI : IV 128) (rf re : Nat) : Bool :=
  and (and (and (and (SInt.ble lamI.lo E.lam.v) (SInt.ble E.lam.v lamI.hi))
            (and (SInt.ble muI.lo E.mu.v) (SInt.ble E.mu.v muI.hi)))
          (and (and (SInt.ble κI.lo E.kap.v) (SInt.ble E.kap.v κI.hi))
            (and (SInt.ble cI.lo E.cc.v) (SInt.ble E.cc.v cI.hi))))
    (and (and (and (Nat.ble E.lam.v.mag (Nat.shiftLeft 1 131)) (Nat.ble E.mu.v.mag (Nat.shiftLeft 1 131)))
          (Nat.ble (Nat.add (Nat.add rf re) (Nat.add (SInt.sub lamI.hi lamI.lo).mag (SInt.sub muI.hi muI.lo).mag))
            (Nat.shiftLeft 1 127)))
      (and (absLe cI (Nat.shiftLeft 1 128))
        (and (SInt.ble (SInt.add lsqI.hi ⟨false, 2⟩) E.lsq.v) (SInt.ble ⟨false, Nat.shiftLeft 1 126⟩ E.lsq.v))))

/-- `evalCheckOf` (`Box.Cert`, transcribed). -/
def evalCheckOfN (E : EvalData) (P : Prims) (lamI : IV 128) (rf re : Nat) : Bool :=
  evalHypCheckN E lamI (muOf P lamI) (kapOf P lamI) (ccOf P lamI) P.lsqI rf re

/-! ### The scalar checks (`Box.NumScalar`, transcribed in `Rat`) -/

def wq (I : IV 128) : Rat := ((SInt.sub I.hi I.lo).mag : Rat) / (NN : Rat)

/-- The two lower bounds of `δ` in `deltaB` (the value budget `deltaG`, the exterior budget `deltaExt`). -/
def deltaParts (rf re : Nat) (P : Prims) (lamI : IV 128) : Rat × Rat :=
  ((qd rf + qd re + 2 * (1 / 10 ^ 11) + wq (muOf P lamI) + wq lamI / 4) / (28209 / 100000) + 1 / 2 ^ 60,
    wq (kapOf P lamI) + 4 * wq (ccOf P lamI) + 1 / 2 ^ 100)

def kcLhs (L1 L2 L3 L4 : Nat) (thr : Int) (x shK rd rx : Nat) (δ : Rat) : Rat :=
  2 * ((thr : Rat) / 2 ^ 256 + δ * qd x + qd L4 * qd shK ^ 2 * qd x / 24 +
    (qd L2 * qd rx ^ 2 / 2 + qd L1 * qd rd * qd rx + 65 / 100 * qd L3 * qd rd ^ 2 / 2))

/-- `outThrB`: the left side minus `Kc` (the test is `Kc + outErr ≤ thr/2^256`). -/
def outErr (L1 L2 L3 L4 : Nat) (x sh dh rho : Nat) (δ : Rat) : Rat :=
  2 * qd L2 * qd sh ^ 2 / 8 + 2 * qd x * qd L3 * qd dh ^ 2 / 8 + 2 * qd x * qd L1 * qd rho +
    (qd L4 * qd sh ^ 2 / 12 + 2 * δ) * qd x

/-- `negThrB`: the test is `thr/2^256 + negErr + Kc ≤ 0`. -/
def negErr (L1 L2 : Nat) (x sh dh : Nat) (δ : Rat) : Rat :=
  (δ + qd L2 * qd sh / 4) * qd x + qd x * qd L1 * qd dh / 2

end CertGen.Box
