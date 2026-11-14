/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Table
public import SandierSerfaty.Certificate.Lambda.Eval

/-!
# The native dry run of the box assertions (untrusted)

`CertGen.Box.dryRun` builds every literal of `Box.certificateGoal_of_checks` that is not table data (the query
cells, the evaluator constants, the five grids, the thresholds, `NumFree`, `δ`, `Kc`), runs every Boolean check of
that theorem natively (`a7B`, `outerGridB`, `negGridB`, `kRowB`, `hessB` unchanged; the transcribed `evalCheckOf`,
`kcB`, `outThrB`, `negThrB`, `deltaB`; `cellCheck` on every query cell), and prints the margins per assertion, for
the certified `λ` enclosure (`lamEnc`, scenario A) and for hypothetical fine enclosures (scenario B).
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box SandierSerfaty.Certificate.Lambda

def intOfFloat (e : Float) : Int := if e < 0 then -Int.ofNat (-e).toUInt64.toNat else Int.ofNat e.toUInt64.toNat

/-- Scientific notation with four significant digits. -/
def sci (x : Float) : String :=
  if x == 0 then "0"
  else if x.isNaN || x.isInf then toString x
  else
    let e := Float.floor (Float.log10 x.abs)
    let m := Float.round (x / Float.pow 10 e * 1000) / 1000
    s!"{m}e{intOfFloat e}"

def timed {α : Type} (label : String) (act : Unit → IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← act ()
  IO.println s!"[{label}] {(← IO.monoMsNow) - t0} ms"
  return a

/-- The smallest `r ≤ 1000` with `p r` (`1001` if none). -/
def leastR (p : Nat → Bool) : Nat := ((List.range 1001).find? p).getD 1001

/-- The `K` row: `d` node `⌊p 2^128⌋`, the top `X` (the least even mantissa with `closeHiB X 0 108`, i.e.
`X ≥ x₀`) and the cell count `m = ⌈X/h⌉`. -/
def gridK (d : BasisData) (h : Rat) : Nat × Nat × Nat := Id.run do
  let x0 := (IV.divPow2 d.r0 1).lo.mag
  let mut X := evenCl x0
  while !closeHiB X 0 108 do X := X + 2
  return (d.p.lo.mag, X, nsamp 0 (qd X) h)

/-- Everything the emitter needs. -/
structure BoxOut where
  S : Spec
  Q : QOut
  P : Prims
  E : EvalData
  lamH : Fx 128
  lamI : IV 128
  gO : G3
  gN : G3
  rO : Array RowRes
  rN : Array RowRes
  dK : Nat
  XK : Nat
  mK : Nat
  rK : RowRes
  A : A7Data
  H : HessData
  par : NumFree
  δ : Rat
  Kc : Rat
  thrO : Int
  thrN : Int
  pass : Bool
  /-- `true`: `lamI` is the certified `lamFine` enclosure; `false`: a hypothetical placeholder or `lamEnc`. -/
  certLam : Bool
  /-- The parameters of `lamFine`. -/
  lamPar : LamPar


def dryRun (S : Spec) (d : BasisData) (nodes : Array (IV 128)) (cts nts : Array Tup) (knot : List Nat) :
    IO (Option BoxOut) := do
  IO.println s!"== box dry run: outer ({sci (flQ S.oD)}, {sci (flQ S.oS)}), neg ({sci (flQ S.nD)}, {sci (flQ S.nS)}), A7 {sci (flQ S.aH)}, Hessian ({sci (flQ S.hD)}, {sci (flQ S.hS)}), K {sci (flQ S.kH)}, threads {S.threads}"
  let rad := (2 ^ 128 + 10 ^ 11 - 1) / 10 ^ 11
  -- query cells
  let Q ← timed "query cells" fun _ => pure (buildQ nodes cts nts)
  let nQ := Q.cells.size
  let qOK := (List.range nQ).all fun i => cellCheck nodes[i]! nodes[i + 1]! cts[i]! nts[i]! Q.cells[i]! Q.rf Q.re
  IO.println s!"query cells: {nQ}, rf = {sci (flN Q.rf)}, re = {sci (flN Q.re)}, cellCheck on all cells: {qOK}"
  for j in [0:6] do
    let a := knot.getD j 0
    let b := knot.getD (j + 1) nQ
    IO.println s!"  segment {j} (cells {a}..{b}): max rf {sci (flN ((Q.rfs.extract a b).foldl max 0))}, max re {sci (flN ((Q.res.extract a b).foldl max 0))}"
  -- constants
  let P := mkPrims d nts knot rad
  let lamH ← timed "λ̂ (Hermite midpoint rule)" fun _ => pure (lamHat d nodes nts S.lamM)
  IO.println s!"λ̂ = {flS lamH.v} (mantissa {lamH.v.toInt})"
  let iT : ITable := ⟨cts.size, fun i => nodes[i]!, fun i => cts[i]!⟩
  let FL : FTable := ⟨iT, fun i => nts[i]!⟩
  let PL : LamPar := ⟨S.lamNq, S.lamNe, rad, 1, S.lamS0d⟩
  let lamL ← timed s!"lamFine Nq = {S.lamNq}, Ne = {S.lamNe}, s0 = 1/{S.lamS0d}" fun _ => pure (lamFine FL d PL)
  let lamA ← if S.withA then timed s!"lamEnc N = {S.lamN}" fun _ => pure (lamEnc iT d S.lamN rad) else pure none
  let scens : List (String × IV 128) := (match lamL with
    | some I => [(s!"L: lamFine Nq={S.lamNq} Ne={S.lamNe} s0=1/{S.lamS0d}", I)]
    | none => []) ++ (match lamA with
    | some I => if S.noA then [] else [(s!"A: lamEnc N={S.lamN}", I)]
    | none => []) ++ S.lamW.map fun w =>
      (s!"B: hypothetical λ̂ ± {sci (flQ w)}", ⟨SInt.sub lamH.v ⟨false, mCl w⟩, SInt.add lamH.v ⟨false, mCl w⟩⟩)
  match lamL with
  | some I =>
    IO.println s!"lamFine: [{flS I.lo}, {flS I.hi}], width {sci (flN (wdt I))}, λ̂ inside: {SInt.ble I.lo lamH.v && SInt.ble lamH.v I.hi}"
  | none => IO.println "lamFine FAILED (none)"
  if let some I := lamA then
    IO.println s!"lamEnc: [{flS I.lo}, {flS I.hi}], width {sci (flN (wdt I))}, λ̂ inside: {SInt.ble I.lo lamH.v && SInt.ble lamH.v I.hi}"
  -- the evaluator constant: the midpoint of the certified fine enclosure (else the proposal `λ̂`)
  let lamH : Fx 128 := match lamL with
    | some I => midF I
    | none => lamH
  let E := mkEval Q P lamH
  -- grids
  let gO := G3.of S.oD S.oS
  let gN := G3.of S.nD S.nS
  let (dO, sO, dN, sN) := (gO.dArr, gO.sArr, gN.dArr, gN.sArr)
  let same := gO == gN
  IO.println s!"outer grid {gO.nd + 1} rows × {gO.nx} cells (segments {gO.d1}/{gO.d2}/{gO.d3} × {gO.s1}/{gO.s2}/{gO.s3}); negative grid {gN.nd + 1} × {gN.nx}{if same then " (same grid)" else ""}"
  let (jl, jr, kl, kr) := (gO.d1, gO.d1 + gO.d2, gO.s1, gO.s1 + gO.s2)
  let skipO : Nat → Nat → Bool := fun j k => jl < j && j < jr && kl < k && k < kr
  let rO ← timed "outer rows (instrumented)" fun _ => pure (gridRows S.threads S.seg E Q.cells dO sO skipO)
  let rN ← if same then pure rO else
    timed "negative rows (instrumented)" fun _ => pure (gridRows S.threads S.seg E Q.cells dN sN fun _ _ => false)
  let badO := rO.foldl (· + ·.bad) 0
  let badN := rN.foldl (· + ·.bad) 0
  let thrO := rO.foldl (fun m r => min m r.minQ2) bigI
  let thrN := rN.foldl (fun m r => max m r.negN) (-bigI)
  let jO := (List.range rO.size).foldl (fun b j => if rO[j]!.minQ2 < rO[b]!.minQ2 then j else b) 0
  let jN := (List.range rN.size).foldl (fun b j => if rN[j]!.negN > rN[b]!.negN then j else b) 0
  IO.println s!"outer: failed queries {badO}, threshold min 2Q = {flI thrO 256} at row {jO} (d = {flN dO[jO]!}), node {rO[jO]!.minK} (s = {flN sO[rO[jO]!.minK]!})"
  IO.println s!"negative: failed queries {badN}, threshold max ∫ max(0,-G) = {sci (flI thrN 256)} at row {jN} (d = {flN dN[jN]!})"
  -- the K row
  let (dK, XK, mK) := gridK d S.kH
  let sK := (Array.range (mK + 1)).map (kS XK mK)
  let rK := rowRes S.seg E Q.cells dK sK fun _ => true
  IO.println s!"K row: d = {flN dK}, {mK} cells to X = {flN XK}, failed {rK.bad}, ∫ G = {flI rK.sumQ 256} (2∫G = {2 * flI rK.sumQ 256})"
  let G : OuterGrid := ⟨gO.nd, gO.nx, gridD3 gO.d1 gO.d2 gO.d3, gridS3 gO.s1 gO.s2 gO.s3,
    fun j k => (rO[j]!.idx)[k]!, jl, jr, kl, kr, sintOfInt thrO⟩
  let Gr : NegGrid := ⟨gN.nd, gN.nx, gridD3 gN.d1 gN.d2 gN.d3, gridS3 gN.s1 gN.s2 gN.s3,
    fun j k => (rN[j]!.idx)[k]!, sintOfInt thrN⟩
  let KG : KGrid := ⟨mK, dK, kS XK mK, fun k => rK.idx[k]!, sintOfInt rK.sumQ⟩
  let par : NumFree := ⟨maxStep sO, maxStep dO, leastR (subLeB dO[0]! 28209 100000), maxStep sN, maxStep dN,
    maxStep sK, leastR (fun r => closeLoB dK r 12 && closeHiB dK r 12), leastR (closeLoB XK · 108)⟩
  IO.println s!"NumFree: oSh {sci (flN par.oSh)}, oDh {sci (flN par.oDh)}, oRho {par.oRho} ulp, nSh {sci (flN par.nSh)}, nDh {sci (flN par.nDh)}, kSh {sci (flN par.kSh)}, kRd {par.kRd} ulp, kRx {par.kRx} ulp"
  -- A7 / Hessian partitions
  let (nj, nk) := a7Counts S.aH
  let (hnd, hm1, hm2) := hessCounts S.hD S.hS
  IO.println s!"A7 rectangles {nj} × {nk}; Hessian cells {hnd} × {hm1 + hm2} (tested from s cell {hm1})"
  let mut result : Option BoxOut := none
  let mut si := 0
  for (name, lamI) in scens do
    let isA := name.startsWith "L:"
    IO.println s!"-- scenario {name}: λ width {sci (flN (wdt lamI))}"
    let muI := muOf P lamI
    let k0I := IV.neg (IV.mul P.piI P.blI)
    let A0 : A7Data := ⟨iT, P.f0lI, k0I, P.lsqI, P.lI, lamI, muI, rad, 0, 0, 0, 0, nj, nk, a7D nj, a7S nk⟩
    let (Ls, badA) ← if S.skipDeriv then pure ((0, 0, 0, 0), 0) else
      timed "A7 rectangles (instrumented)" fun _ => pure ((parMap S.threads A0.nj (a7Row A0)).foldl
        (fun (m, b) (r, b') => ((max m.1 r.1, max m.2.1 r.2.1, max m.2.2.1 r.2.2.1, max m.2.2.2 r.2.2.2), b + b'))
        ((0, 0, 0, 0), 0))
    let A : A7Data := { A0 with L1 := Ls.1 + 1, L2 := Ls.2.1 + 1, L3 := Ls.2.2.1 + 1, L4 := Ls.2.2.2 + 1 }
    IO.println s!"A7: failed contexts {badA}; L1 {sci (flN A.L1)}, L2 {sci (flN A.L2)}, L3 {sci (flN A.L3)}, L4 {sci (flN A.L4)}"
    let H : HessData := ⟨iT, P.f0lI, k0I, P.lsqI, P.lI, lamI, muI, rad, hnd, hm1 + hm2, hm1, hessD hnd, hessS hm1 hm2⟩
    let hm ← if S.skipDeriv then pure ({} : HessMin) else
      timed "Hessian rows (instrumented)" fun _ => pure ((parMap S.threads H.nd (hessRow H)).foldl (fun a r =>
        { aLo := min a.aLo r.aLo, cLo := min a.cLo r.cLo, detLo := min a.detLo r.detLo, bad := a.bad + r.bad,
          fails := a.fails + r.fails }) {})
    IO.println s!"Hessian: failed contexts {hm.bad}, failed cells {hm.fails}; min inf A {sci (flI hm.aLo)}, min inf C {sci (flI hm.cLo)}, min inf (AC - B²) {sci (flI hm.detLo)}"
    let (δ1, δ2) := deltaParts Q.rf Q.re P lamI
    let δ := max δ1 δ2
    let hchk := evalCheckOfN E P lamI Q.rf Q.re
    let Kc := kcLhs A.L1 A.L2 A.L3 A.L4 rK.sumQ XK par.kSh par.kRd par.kRx δ
    let Kc0 := kcLhs A.L1 A.L2 A.L3 A.L4 rK.sumQ XK par.kSh par.kRd par.kRx 0
    let xO := G.sm G.nx
    let xN := Gr.sm Gr.nx
    let eO := outErr A.L1 A.L2 A.L3 A.L4 xO par.oSh par.oDh par.oRho δ
    let eN := negErr A.L1 A.L2 xN par.nSh par.nDh δ
    let mO := qInt thrO 256 - (Kc + eO)
    let mN := -(qInt thrN 256 + eN + Kc)
    let mO0 := qInt thrO 256 - (Kc0 + outErr A.L1 A.L2 A.L3 A.L4 xO par.oSh par.oDh par.oRho 0)
    let mN0 := -(qInt thrN 256 + negErr A.L1 A.L2 xN par.nSh par.nDh 0 + Kc0)
    let slopeO := 2 * qd XK + 2 * qd xO
    let slopeN := qd xN + 2 * qd XK
    IO.println s!"δ = max(δ_G {sci (flQ δ1)}, δ_ext {sci (flQ δ2)}) = {sci (flQ δ)}; (rf+re)/b = {sci (flQ ((qd Q.rf + qd Q.re) / bQ))}; evalCheckOf {hchk}"
    IO.println s!"Kc = {flQ Kc} (2∫G = {flQ (2 * qInt rK.sumQ 256)}); outer mesh terms {sci (flQ (eO - 2 * δ * qd xO))}, 2δx {sci (flQ (2 * δ * qd xO))}"
    IO.println s!"outer threshold margin {sci (flQ mO)} (at δ = 0: {sci (flQ mO0)}; passes iff δ ≤ {sci (flQ (mO0 / slopeO))})"
    IO.println s!"negative threshold margin {sci (flQ mN)} (at δ = 0: {sci (flQ mN0)}; passes iff δ ≤ {sci (flQ (mN0 / slopeN))})"
    -- the Boolean checks of `certificateGoal_of_checks`, run unchanged
    let bA ← if S.skipDeriv then pure false else timed "a7BI" fun _ => pure (a7BI A (a7Ix A))
    let bH ← if S.skipDeriv then pure false else timed "hessBI" fun _ => pure (hessBI H (hessIx H))
    let bO ← timed "outerGridB" fun _ => pure (outerGridB A G E par)
    let bN ← timed "negGridB" fun _ => pure (negGridB A Gr E par)
    let bK := kRowB KG E par
    let bkc := decide (kcLhs A.L1 A.L2 A.L3 A.L4 KG.thr.toInt (KG.sm KG.nx) par.kSh par.kRd par.kRx δ ≤ Kc)
    let bthr := decide (Kc + outErr A.L1 A.L2 A.L3 A.L4 xO par.oSh par.oDh par.oRho δ ≤ qInt G.thr.toInt 256)
    let bnthr := decide (qInt Gr.thr.toInt 256 + negErr A.L1 A.L2 xN par.nSh par.nDh δ + Kc ≤ 0)
    let bdel := decide (0 ≤ δ) && decide (δ1 ≤ δ) && decide (δ2 ≤ δ)
    let all := [("cellCheck (QRealizes)", qOK), ("evalCheckOf", hchk), ("a7BI", bA), ("outerGridB", bO),
      ("negGridB", bN), ("kRowB", bK), ("hessBI", bH), ("kcB", bkc), ("outThrB", bthr), ("negThrB", bnthr),
      ("deltaB", bdel)]
    IO.println ("checks: " ++ ", ".intercalate (all.map fun (n, b) => s!"{n} {b}"))
    let pass := all.all (·.2)
    IO.println s!"scenario {name}: {if pass then "ALL CHECKS PASS" else "FAILS"}"
    if si == S.emitScen then
      result := some ⟨S, Q, P, E, lamH, lamI, gO, gN, rO, rN, dK, XK, mK, rK, A, H, par, δ, Kc, thrO, thrN, pass, isA,
        PL⟩
    si := si + 1
  return result

end CertGen.Box
