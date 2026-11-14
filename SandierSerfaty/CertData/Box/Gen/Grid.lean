/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Core
public import SandierSerfaty.CertData.Box.Gen.Idx

/-!
# The grids of the box assertions and their native evaluation (untrusted)

The default meshes (`Spec`, overridable on the command line), the literal grids as `Nat` mantissas
(`OuterGrid`, `NegGrid`, `KGrid`, `A7Data`, `HessData` of `Box.Eval`, `Box.KRowDef`, `Box.CtxDef`, `Box.HessDef`),
and the instrumented native passes that propose the cell indices, the thresholds and the bounds `L₁, …, L₄` and
measure the margins. The Boolean checks themselves are then run unchanged (`SandierSerfaty.CertData.Box.Gen.Run`).

C++ conventions (`verification/grids.hpp`): `grid_seq(a, b, h)` = the nodes `a + (b - a) i/m`, `m = ⌈(b - a)/h⌉`;
the outer grid is `[b, d_l) ∪ [d_l, d_u) ∪ [d_u, .697]` × `[0, s_l) ∪ [s_l, s_u) ∪ [s_u, .65]` with the hole
`(d_l, d_u) × (s_l, s_u)`; the `s` nodes here are even mantissas (exact midpoints, `Box.midVal`), the endpoints
are rounded outward so that the literal comparisons of `Box.NumCheck` hold.
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-- The mesh parameters (the defaults are those of the certificate). -/
structure Spec where
  /-- Outer grid steps `D_h`, `S_h`. -/
  oD : Rat := 247 / 1000000
  oS : Rat := 234 / 1000000
  /-- Negative-part grid steps. -/
  nD : Rat := 247 / 1000000
  nS : Rat := 234 / 1000000
  /-- A7 mesh (C++ `bdsup`, j9: `.0048`). -/
  aH : Rat := 48 / 10000
  /-- Hessian meshes (j9: `×4` of `.00004`, `.00008`). -/
  hD : Rat := 16 / 100000
  hS : Rat := 32 / 100000
  /-- `K` row step (C++ `calcK`: `.0001`). -/
  kH : Rat := 1 / 10000
  /-- `lamEnc` subintervals (default `64`). -/
  lamN : Nat := 64
  /-- Midpoints of the proposal `λ̂`. -/
  lamM : Nat := 20000
  /-- The parameters of the fine certified `λ` (`Lambda.lamFine`, scenario L): steps of the two midpoint sums and
  `s₀ = 1/lamS0d` (the paper: `45000`, `45000`, `100`). -/
  lamNq : Nat := 45000
  lamNe : Nat := 45000
  lamS0d : Nat := 100
  /-- Steps per declaration and declarations per module of the `λ` shards. -/
  lamL : Nat := 1000
  lamPer : Nat := 9
  /-- Also run scenario A (the coarse `lamEnc`, which cannot pass the box checks). -/
  withA : Bool := false
  /-- Hypothetical half-widths of a fine certified `λ` enclosure (scenario B; default `10⁻⁷`). -/
  lamW : List Rat := []
  /-- What-if table densities per segment (empty: the table of `CertGen.Main`). -/
  dens : List Nat := []
  /-- Value queries per shard declaration (outer, negative, `K` rows). -/
  seg : Nat := 400
  /-- A7 rectangles per shard declaration. -/
  aSeg : Nat := 8
  /-- Hessian cells per shard declaration. -/
  hSeg : Nat := 16
  /-- Rows per index page; value rows, A7 rows, Hessian rows per shard module; query cells per declaration and
  declarations per query-cell module. -/
  idxPage : Nat := 48
  oMod : Nat := 24
  aMod : Nat := 4
  hMod : Nat := 1
  qSeg : Nat := 64
  qMod : Nat := 8
  /-- Emit the shard modules into `OUT` (only if every check passes, unless `--force`). -/
  emit : Bool := false
  /-- Write the kernel probes into `OUT/kprobe`. -/
  probe : Bool := false
  /-- Skip scenario A (the certified `lamEnc`); the scenario whose data are emitted (`0` = first). -/
  noA : Bool := false
  emitScen : Nat := 0
  force : Bool := false
  /-- Parallel tasks of the native passes. -/
  threads : Nat := 4
  /-- Skip the A7 / Hessian passes (quick runs). -/
  skipDeriv : Bool := false
deriving Inhabited

def parseRat (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [a] => (a.toInt?).map fun z => (z : Rat)
  | [a, b] => match a.toInt?, b.toNat? with
    | some z, some n => if n = 0 then none else some ((z : Rat) / (n : Rat))
    | _, _ => none
  | _ => none

/-- `key=value` overrides (`oD=247/1000000`, `outer=13/10` scales both outer steps of `j9`, …). -/
def Spec.parse (args : List String) : Spec := Id.run do
  let mut S : Spec := {}
  for a in args do
    match a.splitOn "=" with
    | [k, v] =>
      match k, parseRat v with
      | "oD", some q => S := { S with oD := q }
      | "oS", some q => S := { S with oS := q }
      | "nD", some q => S := { S with nD := q }
      | "nS", some q => S := { S with nS := q }
      | "outer", some q => S := { S with oD := q * (19 / 100000), oS := q * (18 / 100000) }
      | "neg", some q => S := { S with nD := q * (19 / 100000), nS := q * (18 / 100000) }
      | "aH", some q => S := { S with aH := q }
      | "hD", some q => S := { S with hD := q }
      | "hS", some q => S := { S with hS := q }
      | "kH", some q => S := { S with kH := q }
      | "lamN", some q => S := { S with lamN := (floorQ q).toNat }
      | "lamM", some q => S := { S with lamM := (floorQ q).toNat }
      | "lamW", some q => S := { S with lamW := S.lamW ++ [q] }
      | "lamNq", some q => S := { S with lamNq := max 1 (floorQ q).toNat }
      | "lamNe", some q => S := { S with lamNe := max 1 (floorQ q).toNat }
      | "lamS0d", some q => S := { S with lamS0d := max 1 (floorQ q).toNat }
      | "lamL", some q => S := { S with lamL := max 1 (floorQ q).toNat }
      | "lamPer", some q => S := { S with lamPer := max 1 (floorQ q).toNat }
      | "threads", some q => S := { S with threads := max 1 (floorQ q).toNat }
      | "seg", some q => S := { S with seg := max 1 (floorQ q).toNat }
      | "aSeg", some q => S := { S with aSeg := max 1 (floorQ q).toNat }
      | "hSeg", some q => S := { S with hSeg := max 1 (floorQ q).toNat }
      | "idxPage", some q => S := { S with idxPage := max 1 (floorQ q).toNat }
      | "oMod", some q => S := { S with oMod := max 1 (floorQ q).toNat }
      | "aMod", some q => S := { S with aMod := max 1 (floorQ q).toNat }
      | "hMod", some q => S := { S with hMod := max 1 (floorQ q).toNat }
      | "qSeg", some q => S := { S with qSeg := max 1 (floorQ q).toNat }
      | "qMod", some q => S := { S with qMod := max 1 (floorQ q).toNat }
      | "emitScen", some q => S := { S with emitScen := (floorQ q).toNat }
      | "dens", _ => S := { S with dens := (v.splitOn ",").filterMap String.toNat? }
      | _, _ => pure ()
    | _ =>
      if a == "--noderiv" then S := { S with skipDeriv := true }
      if a == "--emit" then S := { S with emit := true }
      if a == "--probe" then S := { S with probe := true }
      if a == "--noA" then S := { S with noA := true }
      if a == "--withA" then S := { S with withA := true }
      if a == "--force" then S := { S with force := true }
  return S

/-! ### Grid nodes (the closed formulas of `CertData.Box.Nodes`) -/

/-- The segment counts `(m₁, m₂, m₃)` of the outer / negative grids for the steps `(hd, hs)`. -/
structure G3 where
  d1 : Nat
  d2 : Nat
  d3 : Nat
  s1 : Nat
  s2 : Nat
  s3 : Nat
deriving Inhabited, BEq

def G3.of (hd hs : Rat) : G3 :=
  ⟨nsamp bQ dlQ hd, nsamp dlQ duQ hd, nsamp duQ dTopQ hd, nsamp 0 slQ hs, nsamp slQ suQ hs, nsamp suQ sTopQ hs⟩

def G3.nd (g : G3) : Nat := g.d1 + g.d2 + g.d3
def G3.nx (g : G3) : Nat := g.s1 + g.s2 + g.s3

/-- The `d` nodes `0, …, nd` (`gridD3`); the hole rows are `jl = d1`, `jr = d1 + d2`. -/
def G3.dArr (g : G3) : Array Nat := (Array.range (g.nd + 1)).map (gridD3 g.d1 g.d2 g.d3)

/-- The `s` nodes `0, …, nx` (`gridS3`); the hole nodes are `kl = s1`, `kr = s1 + s2`. -/
def G3.sArr (g : G3) : Array Nat := (Array.range (g.nx + 1)).map (gridS3 g.s1 g.s2 g.s3)

def maxStep (a : Array Nat) : Nat := Id.run do
  let mut m := 0
  for i in [0:a.size - 1] do
    m := max m (a[i + 1]! - a[i]!)
  return m

/-- The A7 cell counts `(nj, nk)` for the mesh `h`. -/
def a7Counts (h : Rat) : Nat × Nat := (nsamp bQ dTopQ h, nsamp 0 sTopQ h)

/-- The Hessian cell counts `(nd, m₁, m₂)` (`jmin = m₁`). -/
def hessCounts (hd hs : Rat) : Nat × Nat × Nat := (nsamp dlQ duQ hd, nsamp 0 slQ hs, nsamp slQ suQ hs)

/-! ### Rows of value queries -/

structure RowRes where
  idx : Array Nat
  /-- Failed proposals (gaps) or failed queries. -/
  bad : Nat
  /-- `min 2Q_k` over the tested nodes (units `2^-256`). -/
  minQ2 : Int
  /-- The node of the minimum. -/
  minK : Nat
  /-- `∑ w_k max 0 (-v_k)`. -/
  negN : Int
  /-- `∑ w_k v_k`. -/
  sumQ : Int
  /-- The accumulators `Q`, `N` after the cells `0, …, cL - 1`, `c = 1, 2, …` (the checkpoints of the shards). -/
  ckQ : Array Int
  ckN : Array Int
deriving Inhabited

def bigI : Int := 2 ^ 400

/-- The instrumented pass over one row (the same `midVal` as `outerLoop`/`negLoop`/`sumLoop`). -/
def rowRes (L : Nat) (E : EvalData) (cells : Array QCell) (dm : Nat) (sm : Array Nat) (skip : Nat → Bool) :
    RowRes := Id.run do
  let nx := sm.size - 1
  let smF : Nat → Nat := fun k => sm[k]!
  let mut idx : Array Nat := Array.mkEmpty nx
  let mut acc : Int := 0
  let mut neg : Int := 0
  let mut minQ : Int := bigI
  let mut minK := 0
  let mut bad := 0
  let mut ckQ : Array Int := #[]
  let mut ckN : Array Int := #[]
  for k in [0:nx] do
    if k > 0 && k % L == 0 then
      ckQ := ckQ.push acc
      ckN := ckN.push neg
    if !skip k && 2 * acc < minQ then
      minQ := 2 * acc
      minK := k
    let i := (propose E cells dm (midM smF k)).getD 0
    if (propose E cells dm (midM smF k)).isNone then bad := bad + 1
    idx := idx.push i
    match midVal E (fun _ => i) dm smF k with
    | none => bad := bad + 1
    | some v =>
      let w : Int := Int.ofNat (sm[k + 1]! - sm[k]!)
      acc := acc + w * v.v.toInt
      neg := neg + w * max 0 (-v.v.toInt)
  if !skip nx && 2 * acc < minQ then
    minQ := 2 * acc
    minK := nx
  return ⟨idx, bad, minQ, minK, neg, acc, ckQ, ckN⟩

/-- `f` on `0, …, n - 1` in `T` parallel tasks (contiguous blocks), in order. -/
def parMap {α : Type} [Inhabited α] (T n : Nat) (f : Nat → α) : Array α := Id.run do
  let blk := (n + T - 1) / T
  let tasks := (List.range T).map fun t =>
    Task.spawn (prio := .dedicated) fun _ => ((List.range blk).filterMap fun i =>
      if t * blk + i < n then some (f (t * blk + i)) else none).toArray
  return tasks.foldl (fun acc tk => acc ++ tk.get) #[]

/-- All rows of a grid. -/
def gridRows (T L : Nat) (E : EvalData) (cells : Array QCell) (dm sm : Array Nat) (skip : Nat → Nat → Bool) :
    Array RowRes :=
  parMap T dm.size fun j => rowRes L E cells dm[j]! sm (skip j)

/-! ### Derivative rectangles (A7) and Hessian rows (A10) -/

def magMax (I : IV 128) : Nat := max I.lo.mag I.hi.mag

/-- The four magnitudes of a rectangle (`none` if the context fails), with the checked-index lookup. -/
def rectMags (A : A7Data) (j k : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match mkDCtx2I A.T A.f0lI A.k0I A.lsqI A.lI A.lamI A.muI A.rad
      (IV.ofNatPair (A.dp j) (A.dp (j + 1))) (IV.ofNatPair (A.sp k) (A.sp (k + 1))) (a7Ix A j k).1 (a7Ix A j k).2 with
  | none => none
  | some c => some (magMax (gdOf c.toDCtx), magMax (gsOf c.toDCtx), magMax (gddOf c), magMax (gssOf c))

/-- Per `d` row: the maxima of the four magnitudes and the number of failed contexts. -/
def a7Row (A : A7Data) (j : Nat) : (Nat × Nat × Nat × Nat) × Nat := Id.run do
  let mut m := (0, 0, 0, 0)
  let mut bad := 0
  for k in [0:A.nk] do
    match rectMags A j k with
    | none => bad := bad + 1
    | some (a, b, c, d) => m := (max m.1 a, max m.2.1 b, max m.2.2.1 c, max m.2.2.2 d)
  return (m, bad)

structure HessMin where
  aLo : Int := bigI
  cLo : Int := bigI
  detLo : Int := bigI
  bad : Nat := 0
  fails : Nat := 0
deriving Inhabited

/-- The instrumented pass of `HessData.rowAuxG (H.ctxI (hessIx H))` over the row `a`. -/
def hessRow (H : HessData) (a : Nat) : HessMin := Id.run do
  let mut acc : IV 128 := IV.ofNatPair 0 0
  let mut r : HessMin := {}
  for i in [0:H.nx] do
    match H.ctxI (hessIx H) a i with
    | none => r := { r with bad := r.bad + 1 }
    | some c =>
      if H.jmin ≤ i then
        let A := IV.add acc (IV.mul (IV.ofNatPair 0 (widthN H.sp i)) (gddOf c))
        let B := gdOf c.toDCtx
        let C := gsOf c.toDCtx
        let det := IV.sub (IV.mul A C) (IV.sq B)
        r := { r with aLo := min r.aLo A.lo.toInt, cLo := min r.cLo C.lo.toInt, detLo := min r.detLo det.lo.toInt,
                      fails := r.fails + (if hessTest A B C then 0 else 1) }
      acc := IV.add acc (IV.mul (IV.ofNatPair (widthN H.sp i) (widthN H.sp i)) (gddOf c))
  return r

end CertGen.Box
