/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Run
public import SandierSerfaty.CertData.Box.Split

/-!
# Emission of the box data and shard modules (untrusted)

Writes, under `OUT/SandierSerfaty/CertData/Box/`, the literal data of the box assertions and the `decide +kernel`
shards (namespace `SandierSerfaty.CertData.Box`):

* data: `QPage*`, `QCells` (the query cells, `qTbl`, `qRf`, `qRe`), `Idx/P*`, `Idx` (the cell-index proposals,
  one packed `12`-bit literal per row: `oIdx j k`), `Consts` (the evaluator data `evalE`, the enclosure literals,
  the grids `oGrid`, `nGrid`, `kGrid`, `a7Dat`, `hessDat`, `parLit`, `deltaLit`, `kcLit`; the grid nodes are the
  closed formulas of `CertData.Box.Nodes`);
* shards: `Outer/S*`, `Neg/S*` (row segments of at most `seg` queries with literal checkpoints, `outerSeg`/`negSeg`,
  the rows, a block per module), `KRow`, `A7/S*` (blocks of `aSeg` rectangles), `Hess/S*` (segments of `hSeg`
  Hessian cells with interval checkpoints), `QCheck/S*` (`cellCheck` on blocks of query cells), `Checks` (the
  non-row conjuncts and the scalar checks), `Final` (the Booleans of `certificateGoal_of_checks` from the shards).

Every emitted segment statement is first evaluated natively with the same definitions (`outerSeg`, `negSeg`,
`sumSeg`, `hessSeg`, `allFrom`, …); emission stops at the first failure.
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-! ### Printing -/

def sintS (a : SInt) : String := s!"⟨{a.isNeg}, {a.mag}⟩"
def fxS (a : Fx 128) : String := s!"⟨{sintS a.v}⟩"
def ivS (a : IV 128) : String := s!"⟨{sintS a.lo}, {sintS a.hi}⟩"
def qcellS (c : QCell) : String :=
  s!"⟨{fxS c.lo}, {fxS c.hi}, {fxS c.tb}, {fxS c.fb}, {fxS c.f1}, {fxS c.eb}, {fxS c.e1}⟩"
def ratS (q : Rat) : String := s!"(mkRat ({q.num}) {q.den})"

def hexDigit (n : Nat) : Char := ("0123456789abcdef".toList).getD (n % 16) '0'

/-- The packed literal `∑ v_k 2^(12k)` in hexadecimal (`v_k < 4096`). -/
def packHex (v : Array Nat) : String := Id.run do
  let mut s := "0x"
  for i in [0:v.size] do
    let x := v[v.size - 1 - i]!
    s := s.push (hexDigit (x / 256)) |>.push (hexDigit (x / 16)) |>.push (hexDigit x)
  return s

def pad (n w : Nat) : String := let s := toString n; "".pushn '0' (w - s.length) ++ s

/-- A binary `cond` tree on `var` over the leaves `lo, …, hi - 1` (one leaf per line). -/
def treeS (var : String) (leaf : Nat → String) : Nat → Nat → Nat → String
  | 0, lo, _ => "\n    " ++ leaf lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then "\n    " ++ leaf lo
    else
      let mid := (lo + hi) / 2
      s!"cond (Nat.blt {var} {mid}) ({treeS var leaf fuel lo mid}) ({treeS var leaf fuel mid hi})"

def header (title : String) (imports : List String) (doc : String) : String :=
  "/-\nCopyright (c) 2026 Scott Armstrong. All rights reserved.\nReleased under Apache 2.0 license as described in " ++
  "the file LICENSE.\nAuthors: Scott Armstrong, Sylvia Serfaty\n-/\nmodule\n\n" ++
  String.join (imports.map fun m => s!"public import {m}\n") ++ s!"\n/-!\n# {title}\n\n{doc}\n-/\n\n"

def opensS : String :=
  "open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table\n" ++
  "open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box\n"

def dataMod (title : String) (imports : List String) (doc body : String) : String :=
  header title imports doc ++ "@[expose] public section\n\nnamespace SandierSerfaty.CertData.Box\n\n" ++ opensS ++
    "\n" ++ body ++ "end SandierSerfaty.CertData.Box\n"

def proofMod (title : String) (imports : List String) (doc body : String) : String :=
  header title imports doc ++ "public section\n\nnamespace SandierSerfaty.CertData.Box\n\n" ++ opensS ++ "\n" ++
    body ++ "end SandierSerfaty.CertData.Box\n"

def boxPath (out rel : String) : System.FilePath :=
  (out : System.FilePath) / "SandierSerfaty" / "CertData" / "Box" / (rel ++ ".lean")

def boxMod (rel : String) : String := "SandierSerfaty.CertData.Box." ++ rel.replace "/" "."

def writeBox (out rel s : String) : IO Unit := do
  let p := boxPath out rel
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p s

/-- `true`, or an error naming the failed statement. -/
def must (ok : Bool) (what : String) : IO Unit :=
  if ok then pure () else throw (IO.userError s!"native check failed before emission: {what}")

/-- Pieces `(start, length)` of `0, …, n - 1` of length `L`, the last one nonempty. -/
def pieces (n L : Nat) : Array (Nat × Nat) := Id.run do
  let mut a := #[]
  let mut k := 0
  while k < n do
    a := a.push (k, min L (n - k))
    k := k + L
  return a

/-- `allFrom_cons (f := f) h_a (allFrom_cons … (allFrom_zero f (a + n)))` over the names `hs` of `f a, …`. -/
def consChain (f : String) (a : Nat) (hs : Array String) : String := Id.run do
  let mut t := s!"(allFrom_zero ({f}) {a + hs.size})"
  for i in [0:hs.size] do
    let j := hs.size - 1 - i
    t := s!"(allFrom_cons (f := {f}) (a := {a + j}) {hs[j]!} {t})"
  return t

/-- `allLt_add (f := f) (n := a) (m := len) (… (allLt_add (allLt_zero f) h₀) …) h_last` over blocks
`(name, start, length)` (explicit lengths: see `segChain`). -/
def addChain (f : String) (bs : Array (String × Nat × Nat)) : String := Id.run do
  let mut t := s!"(allLt_zero ({f}))"
  for (h, a, len) in bs do
    t := s!"(allLt_add (f := {f}) (n := {a}) (m := {len}) {t} {h})"
  return t

/-- `lem (m := N - k₁) h₀ (lem (m := N - k₂) h₁ (… h_last))` for segment names ending in their first cell `kᵢ`
(the remaining lengths are explicit: inferring them makes the elaborator unfold the loop on a literal count). -/
def segChain (lem : String) (hs : Array String) (total : Nat) : String := Id.run do
  let start : String → Nat := fun h => ((h.splitOn "_").getLast!).toNat!
  let mut t := hs[hs.size - 1]!
  for i in [1:hs.size] do
    let j := hs.size - 1 - i
    t := s!"({lem} (m := {total - start hs[j + 1]!}) {hs[j]!} {t})"
  return t

/-! ### Data modules -/

def emitQCells (out : String) (Q : QOut) : IO (List String) := do
  let n := Q.cells.size
  let nb := (n + 63) / 64
  let per := 16
  let np := (nb + per - 1) / per
  let mut mods := []
  for p in [0:np] do
    let mut body := ""
    for b in [p * per:min nb ((p + 1) * per)] do
      let cs := (Q.cells.extract (64 * b) (64 * b + 64)).map qcellS
      body := body ++ s!"/-- The query cells `{64 * b} + k`. -/\ndef qcB_{b} (k : Nat) : QCell :=\n  " ++
        treeS "k" (fun i => cs[i]!) 64 0 cs.size ++ "\n\n"
    writeBox out s!"QPage{pad p 2}" (dataMod s!"The query cells, page {p} (data)"
      ["SandierSerfaty.Certificate.Box.NumDef"]
      s!"The query cells (`Query.QCell`) of the blocks from `{p * per}` (`64` cells each); generated by `lake exe certgen` (box mode)." body)
    mods := mods ++ [boxMod s!"QPage{pad p 2}"]
  let body := "/-- The query cells, by block. -/\ndef qBlk (b k : Nat) : QCell :=\n  " ++
    treeS "b" (fun i => s!"qcB_{i} k") 64 0 nb ++
    "\n\n/-- The query cell `i`. -/\ndef qCell (i : Nat) : QCell := qBlk (Nat.div i 64) (Nat.mod i 64)\n\n" ++
    s!"/-- The query table (one cell per table cell). -/\ndef qTbl : QTable := ⟨{n}, qCell⟩\n\n" ++
    s!"/-- The radius `rf` of the cells (`f̃₀`). -/\ndef qRf : Nat := {Q.rf}\n\n" ++
    s!"/-- The radius `re` of the cells (`ẽ`). -/\ndef qRe : Nat := {Q.re}\n\n"
  writeBox out "QCells" (dataMod "The query cells (dispatch, data)" mods
    "The query table `qTbl` of the value queries and the global radii `qRf`, `qRe` (`Query.cellCheck`)." body)
  return mods ++ [boxMod "QCells"]

/-- The packed index literal `∑ idx_k 4096^k` of a row, and the decoding of the shards. -/
def packNat (v : Array Nat) : Nat := v.foldr (fun x acc => acc * 4096 + x) 0

def unpack (p k : Nat) : Nat := Nat.land (Nat.shiftRight p (Nat.mul 12 k)) 4095

/-- The index pages `Idx/{P}nn` (`perPage` rows each) and the dispatch `{pre}Idx j k`. -/
def emitIdx (out pre : String) (rows : Array (Array Nat)) (perPage : Nat) : IO (List String) := do
  let n := rows.size
  let np := (n + perPage - 1) / perPage
  let mut mods := []
  for p in [0:np] do
    let a := p * perPage
    let b := min n (a + perPage)
    let mut body := ""
    for j in [a:b] do
      body := body ++ s!"/-- The packed cell indices of row `{j}`. -/\ndef {pre}Row_{j} : Nat :=\n  {packHex rows[j]!}\n\n"
    body := body ++ s!"/-- The packed rows `{a} + i`. -/\ndef {pre}RowP{p} (i : Nat) : Nat :=\n  " ++
      treeS "i" (fun i => s!"{pre}Row_{a + i}") 64 0 (b - a) ++ "\n\n"
    let rel := s!"Idx/{pre.capitalize}{pad p 2}"
    writeBox out rel (dataMod s!"Cell-index proposals `{pre}`, rows {a}–{b - 1} (data)" ["SandierSerfaty.Certificate.Box.NumDef"]
      "One literal per row: the cell index proposed for the query `k` is its `12`-bit digit `k`." body)
    mods := mods ++ [boxMod rel]
  let body := s!"/-- The packed rows, by page. -/\ndef {pre}RowQ (p i : Nat) : Nat :=\n  " ++
    treeS "p" (fun q => s!"{pre}RowP{q} i") 64 0 np ++
    s!"\n\n/-- The packed row `j`. -/\ndef {pre}RowAt (j : Nat) : Nat := {pre}RowQ (Nat.div j {perPage}) (Nat.mod j {perPage})\n\n" ++
    s!"/-- The cell index proposed for the query `k` of row `j`. -/\ndef {pre}Idx (j k : Nat) : Nat :=\n  Nat.land (Nat.shiftRight ({pre}RowAt j) (Nat.mul 12 k)) 4095\n\n"
  let rel := s!"Idx/{pre.capitalize}"
  writeBox out rel (dataMod s!"Cell-index proposals `{pre}` (dispatch, data)" mods
    s!"`{pre}Idx j k`: the cell index of the query `k` of row `j`, from the packed row literals." body)
  return mods ++ [boxMod rel]

/-- The packed literal `∑ (i0_k + 4096 i1_k) 2^(24k)` in hexadecimal (`i0_k, i1_k < 4096`). -/
def packHex2 (v : Array (Nat × Nat)) : String := Id.run do
  let mut s := "0x"
  for i in [0:v.size] do
    let (a, b) := v[v.size - 1 - i]!
    for x in [b, a] do
      s := s.push (hexDigit (x / 256)) |>.push (hexDigit (x / 16)) |>.push (hexDigit x)
  return s

/-- The index-range pages `Idx/{P}nn` (`perPage` rows each) and the dispatch `{pre}Ix j k : Nat × Nat`. -/
def emitIdx2 (out pre : String) (rows : Array (Array (Nat × Nat))) (perPage : Nat) : IO (List String) := do
  let n := rows.size
  let np := (n + perPage - 1) / perPage
  let mut mods := []
  for p in [0:np] do
    let a := p * perPage
    let b := min n (a + perPage)
    let mut body := ""
    for j in [a:b] do
      body := body ++ s!"/-- The packed index ranges of row `{j}`. -/\ndef {pre}Row_{j} : Nat :=\n  {packHex2 rows[j]!}\n\n"
    body := body ++ s!"/-- The packed rows `{a} + i`. -/\ndef {pre}RowP{p} (i : Nat) : Nat :=\n  " ++
      treeS "i" (fun i => s!"{pre}Row_{a + i}") 64 0 (b - a) ++ "\n\n"
    let rel := s!"Idx/{pre.capitalize}{pad p 2}"
    writeBox out rel (dataMod s!"Index-range proposals `{pre}`, rows {a}–{b - 1} (data)" ["SandierSerfaty.Certificate.Box.NumDef"]
      "One literal per row: the index range `(i0, i1)` proposed for the query `k` is its `24`-bit digit `k` (`i0` in the low `12` bits)." body)
    mods := mods ++ [boxMod rel]
  let body := s!"/-- The packed rows, by page. -/\ndef {pre}RowQ (p i : Nat) : Nat :=\n  " ++
    treeS "p" (fun q => s!"{pre}RowP{q} i") 64 0 np ++
    s!"\n\n/-- The packed row `j`. -/\ndef {pre}RowAt (j : Nat) : Nat := {pre}RowQ (Nat.div j {perPage}) (Nat.mod j {perPage})\n\n" ++
    s!"/-- The index range proposed for the query `k` of row `j`. -/\ndef {pre}Ix (j k : Nat) : Nat × Nat :=\n" ++
    s!"  (Nat.land (Nat.shiftRight ({pre}RowAt j) (Nat.mul 24 k)) 4095,\n" ++
    s!"    Nat.land (Nat.shiftRight ({pre}RowAt j) (Nat.add (Nat.mul 24 k) 12)) 4095)\n\n"
  let rel := s!"Idx/{pre.capitalize}"
  writeBox out rel (dataMod s!"Index-range proposals `{pre}` (dispatch, data)" mods
    s!"`{pre}Ix j k`: the index range of the query `k` of row `j` (checked-index lookup), from the packed row literals." body)
  return mods ++ [boxMod rel]

/-- The enclosure literals of the box data. -/
structure Lits where
  f0l : IV 128
  f0R : IV 128
  eR : IV 128
  bl : IV 128
  lsq : IV 128
  l : IV 128
  k0 : IV 128
  mu : IV 128

def litsOf (r : BoxOut) : Lits :=
  ⟨r.P.f0lI, r.P.f0RI, r.P.eRI, r.P.blI, r.P.lsqI, r.P.lI, IV.neg (IV.mul r.P.piI r.P.blI), muOf r.P r.lamI⟩

def emitConsts (out : String) (r : BoxOut) (imports : List String) : IO Unit := do
  let L := litsOf r
  let (nj, nk) := (r.A.nj, r.A.nk)
  let g := r.gO
  let h := r.gN
  let same := r.gO == r.gN
  let body :=
    "/-! ### The evaluator -/\n\n" ++
    s!"/-- `λ̂`, the generator's proposal (inside the enclosure `lamBox`). -/\ndef lamHat : Fx 128 := {fxS r.E.lam}\n\n" ++
    s!"/-- `μ̂`. -/\ndef muHat : Fx 128 := {fxS r.E.mu}\n\n" ++
    s!"/-- `κ̂`. -/\ndef kapHat : Fx 128 := {fxS r.E.kap}\n\n" ++
    s!"/-- `ĉ`. -/\ndef ccHat : Fx 128 := {fxS r.E.cc}\n\n" ++
    s!"/-- The exterior threshold for `t²`. -/\ndef lsqHat : Fx 128 := {fxS r.E.lsq}\n\n" ++
    "/-- The evaluator data of the value queries. -/\ndef evalE : EvalData := ⟨qTbl, lamHat, muHat, kapHat, ccHat, lsqHat⟩\n\n" ++
    "/-! ### The enclosures (literals; `Box.Checks` ties them to the table) -/\n\n" ++
    (if r.certLam then "/-- The enclosure of `λ`: the certified fine enclosure `lamFLit` (`lamFine flTbl dLit lamPar`). -/\ndef lamBox : IV 128 := lamFLit\n\n"
     else s!"/-- NOT CERTIFIED: a hypothetical fine enclosure `λ̂ ± w` of `λ`, standing for the output of the\nmissing fine `λ` quadrature; `IV.Mem lam lamBox` has no proof. -/\ndef lamBox : IV 128 := {ivS r.lamI}\n\n") ++
    s!"/-- `f₀(l)`: `IV.addRad (ntAt {r.P.iL}).f0 lamRad`. -/\ndef f0lLit : IV 128 := {ivS L.f0l}\n\n" ++
    s!"/-- `f₀(R₀)`: `IV.addRad (ntAt {r.P.iR}).f0 lamRad`. -/\ndef f0RLit : IV 128 := {ivS L.f0R}\n\n" ++
    s!"/-- `e(R₀)`: `IV.addRad (ntAt {r.P.iR}).e0 lamRad`. -/\ndef eRLit : IV 128 := {ivS L.eR}\n\n" ++
    s!"/-- `B(l)`: `IV.addRad (basis dLit 5 (knotIV dLit 6)).bsum.c0 lamRad`. -/\ndef blLit : IV 128 := {ivS L.bl}\n\n" ++
    s!"/-- `l²`: `IV.sq (knotIV dLit 6)`. -/\ndef lsqLit : IV 128 := {ivS L.lsq}\n\n" ++
    s!"/-- `l`: `knotIV dLit 6`. -/\ndef lLit : IV 128 := {ivS L.l}\n\n" ++
    s!"/-- `-π B(l)`. -/\ndef k0Lit : IV 128 := {ivS L.k0}\n\n" ++
    s!"/-- `μ`: `muEnc dLit.r0 f0RLit eRLit lamBox`. -/\ndef muLit : IV 128 := {ivS L.mu}\n\n" ++
    "/-! ### The grids -/\n\n" ++
    s!"/-- The outer threshold (`min 2Q` over the tested nodes). -/\ndef oThr : SInt := {sintS (sintOfInt r.thrO)}\n\n" ++
    s!"/-- The negative-part threshold (`max N` over the rows). -/\ndef nThr : SInt := {sintS (sintOfInt r.thrN)}\n\n" ++
    s!"/-- The `K` threshold (the sum of the `K` row). -/\ndef kThr : SInt := {sintS (sintOfInt r.rK.sumQ)}\n\n" ++
    s!"/-- The outer grid (A8). -/\ndef oGrid : OuterGrid :=\n  ⟨{g.nd}, {g.nx}, gridD3 {g.d1} {g.d2} {g.d3}, gridS3 {g.s1} {g.s2} {g.s3}, oIdx, {g.d1}, {g.d1 + g.d2}, {g.s1}, {g.s1 + g.s2}, oThr⟩\n\n" ++
    s!"/-- The negative-part grid (A9). -/\ndef nGrid : NegGrid :=\n  ⟨{h.nd}, {h.nx}, gridD3 {h.d1} {h.d2} {h.d3}, gridS3 {h.s1} {h.s2} {h.s3}, {if same then "oIdx" else "nIdx"}, nThr⟩\n\n" ++
    s!"/-- The packed cell indices of the `K` row. -/\ndef kRowLit : Nat :=\n  {packHex r.rK.idx}\n\n" ++
    "/-- The cell index of the query `k` of the `K` row. -/\ndef kIdx (k : Nat) : Nat := Nat.land (Nat.shiftRight kRowLit (Nat.mul 12 k)) 4095\n\n" ++
    s!"/-- The `K` row. -/\ndef kGrid : KGrid := ⟨{r.mK}, {r.dK}, kS {r.XK} {r.mK}, kIdx, kThr⟩\n\n" ++
    s!"/-- The A7 rectangles. -/\ndef a7Dat : A7Data :=\n  ⟨iTbl, f0lLit, k0Lit, lsqLit, lLit, lamBox, muLit, lamRad, {r.A.L1}, {r.A.L2}, {r.A.L3}, {r.A.L4}, {nj}, {nk}, a7D {nj}, a7S {nk}⟩\n\n" ++
    s!"/-- The Hessian rows (A10). -/\ndef hessDat : HessData :=\n  ⟨iTbl, f0lLit, k0Lit, lsqLit, lLit, lamBox, muLit, lamRad, {r.H.nd}, {r.H.nx}, {r.H.jmin}, hessD {r.H.nd}, hessS {r.H.jmin} {r.H.nx - r.H.jmin}⟩\n\n" ++
    s!"/-- The free parameters. -/\ndef parLit : NumFree :=\n  ⟨{r.par.oSh}, {r.par.oDh}, {r.par.oRho}, {r.par.nSh}, {r.par.nDh}, {r.par.kSh}, {r.par.kRd}, {r.par.kRx}⟩\n\n" ++
    s!"/-- The error budget `δ` of one value. -/\ndef deltaLit : Rat := {ratS r.δ}\n\n" ++
    s!"/-- The threshold `Kc ≥ K`. -/\ndef kcLit : Rat := {ratS r.Kc}\n\n"
  writeBox out "Consts" (dataMod "The box data: evaluator, enclosures, grids, parameters (data)" imports
    ("The literal data of `Box.certificateGoal_of_checks` other than the table (generated by `lake exe certgen`, box\n" ++
     "mode; untrusted until checked). The grid nodes are the closed formulas of `CertData.Box.Nodes`.") body)

end CertGen.Box
