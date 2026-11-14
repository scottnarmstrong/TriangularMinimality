/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Data
public import SandierSerfaty.Certificate.Basis.Core
public import SandierSerfaty.Certificate.Table.Eval
public import SandierSerfaty.Certificate.Query.Lam
public import SandierSerfaty.Certificate.Query.Const
public import SandierSerfaty.CertData.Box.Gen.Entry

/-!
# `lake exe certgen`: the untrusted data generator of the certificate for the square-torus bound

Usage: `lake exe certgen OUT [BUDGET COREMOD] [--quick]`: `BUDGET` estimated kernel seconds per table shard
module (default 180; the chunk lengths per segment are `chunkLen`), `COREMOD` core declarations per shard
module (default 8; the core cells per declaration are `corePer`); `--quick` skips the native run of the table
chunk checks. Writes the literal data modules and the shard modules of
the opt-in library `SandierSerfatyCert` under `OUT/SandierSerfaty/CertData/`, and prints a summary (counts,
widths, the λ enclosure, the A6 margins).

The generator is natively compiled from the *same* evaluator definitions the kernel checks
(`SandierSerfaty.Certificate.{Basis,Table,Query}`, Mathlib-free): it proposes data, the kernel only checks the
cheap `Bool` conditions of the shards. Nothing here is
trusted; `native_decide` is not involved. Every check the shards will run is first run natively here, so a
failing shard is reported before any kernel time is spent.

## Computations

Natively compiled calls of the certificate's own evaluator definitions:

* the enclosures of `√3`, `p = (1/12)^{1/4}`, `R₀ = (4/27)^{1/4}` (floors by integer square roots);
* the coefficient blocks of assertion A1 (`coeffsFrom`/`boxSums`, the C++ squares `D = 256` for `c_1` and
  `D = 48` for `c_2, …, c_38`), and the basis constants `mkData`;
* the table nodes (the C++ node scheme `κ_j + (κ_{j+1} - κ_j) i/n` with the densities of `density`, the cell count of
  each segment rounded up to a multiple of `8`), the propagation chunk by chunk from literal checkpoints
  (`stepNext`, `fh`, `cellState`, `fhInner`, `initStateOf`), exactly as `chunkCheck`/`innerCheck`/`initCheck`
  recompute them;
* the core cells of assertion A2 (the C++ step `.00022`), the coarse `λ` enclosure (`lamEnc`) and the A6 test.

Every function here only proposes; the kernel checks.

## Printing

Printers for `SInt`, `IV 128`, `Tup`, `SState`, `ModeData`, `BasisData` as anonymous-constructor literals,
binary `cond` trees over blocks of `64` entries (one huge literal does not
parse in reasonable time, `64`-entry chunks behind a binary tree do), and `run`, the whole generation.
-/

public section

namespace CertGen

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis
open SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query

/-- The literal enclosure `piIV` of `SandierSerfaty.Certificate.Arith.Pi` (that module imports Mathlib; the
value is repeated here and checked by the kernel through `dataSubB`). -/
def piLit : IV 128 :=
  ⟨⟨false, 1069028584064966747859680373161870783300⟩, ⟨false, 1069028584064966747859680373161870783301⟩⟩

/-- `[⌊x 2^128⌋, ⌊x 2^128⌋ + 1]/2^128` for `x = (num/den)^{1/4}`. -/
def fourthRoot (num den : Nat) : IV 128 :=
  ⟨⟨false, IV.isqrt (IV.isqrt (num * 2 ^ 512 / den))⟩, ⟨false, IV.isqrt (IV.isqrt (num * 2 ^ 512 / den)) + 1⟩⟩

def pI : IV 128 := fourthRoot 1 12
def rI : IV 128 := fourthRoot 4 27

/-- The checked square root `[l, h]` of `3`. -/
def s3 : Nat × Nat := IV.sqrtProposal (IV.ofNat 3 : IV 128)

/-- The coefficient blocks `(m₀, count, D)`. -/
def coeffBlocks : List (Nat × Nat × Nat) := [(1, 1, 256), (2, 9, 48), (11, 9, 48), (20, 9, 48), (29, 10, 48)]

/-- The row checkpoints of a block: the accumulator after the rows `0, …, c` (`Assemble.rowB`), `c ≤ 2D`. -/
def rowCks (b : Nat × Nat × Nat) : Array (List (IV 128)) := Id.run do
  let D := b.2.2
  let mut acc : List (IV 128) := zeros b.2.1
  let mut out := #[]
  for c in [0:2 * D + 1] do
    acc := rowLoop b.1 D (SInt.sub ⟨false, c⟩ ⟨false, D⟩) (2 * D + 1) acc
    out := out.push acc
  return out

/-- The coefficient enclosures of a block from its last row checkpoint (`Assemble.coeffFinB`). -/
def coeffBlockOf (b : Nat × Nat × Nat) (cks : Array (List (IV 128))) : List (IV 128) :=
  coeffsFrom (sqrt3Half s3.1 s3.2) b.2.2 b.1 cks[2 * b.2.2]!

/-- Rows per declaration of the A1 shards, per block. -/
def rowsPerDecl (b : Nat × Nat × Nat) : Nat := if b.2.2 > 100 then 8 else 13

/-! ### The table -/

/-- The density of segment `j` (finer on the segments `0` and `1`):
4000/12000/6000/24000/24000/24000. -/
def density (j : Nat) : Nat := [4000, 12000, 6000, 24000, 24000, 24000].getD j 24000

def roundUp8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- The number of cells of segment `j`: `⌊(κ_{j+1} - κ_j)·density⌋ + 1`, rounded up to a multiple of `8`. -/
def segCells (d : BasisData) (j : Nat) : Nat :=
  roundUp8 (((knotIV d (j + 1)).lo.mag - (knotIV d j).lo.mag) * density j / 2 ^ 128 + 1)

/-- The node `κ_j + (κ_{j+1} - κ_j) i/n` (the knot interval itself for `i = 0`). -/
def segNode (d : BasisData) (j n i : Nat) : IV 128 :=
  if i = 0 then knotIV d j
  else IV.add (knotIV d j) (IV.divNat (IV.mulNat (IV.sub (knotIV d (j + 1)) (knotIV d j)) i) n)

/-- All the nodes: the segments in order, then the last knot `l`. -/
def allNodes (d : BasisData) : Array (IV 128) := Id.run do
  let mut a : Array (IV 128) := #[]
  for j in [0:6] do
    let n := segCells d j
    for i in [0:n] do
      a := a.push (segNode d j n i)
  return a.push (knotIV d 6)

/-- The global cell index of the first node of segment `j`. -/
def knotIdx (d : BasisData) (j : Nat) : Nat := ((List.range j).map (segCells d)).foldl (· + ·) 0

/-- The chunk length of segment `j` (cells per declaration; measured: a step of segment 2 costs about
2.2 GB of kernel memory, of segments 1, 3–5 about 1 GB, of segment 0 (closed form) very little). -/
def chunkLen (j : Nat) : Nat := [8, 2, 1, 2, 2, 2].getD j 1

/-- The table: nodes, cell and node tuples, the checkpoints by node (at the first node of every chunk of the
segments `≥ 1`, and at the last node), the chunks `(segment, first node, length)`. -/
structure TableOut where
  nodes : Array (IV 128)
  cts : Array Tup
  nts : Array Tup
  cks : Array (Option SState)
  chunks : Array (Nat × Nat × Nat)

def emptyState : SState := ⟨⟨SInt.zero, SInt.zero⟩, ⟨SInt.zero, SInt.zero⟩, []⟩

/-- Build the table, chunk by chunk, restarting every chunk from its checkpoint, as the kernel does. -/
def buildTable (d : BasisData) : TableOut := Id.run do
  let nodes := allNodes d
  let mut cts : Array Tup := #[]
  let mut nts : Array Tup := #[]
  let mut cks : Array (Option SState) := Array.replicate nodes.size none
  let mut chunks : Array (Nat × Nat × Nat) := #[]
  let mut S : SState := emptyState
  let mut i := 0
  for j in [0:6] do
    let n := segCells d j
    let L := chunkLen j
    if j = 1 then
      S := initStateOf d d.pc (initTerms d d.pc)
    for _ in [0:n / L] do
      if j ≥ 1 then cks := cks.set! i (some S)
      chunks := chunks.push (j, i, L)
      for _ in [0:L] do
        let v := nodes[i]!
        let u := nodes[i + 1]!
        if j = 0 then
          cts := cts.push (fhInner d.pi (mkIV v.lo u.hi))
          nts := nts.push (fhInner d.pi u)
        else
          let ptc := mkPt d j (mkIV v.lo u.hi)
          cts := cts.push (fh d.pi ptc (cellState (IV.sub u v) ptc (ivPow (IV.divPos v (mkIV v.lo u.hi)) 6) S))
          let S' := stepNext d j v u S
          nts := nts.push (fh d.pi (mkPt d j u) S')
          S := S'
        i := i + 1
  cks := cks.set! i (some S)
  return ⟨nodes, cts, nts, cks, chunks⟩

/-- The nodes `i, …, i + k` of an array. -/
def nodesFromA (a : Array (IV 128)) (i k : Nat) : List (IV 128) := (List.range (k + 1)).map fun m => a[i + m]!

def tupsFromA (a : Array Tup) (i k : Nat) : List Tup := (List.range k).map fun m => a[i + m]!

def ckOf (t : TableOut) (i : Nat) : SState := (t.cks[i]!).getD emptyState

/-- The native run of the check of a chunk. -/
def chunkOKNative (d : BasisData) (t : TableOut) (c : Nat × Nat × Nat) : Bool :=
  let (j, i, L) := c
  if j = 0 then innerCheck d.pi (nodesFromA t.nodes i L) (tupsFromA t.cts i L) (tupsFromA t.nts i L)
  else chunkCheck d j (ckOf t i) (nodesFromA t.nodes i L) (tupsFromA t.cts i L) (tupsFromA t.nts i L) (ckOf t (i + L))

/-- The table seen by the interval queries. -/
def iTable (t : TableOut) : ITable := ⟨t.cts.size, fun i => t.nodes[i]!, fun i => t.cts[i]!⟩

/-! ### Core cells (A2) -/

/-- The core cells of segment `j`: `n = ⌈(κ_{j+1} - κ_j)/.00022⌉` cells `[x_i.lo, x_{i+1}.hi]`,
`x_i = κ_j + (κ_{j+1} - κ_j) i/n`. -/
def coreCells (d : BasisData) (j : Nat) : List (IV 128) :=
  let aa := knotIV d j
  let bb := knotIV d (j + 1)
  let len := bb.hi.mag - aa.lo.mag
  let n := max 1 ((len * 100000 + 22 * 2 ^ 128 - 1) / (22 * 2 ^ 128))
  let x := fun i => if i = 0 then aa else IV.add aa (IV.divNat (IV.mulNat (IV.sub bb aa) i) n)
  (List.range n).map fun i => (⟨(x i).lo, (x (i + 1)).hi⟩ : IV 128)

/-! ### Printing -/

def sintS (a : SInt) : String := s!"⟨{a.isNeg}, {a.mag}⟩"

def ivS (a : IV 128) : String := s!"⟨{sintS a.lo}, {sintS a.hi}⟩"

def listS {α : Type} (f : α → String) (l : List α) : String := "[" ++ ", ".intercalate (l.map f) ++ "]"

def tupS (t : Tup) : String :=
  s!"⟨{ivS t.f0}, {ivS t.f1}, {ivS t.f2}, {ivS t.e0}, {ivS t.e1}, {ivS t.e2}⟩"

def stateS (s : SState) : String := s!"⟨{ivS s.s1}, {ivS s.s2}, {listS ivS s.hs}⟩"

def modeS (m : ModeData) : String :=
  s!"⟨{m.k}, {ivS m.sc}, {ivS m.t0}, {ivS m.t1}, {ivS m.t2}, {listS ivS m.edge}, {ivS m.vr}, {ivS m.va}, {ivS m.vb}⟩"

/-- The width `hi - lo` of an interval, in units of `2^-128` (as a float exponent of ten, for reports). -/
def widthE (a : IV 128) : Float :=
  let w : Int := a.hi.toInt - a.lo.toInt
  Float.ofInt w / 2.0 ^ 128.0

def ivF (a : IV 128) : Float := (Float.ofInt a.lo.toInt + Float.ofInt a.hi.toInt) / 2.0 / 2.0 ^ 128.0

def header (title : String) (imports : List String) (doc : String) : String :=
  "/-\nCopyright (c) 2026 Scott Armstrong. All rights reserved.\nReleased under Apache 2.0 license as described in " ++
  "the file LICENSE.\nAuthors: Scott Armstrong, Sylvia Serfaty\n-/\nmodule\n\n" ++
  String.join (imports.map fun m => s!"public import {m}\n") ++
  s!"\n/-!\n# {title}\n\n{doc}\n-/\n\n"

def writeFile (path : System.FilePath) (s : String) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path s

def timeit {α : Type} (label : String) (act : IO α) : IO α := do
  let t0 ← IO.monoMsNow
  let a ← act
  let t1 ← IO.monoMsNow
  IO.println s!"[{label}] {t1 - t0} ms"
  return a

/-! ### Emission -/

def opens : String :=
  "open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table\n" ++
  "open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble\n"

/-- A data module (`@[expose]`: the kernel unfolds its literals from the shards). -/
def dataModule (title : String) (imports : List String) (doc body : String) : String :=
  header title imports doc ++ "@[expose] public section\n\nnamespace SandierSerfaty.CertData\n\n" ++ opens ++
    "\n" ++ body ++ "end SandierSerfaty.CertData\n"

/-- A shard or proof module. -/
def proofModule (title : String) (imports : List String) (doc body : String) : String :=
  header title imports doc ++ "public section\n\nnamespace SandierSerfaty.CertData\n\n" ++ opens ++ "\n" ++ body ++
    "end SandierSerfaty.CertData\n"

/-- A binary `cond` tree on the variable `var` over the leaves `lo, …, hi - 1` (one leaf per line). -/
def treeS (var : String) (leaf : Nat → String) : Nat → Nat → Nat → String
  | 0, lo, _ => "\n    " ++ leaf lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then "\n    " ++ leaf lo
    else
      let mid := (lo + hi) / 2
      s!"cond (Nat.blt {var} {mid}) ({treeS var leaf fuel lo mid}) ({treeS var leaf fuel mid hi})"

def blockDef (doc name ty : String) (entries : Array String) : String :=
  s!"/-- {doc} -/\ndef {name} (k : Nat) : {ty} :=\n  " ++
    treeS "k" (fun i => entries[i]!) 64 0 entries.size ++ "\n\n"

def listLines (f : IV 128 → String) (l : List (IV 128)) (perLine : Nat) : String := Id.run do
  let mut s := "["
  let mut i := 0
  for x in l do
    if i > 0 then s := s ++ ","
    if i % perLine = 0 then s := s ++ "\n    "
    else s := s ++ " "
    s := s ++ f x
    i := i + 1
  return s ++ "]"

def pad (n w : Nat) : String := let s := toString n; "".pushn '0' (w - s.length) ++ s

def certPath (out rel : String) : System.FilePath := (out : System.FilePath) / "SandierSerfaty" / "CertData" / rel

def modName (rel : String) : String := "SandierSerfaty.CertData." ++ rel

def basisDoc : String :=
  "The literal constants of the basis (generated by `lake exe certgen`; untrusted until checked): the\n" ++
  "enclosures `pI ∋ p`, `rI ∋ R₀`, the checked square root `[s3lo, s3hi]/2^128 ∋ √3`, the coefficient\n" ++
  "blocks `cosB1, …, cosB5` of assertion A1 (`c_1, …, c_38`) and the basis constants `dLit`. Their checks:\n" ++
  "`SandierSerfaty.CertData.Coeff.*`, `SandierSerfaty.CertData.BasisValid`."

def emitBasis (out : String) (blocks : List (List (IV 128))) (rowsAll : List (Array (List (IV 128)))) (d : BasisData) :
    IO Unit := do
  let mut body := s!"/-- An enclosure of `p = (1/12)^(1/4)`. -/\ndef pI : IV 128 := {ivS pI}\n\n" ++
    s!"/-- An enclosure of `R₀ = (4/27)^(1/4)`. -/\ndef rI : IV 128 := {ivS rI}\n\n" ++
    s!"/-- The checked square root `[s3lo, s3hi]/2^128` of `3`. -/\ndef s3lo : Nat := {s3.1}\n\ndef s3hi : Nat := {s3.2}\n\n"
  let mut k := 1
  for (b, cs) in coeffBlocks.zip blocks do
    body := body ++ s!"/-- Enclosures of `c_{b.1}, …, c_{b.1 + b.2.1 - 1}` (box `|n|, |q| ≤ {b.2.2}`). -/\n" ++
      s!"def cosB{k} : List (IV 128) := {listLines ivS cs 1}\n\n"
    k := k + 1
  body := body ++ "/-- The enclosures of `c_1, …, c_38`. -/\ndef cosAll : List (IV 128) := " ++
    " ++ ".intercalate ((List.range blocks.length).map fun i => s!"cosB{i + 1}") ++ "\n\n"
  let mut i := 1
  for m in d.modes do
    body := body ++ s!"/-- The constants of mode `{i}`. -/\ndef mode{i} : ModeData :=\n  {modeS m}\n\n"
    i := i + 1
  body := body ++ "/-- The basis constants (`mkData piIV pI rI cosAll`, rounded as computed). -/\ndef dLit : BasisData :=\n  ⟨" ++
    s!"{ivS d.pi},\n    {ivS d.p},\n    {ivS d.pc},\n    {ivS d.p2},\n    {ivS d.r0},\n    {ivS d.r1},\n    " ++
    s!"{ivS d.g0},\n    {ivS d.g1},\n    {ivS d.g2},\n    [" ++
    ", ".intercalate ((List.range d.modes.length).map fun i => s!"mode{i + 1}") ++ "]⟩\n\n"
  writeFile (certPath out "Basis.lean") (dataModule "The basis constants of the certificate (data)"
    ["SandierSerfaty.Certificate.Basis.Data", "SandierSerfaty.Certificate.Assemble.Defs"] basisDoc body)
  -- the row checkpoints
  let mut rb := ""
  k := 1
  for (b, cks) in coeffBlocks.zip rowsAll do
    rb := rb ++ s!"/-- The row checkpoints of block {k} (modes from `{b.1}`, box `|n|, |q| ≤ {b.2.2}`). -/\n" ++
      s!"def rowCk{k} (c : Nat) : List (IV 128) :=\n  " ++
      treeS "c" (fun i => listS ivS cks[i]!) 64 0 cks.size ++ "\n\n"
    k := k + 1
  writeFile (certPath out "Coeff/Rows.lean") (dataModule "The row checkpoints of assertion A1 (data)"
    [modName "Basis"] "The accumulators of the box sums after each row (`Assemble.rowB`), as computed by the generator." rb)
  -- the shards, one module per block
  k := 1
  let mut agg := ""
  for b in coeffBlocks do
    let D := b.2.2
    let R := rowsPerDecl b
    let mut sb := ""
    let mut c := 0
    let mut starts : Array (Nat × Nat) := #[]
    while c < 2 * D + 1 do
      let r := min R (2 * D + 1 - c)
      sb := sb ++ s!"theorem rows_b{k}_{c} : rowsB {b.1} {D} {b.2.1} rowCk{k} {c} {r} = true := by\n  decide +kernel\n\n"
      starts := starts.push (c, r)
      c := c + r
    sb := sb ++ s!"theorem fin_b{k} : coeffFinB s3lo s3hi {b.1} {D} rowCk{k} cosB{k} = true := by\n  decide +kernel\n\n"
    writeFile (certPath out s!"Coeff/B{k}.lean") (proofModule s!"Assertion A1, block {k} (kernel shards)"
      [modName "Coeff.Rows"] s!"`decide +kernel` shards: the rows of the box `|n|, |q| ≤ {D}` for the modes from `{b.1}` ({R} rows per declaration), and the final enclosure test." sb)
    -- the aggregation term
    let mut term := s!"rowsB_sound rows_b{k}_0"
    for (c0, _) in starts.toList.drop 1 do
      term := s!"rows_extend ({term}) rows_b{k}_{c0}"
    agg := agg ++ s!"/-- Assertion A1, block {k}: `cosB{k}` encloses `c_{b.1}, …, c_{b.1 + b.2.1 - 1}`. -/\n" ++
      s!"theorem cosB{k}_encl : EnclFrom SandierSerfaty.Calibration.coeff {b.1} cosB{k} :=\n  coeffs_of_rows (cnt := {b.2.1}) (by norm_num) (by norm_num)\n" ++
      s!"    (fun c hc => ({term}) c (Nat.zero_le c) (by omega)) fin_b{k}\n\n"
    k := k + 1
  writeFile (certPath out "Coeff/Encl.lean") (proofModule "Assertion A1: the coefficient enclosures"
    (((List.range coeffBlocks.length).map fun i => modName s!"Coeff.B{i + 1}") ++ ["SandierSerfaty.Certificate.Assemble.Coeff"])
    "The row shards of each block joined (`Assemble.rows_extend`) and passed to `Assemble.coeffs_of_rows`." agg)

/-- Core cells per declaration, by segment (measured: a core cell of segment 2 costs about 0.6 GB). -/
def corePer (j : Nat) : Nat := [32, 8, 3, 8, 8, 8].getD j 3

/-- The core cells, in pieces of `corePer j` cells: `(segment, piece index, cells)`. -/
def corePieces (d : BasisData) : List (Nat × Nat × List (IV 128)) := Id.run do
  let mut out := []
  for j in [0:6] do
    let per := corePer j
    let cells := coreCells d j
    let np := (cells.length + per - 1) / per
    for k in [0:np] do
      out := out ++ [(j, k, (cells.drop (k * per)).take per)]
  return out

def emitCore (out : String) (d : BasisData) (perMod : Nat) : IO (List String) := do
  let pieces := corePieces d
  let mut body := ""
  for (j, k, cs) in pieces do
    body := body ++ s!"def core_{j}_{k} : List (IV 128) := {listLines ivS cs 4}\n\n"
  for j in [0:6] do
    let ks := (pieces.filter (·.1 == j)).map (·.2.1)
    body := body ++ s!"/-- The core cells of segment `{j}`. -/\ndef coreSeg{j} : List (IV 128) := " ++
      " ++ ".intercalate (ks.map fun k => s!"core_{j}_{k}") ++ "\n\n"
  writeFile (certPath out "Core/Cells.lean") (dataModule "The cells of the finite-core test A2 (data)"
    [modName "Basis"] ("The cells covering each segment `[κ_j, κ_{j+1}]` (step `.00022`), in pieces (one " ++
      "`decide +kernel` declaration each; `32/8/3/8/8/8` cells per piece on the segments `0, …, 5`).") body)
  let mut mods := []
  let mut m := 0
  let mut rest := pieces
  while !rest.isEmpty do
    let grp := rest.take perMod
    rest := rest.drop perMod
    let mut sb := ""
    for (j, k, _) in grp do
      sb := sb ++ s!"theorem core_{j}_{k}_ok : allCells dLit {j} core_{j}_{k} = true := by\n  decide +kernel\n\n"
    let rel := s!"Core/S{pad m 2}"
    writeFile (certPath out (rel ++ ".lean")) (proofModule s!"Assertion A2, shard {m} (kernel)" [modName "Core.Cells"]
      "`decide +kernel` shards of the finite-core test on pieces of the core cells." sb)
    mods := mods ++ [modName (rel.replace "/" ".")]
    m := m + 1
  -- the assembly: covering, segment checks, the finite core
  let mut vb := "/-- The core cells, by segment. -/\ndef coreSeg : Nat → List (IV 128)\n" ++
    String.join ((List.range 5).map fun j => s!"  | {j} => coreSeg{j}\n") ++ "  | _ => coreSeg5\n\n"
  for j in [0:6] do
    let ks := (pieces.filter (·.1 == j)).map (·.2.1)
    let mut term := s!"core_{j}_{ks.headD 0}_ok"
    for k in ks.drop 1 do
      term := s!"allCells_append_of ({term}) core_{j}_{k}_ok"
    vb := vb ++ s!"theorem cover_{j} : coverB (knotIV dLit {j}).lo (knotIV dLit {j + 1}).hi coreSeg{j} = true := by\n  decide +kernel\n\n" ++
      s!"theorem coreSeg_{j}_ok : coreSegCheck dLit {j} (coreSeg {j}) = true := by\n  simp only [coreSegCheck, Bool.and_eq_true]\n" ++
      s!"  exact ⟨cover_{j}, {term}⟩\n\n"
  vb := vb ++ "/-- **Assertion A2**: the finite-core premise `Tails.FiniteCore` (`tail:finite-core-premise`). -/\n" ++
    "theorem finiteCore : SandierSerfaty.Tails.FiniteCore := by\n" ++
    "  have hc : ∀ j, j ≤ 5 → coreSegCheck dLit j (coreSeg j) = true := by\n    intro j hj\n" ++
    "    obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega\n" ++
    "    exacts [coreSeg_0_ok, coreSeg_1_ok, coreSeg_2_ok, coreSeg_3_ok, coreSeg_4_ok, coreSeg_5_ok]\n" ++
    "  exact ⟨abs_coeff_one_lt, fun j hj t ht hb hl => (coreBounds_of_checks dLit_valid hc j hj t ht hb hl).1,\n" ++
    "    fun j hj t ht hb hl => (coreBounds_of_checks dLit_valid hc j hj t ht hb hl).2⟩\n\n"
  writeFile (certPath out "Core/Valid.lean") (proofModule "Assertion A2: the finite core"
    (mods ++ [modName "BasisValid", "SandierSerfaty.Certificate.Assemble.Lists", "SandierSerfaty.Certificate.Basis.CoreSound",
      "SandierSerfaty.Tails.RetainedCore"])
    "The pieces joined (`Assemble.allCells_append_of`), the covering checks, and `Tails.FiniteCore` from `Basis.coreBounds_of_checks`." vb)
  return mods

/-- The estimated kernel seconds of one step of segment `j` (measured, rounded up). -/
def stepCost (j : Nat) : Nat := [1, 6, 13, 6, 6, 6].getD j 13

def emitTable (out : String) (d : BasisData) (t : TableOut) (budget : Nat) : IO (List String) := do
  let mut segMods : Array (List String) := Array.replicate 6 []
  let nb := (t.nodes.size + 63) / 64
  let nq := (nb + 1) / 2
  let ckDefault := stateS emptyState
  for q in [0:nq] do
    let mut body := ""
    for b in [2 * q:min (2 * q + 2) nb] do
      let ns := (t.nodes.extract (64 * b) (64 * b + 64)).map ivS
      body := body ++ blockDef s!"The nodes `{64 * b} + k`." s!"nodeB_{b}" "IV 128" ns
      let cs := (t.cts.extract (64 * b) (64 * b + 64)).map tupS
      if cs.size > 0 then
        body := body ++ blockDef s!"The cell tuples `{64 * b} + k`." s!"ctB_{b}" "Tup" cs
        body := body ++ blockDef s!"The node tuples `{64 * b} + k` (at the node `{64 * b} + k + 1`)." s!"ntB_{b}" "Tup"
          ((t.nts.extract (64 * b) (64 * b + 64)).map tupS)
      let cks := (t.cks.extract (64 * b) (64 * b + 64)).map fun o => (o.map stateS).getD ckDefault
      body := body ++ blockDef s!"The checkpoints at the nodes `{64 * b} + k` (the trivial state where none is read)."
        s!"ckB_{b}" "SState" cks
    writeFile (certPath out s!"Table/Page{pad q 2}.lean") (dataModule s!"The radial table, page {q} (data)"
      ["SandierSerfaty.Certificate.Assemble.Defs"]
      s!"Nodes, cell tuples, node tuples and checkpoints of the blocks `{2 * q}`, `{2 * q + 1}` (`64` entries each)." body)
  -- the dispatch module
  let ncb := (t.cts.size + 63) / 64
  let mut body := ""
  body := body ++ "/-- The nodes, by block. -/\ndef nodeBlk (b k : Nat) : IV 128 :=\n  " ++
    treeS "b" (fun i => s!"nodeB_{i} k") 64 0 nb ++ "\n\n/-- The node `i`. -/\ndef nodeAt (i : Nat) : IV 128 := nodeBlk (Nat.div i 64) (Nat.mod i 64)\n\n"
  body := body ++ "/-- The cell tuples, by block. -/\ndef ctBlk (b k : Nat) : Tup :=\n  " ++
    treeS "b" (fun i => s!"ctB_{i} k") 64 0 ncb ++ "\n\n/-- The cell tuple `i`. -/\ndef ctAt (i : Nat) : Tup := ctBlk (Nat.div i 64) (Nat.mod i 64)\n\n"
  body := body ++ "/-- The node tuples, by block. -/\ndef ntBlk (b k : Nat) : Tup :=\n  " ++
    treeS "b" (fun i => s!"ntB_{i} k") 64 0 ncb ++ "\n\n/-- The node tuple `i` (at the node `i + 1`). -/\ndef ntAt (i : Nat) : Tup := ntBlk (Nat.div i 64) (Nat.mod i 64)\n\n"
  body := body ++ "/-- The checkpoints, by block. -/\ndef ckBlk (b k : Nat) : SState :=\n  " ++
    treeS "b" (fun i => s!"ckB_{i} k") 64 0 nb ++ "\n\n/-- The checkpoint at the node `i`. -/\ndef ckAt (i : Nat) : SState := ckBlk (Nat.div i 64) (Nat.mod i 64)\n\n"
  body := body ++ s!"/-- The number of cells. -/\ndef tblN : Nat := {t.cts.size}\n\n"
  body := body ++ "/-- The node index of the knot `κ_j`. -/\ndef knotCell : Nat → Nat\n" ++
    String.join ((List.range 6).map fun j => s!"  | {j} => {knotIdx d j}\n") ++ s!"  | _ => {knotIdx d 6}\n\n"
  body := body ++ "/-- The chunk length (cells per declaration) of segment `j`. -/\ndef chunkLenAt : Nat → Nat\n" ++
    String.join ((List.range 5).map fun j => s!"  | {j} => {chunkLen j}\n") ++ s!"  | _ => {chunkLen 5}\n\n"
  body := body ++ "/-- The number of chunks of segment `j`. -/\ndef chunkCnt : Nat → Nat\n" ++
    String.join ((List.range 5).map fun j => s!"  | {j} => {segCells d j / chunkLen j}\n") ++
    s!"  | _ => {segCells d 5 / chunkLen 5}\n\n"
  body := body ++ "/-- The table seen by the interval queries. -/\ndef iTbl : ITable := ⟨tblN, nodeAt, ctAt⟩\n\n"
  writeFile (certPath out "Table/Data.lean") (dataModule "The radial table (dispatch)"
    (((List.range nq).map fun q => modName s!"Table.Page{pad q 2}") ++ [modName "Basis", "SandierSerfaty.Certificate.Assemble.Defs"])
    ("The global accessors `nodeAt`, `ctAt`, `ntAt`, `ckAt` of the table (binary `cond` trees over the blocks of the\n" ++
      "pages), the number of cells `tblN`, the knot cells `knotCell j`.") body)
  -- the nodes / init shard
  let k1 := knotIdx d 1
  let nb2 := "/-- Node separation, nondegeneracy and the knots. -/\ntheorem nodes_ok : nodesB dLit nodeAt knotCell tblN = true := by\n  decide +kernel\n\n" ++
    s!"/-- The initial checkpoint at `p - c`. -/\ntheorem init_ok : initCheck dLit (nodeAt {k1}) (ckAt {k1}) = true := by\n  decide +kernel\n\n"
  writeFile (certPath out "Table/Nodes.lean") (proofModule "The nodes and the initial checkpoint (kernel shard)"
    [modName "Table.Data"] "`decide +kernel` shards: `nodesB` and the initial checkpoint." nb2)
  -- chunk shards
  let mut mods := []
  let mut m := 0
  let mut g := 0
  let G := t.chunks.size
  while g < G do
    -- one module: consecutive chunks of one segment, up to `budget` estimated kernel seconds
    let j0 := t.chunks[g]!.1
    let mut g1 := g
    let mut w := 0
    while g1 < G && t.chunks[g1]!.1 == j0 && (g1 == g || w + t.chunks[g1]!.2.2 * stepCost j0 ≤ budget) do
      w := w + t.chunks[g1]!.2.2 * stepCost j0
      g1 := g1 + 1
    let mut sb := ""
    for h in [g:g1] do
      let (j, i, L) := t.chunks[h]!
      if j = 0 then
        sb := sb ++ s!"theorem chunk_{i} : innerB {L} dLit.pi nodeAt ctAt ntAt {i} = true := by\n  decide +kernel\n\n"
      else
        sb := sb ++ s!"theorem chunk_{i} : chunkB {L} dLit nodeAt ctAt ntAt ckAt {j} {i} = true := by\n  decide +kernel\n\n"
    let rel := s!"Table/S{pad m 3}"
    let (_, i0, _) := t.chunks[g]!
    let (_, i1, L1) := t.chunks[g1 - 1]!
    writeFile (certPath out (rel ++ ".lean")) (proofModule s!"The radial table, shard {m} (kernel)" [modName "Table.Data"]
      s!"`decide +kernel` shards of segment `{j0}`: the chunks of the cells `{i0}, …, {i1 + L1 - 1}` ({t.chunks[g]!.2.2} cells per declaration; estimated {w} s of kernel time)." sb)
    mods := mods ++ [modName (rel.replace "/" ".")]
    segMods := segMods.modify j0 (· ++ [modName (rel.replace "/" ".")])
    m := m + 1
    g := g1
  -- the chains, one module per segment
  for j in [0:6] do
    let L := chunkLen j
    let cnt := segCells d j / L
    let k0 := knotIdx d j
    let pdef := if j = 0 then
        s!"/-- The check of the chunk `c` of segment `0`. -/\nabbrev SegP0 (c : Nat) : Prop :=\n  innerB (chunkLenAt 0) dLit.pi nodeAt ctAt ntAt (knotCell 0 + chunkLenAt 0 * c) = true\n\n"
      else
        s!"/-- The check of the chunk `c` of segment `{j}`. -/\nabbrev SegP{j} (c : Nat) : Prop :=\n  chunkB (chunkLenAt {j}) dLit nodeAt ctAt ntAt ckAt {j} (knotCell {j} + chunkLenAt {j} * c) = true\n\n"
    let mut pf := s!"/-- **All chunks of segment `{j}`** ({cnt} chunks of {L} cells). -/\ntheorem seg{j}_chunks : ∀ c, c < chunkCnt {j} → SegP{j} c := by\n  have h0 : ∀ c, c < 0 → SegP{j} c := forall_lt_zero'\n"
    for c in [0:cnt] do
      pf := pf ++ s!"  have h{c + 1} : ∀ c, c < {c + 1} → SegP{j} c := forall_lt_succ_of h{c} chunk_{k0 + L * c}\n"
    pf := pf ++ s!"  exact h{cnt}\n\n"
    writeFile (certPath out s!"Table/Seg{j}.lean") (proofModule s!"The chunks of segment {j}, joined"
      (segMods[j]! ++ ["SandierSerfaty.Certificate.Assemble.Lists"])
      s!"The shard theorems of segment `{j}` joined into one statement over all its chunks (`Assemble.forall_lt_succ_of`)." (pdef ++ pf))
  return mods

def lamN : Nat := 64

def lamRad : Nat := (2 ^ 128 + 10 ^ 11 - 1) / 10 ^ 11

def emitExterior (out : String) (d : BasisData) (t : TableOut) : IO Bool := do
  match lamEnc (iTable t) d lamN lamRad with
  | none => IO.println "lamEnc failed"; return false
  | some I =>
    let n := t.cts.size
    let iR := knotIdx d 3 - 1
    let body := s!"/-- The widening `⌈2^128/10^11⌉` (the infinite-mode error, `Tails.uniform_error_of_finiteCore`). -/\n" ++
      s!"def lamRad : Nat := {lamRad}\n\n/-- The coarse enclosure of `λ` (`lamEnc iTbl dLit {lamN} lamRad`, as computed). -/\n" ++
      s!"def lamLit : IV 128 := {ivS I}\n\n"
    writeFile (certPath out "Exterior/Data.lean") (dataModule "The enclosure of λ (data)" [modName "Table.Data"]
      "The literal enclosure of `λ` and the widening radius of the exterior test A6." body)
    let body := s!"/-- The `λ` quadrature returns the literal enclosure. -/\ntheorem lam_ok : optEqB (lamEnc iTbl dLit {lamN} lamRad) lamLit = true := by\n  decide +kernel\n\n" ++
      s!"/-- The exterior test A6 on the node tuples at `l` (node `{n}`) and `R₀` (node `{iR + 1}`). -/\n" ++
      s!"theorem a6_ok : a6Check dLit.pi dLit.r0 (IV.addRad (ntAt {n - 1}).f0 lamRad) (IV.addRad (ntAt {iR}).f0 lamRad)\n" ++
      s!"    (IV.addRad (ntAt {iR}).e0 lamRad) (IV.addRad (basis dLit 5 (knotIV dLit 6)).bsum.c0 lamRad) lamLit = true := by\n  decide +kernel\n\n"
    writeFile (certPath out "Exterior/Checks.lean") (proofModule "The λ enclosure and the exterior test A6 (kernel shard)"
      [modName "Exterior.Data", "SandierSerfaty.Certificate.Query.Const"]
      "`decide +kernel` shards: `lamEnc` on the whole table, and `a6Check`." body)
    return true

def run (out : String) (quick : Bool) (budget corePerMod : Nat) : IO Bool := do
  IO.println s!"pI ok: {fourthRootOK 1 12 pI}, rI ok: {fourthRootOK 4 27 rI}, s3 ok: {IV.sqrtCheck (IV.ofNat 3 : IV 128) s3.1 s3.2}"
  let rowsAll := coeffBlocks.map rowCks
  let blocks := (coeffBlocks.zip rowsAll).map fun (b, cks) => coeffBlockOf b cks
  let cos := blocks.foldl (· ++ ·) []
  IO.println s!"{cos.length} coefficients; c1 ≈ {ivF (cos.headD default)}, width {widthE (cos.headD default)}"
  IO.println s!"dataOK: {dataOK pI rI cos}"
  let d := mkData piLit pI rI cos
  IO.println s!"modes: {d.modes.length}"
  let segs := (List.range 6).map (segCells d)
  IO.println s!"cells per segment: {segs}, knot indices: {(List.range 7).map (knotIdx d)}"
  let t ← timeit "table" (do let t := buildTable d; IO.println s!"{t.cts.size} cells"; pure t)
  if let some o := ← CertGen.Box.request out then return ← CertGen.Box.entry out (some o) d t.nodes t.cts t.nts ((List.range 7).map (knotIdx d))
  let G := t.chunks.size
  let mut bad : Array Nat := #[]
  let t0 ← IO.monoMsNow
  for c in t.chunks do
    if !quick && !(chunkOKNative d t c) then bad := bad.push c.2.1
  let t1 ← IO.monoMsNow
  IO.println s!"chunk checks: {G} chunks, failing {bad.toList.take 20} ({t1 - t0} ms)"
  let n := t.cts.size
  for i in [0:7] do
    let k := knotIdx d i
    if k > 0 then
      let nt := t.nts[k - 1]!
      IO.println s!"node {k}: f0 ≈ {ivF nt.f0} (w {widthE nt.f0}), f1 ≈ {ivF nt.f1} (w {widthE nt.f1}), e0 ≈ {ivF nt.e0} (w {widthE nt.e0}), e1 w {widthE nt.e1}"
  let ckL := ckOf t t.cts.size
  IO.println s!"final state widths: s1 {widthE ckL.s1}, s2 {widthE ckL.s2}, h0 {widthE (ckL.hs.headD default)}"
  IO.println s!"initCheck: {initCheck d d.pc (ckOf t (knotIdx d 1))}"
  -- core cells
  let mut coreBad : Array (Nat × Nat) := #[]
  let mut coreN := 0
  let t2 ← IO.monoMsNow
  for j in [0:6] do
    let cells := coreCells d j
    coreN := coreN + cells.length
    if !(coverB (knotIV d j).lo (knotIV d (j + 1)).hi cells) then coreBad := coreBad.push (j, 999999)
    for i in [0:cells.length] do
      if !(coreCellCheck d j cells[i]!) then coreBad := coreBad.push (j, i)
  let t3 ← IO.monoMsNow
  IO.println s!"core cells: {coreN}, failing {coreBad.toList.take 20} ({t3 - t2} ms)"
  -- λ and A6
  let T := iTable t
  let rad := (2 ^ 128 + 10 ^ 11 - 1) / 10 ^ 11
  for N in [16, 32, 64, 128] do
    match lamEnc T d N rad with
    | some I =>
      let nR := t.nts[knotIdx d 3 - 1]!
      let nL := t.nts[n - 1]!
      let X := knotIV d 6
      let ok := a6Check d.pi d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad)
        (IV.addRad (basis d 5 X).bsum.c0 rad) I
      let fl := fLEnc d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad) I
      let sl := slopeEnc d.pi (IV.addRad (basis d 5 X).bsum.c0 rad) I
      IO.println s!"N = {N}: λ ∈ [{Float.ofInt I.lo.toInt / 2.0 ^ 128.0}, {Float.ofInt I.hi.toInt / 2.0 ^ 128.0}], a6 {ok}, f(l) ≥ {Float.ofInt fl.lo.toInt / 2.0 ^ 128.0}, slope ≥ {Float.ofInt sl.lo.toInt / 2.0 ^ 128.0}"
    | none => IO.println s!"N = {N}: lamEnc failed"
  if !(bad.isEmpty && coreBad.isEmpty) then return false
  emitBasis out blocks rowsAll d
  let coreMods ← emitCore out d corePerMod
  let tblMods ← emitTable out d t budget
  let ok ← emitExterior out d t
  IO.println s!"core shard modules: {coreMods.length}, table shard modules: {tblMods.length}"
  return ok

end CertGen


open CertGen

def main (args : List String) : IO UInt32 := do
  let out := args.headD "."
  let quick := args.contains "--quick"
  let nums := (args.drop 1).filterMap String.toNat?
  let ok ← CertGen.run out quick (nums.getD 0 180) (nums.getD 1 8)
  return (if ok then 0 else 1)
