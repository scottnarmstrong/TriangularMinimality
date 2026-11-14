/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Emit

/-!
# Emission of the box shards (untrusted)

The `decide +kernel` shard modules of the box assertions and their aggregation (see `CertGen.Box` in
`Gen/Emit.lean` for the layout). Each statement is evaluated natively first, on the index functions decoded from
the packed literals exactly as the shards read them (`unpack`), with the checkpoints computed by the same `SInt`
and `IV` operations as the loops (`stepAcc`, `stepHess`).
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-- The native grids with the index functions decoded from the packed literals. -/
def nativeGrids (r : BoxOut) : OuterGrid × NegGrid × KGrid :=
  let pO := r.rO.map fun x => packNat x.idx
  let pN := r.rN.map fun x => packNat x.idx
  let pK := packNat r.rK.idx
  (⟨r.gO.nd, r.gO.nx, gridD3 r.gO.d1 r.gO.d2 r.gO.d3, gridS3 r.gO.s1 r.gO.s2 r.gO.s3, fun j k => unpack pO[j]! k,
      r.gO.d1, r.gO.d1 + r.gO.d2, r.gO.s1, r.gO.s1 + r.gO.s2, sintOfInt r.thrO⟩,
    ⟨r.gN.nd, r.gN.nx, gridD3 r.gN.d1 r.gN.d2 r.gN.d3, gridS3 r.gN.s1 r.gN.s2 r.gN.s3, fun j k => unpack pN[j]! k,
      sintOfInt r.thrN⟩,
    ⟨r.mK, r.dK, kS r.XK r.mK, fun k => unpack pK k, sintOfInt r.rK.sumQ⟩)

/-- The accumulator after the cells `k, …, k + n - 1` (mode `0`: values, `1`: negative parts), by the loops' own
operations. -/
def stepAcc (neg : Bool) (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (k n : Nat) (acc : SInt) :
    SInt := Id.run do
  let mut a := acc
  for i in [k:k + n] do
    match midVal E idx dm sm i with
    | none => pure ()
    | some v => a := SInt.add a (SInt.mul ⟨false, widthM sm i⟩ (if neg then negPart v else v.v))
  return a

/-- One module of value rows: segments, rows, the block. `kind` is `o` (outer) or `n` (negative part). -/
def valueModule (kind : String) (E : EvalData) (G : OuterGrid) (Gr : NegGrid) (L a b : Nat) :
    IO (String × String) := do
  let gname := if kind == "o" then "oGrid" else "nGrid"
  let mut body := ""
  let mut rowNames : Array String := #[]
  for j in [a:b] do
    let nx := if kind == "o" then G.nx else Gr.nx
    let ps := pieces nx L
    let mut acc := SInt.zero
    let mut names : Array String := #[]
    for (k, len) in ps do
      let nm := s!"{kind}_{j}_{k}"
      names := names.push nm
      let last := k + len == nx
      if kind == "o" then
        let inRow := inRowB G.jl G.jr j
        let args := s!"evalE (oGrid.idx {j}) (oGrid.dm {j}) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr {j}) oGrid.kl oGrid.kr {len} {k} {sintS acc}"
        if last then
          must (outerLoop E (G.idx j) (G.dm j) G.sm G.thr inRow G.kl G.kr len k acc) nm
          body := body ++ s!"theorem {nm} : outerLoop {args} = true := by\n  decide +kernel\n\n"
        else
          let acc' := stepAcc false E (G.idx j) (G.dm j) G.sm k len acc
          must (outerSeg E (G.idx j) (G.dm j) G.sm G.thr inRow G.kl G.kr len k acc acc') nm
          body := body ++ s!"theorem {nm} : outerSeg {args} {sintS acc'} = true := by\n  decide +kernel\n\n"
          acc := acc'
      else
        let args := s!"evalE (nGrid.idx {j}) (nGrid.dm {j}) nGrid.sm"
        if last then
          must (negLoop E (Gr.idx j) (Gr.dm j) Gr.sm Gr.thr len k acc) nm
          body := body ++ s!"theorem {nm} : negLoop {args} nGrid.thr {len} {k} {sintS acc} = true := by\n  decide +kernel\n\n"
        else
          let acc' := stepAcc true E (Gr.idx j) (Gr.dm j) Gr.sm k len acc
          must (negSeg E (Gr.idx j) (Gr.dm j) Gr.sm len k acc acc') nm
          body := body ++ s!"theorem {nm} : negSeg {args} {len} {k} {sintS acc} {sintS acc'} = true := by\n  decide +kernel\n\n"
          acc := acc'
    let lem := if kind == "o" then "outerLoop_of_seg" else "negLoop_of_seg"
    body := body ++ s!"theorem {kind}_row_{j} : {gname}.row evalE {j} = true :=\n  {segChain lem names nx}\n\n"
    rowNames := rowNames.push s!"{kind}_row_{j}"
  let blk := s!"{kind}_blk_{a}"
  body := body ++ s!"theorem {blk} : allFrom (fun j => {gname}.row evalE j) {a} {b - a} = true :=\n  " ++
    consChain s!"fun j => {gname}.row evalE j" a rowNames ++ "\n\n"
  return (body, blk)

/-- The A7 rows `a, …, b - 1` in blocks of `B` rectangles (checked index `aIx`). -/
def a7Module (A : A7Data) (ix : Nat → Nat → Nat × Nat) (B a b : Nat) : IO (String × String) := do
  let mut body := ""
  let mut rowNames : Array String := #[]
  for j in [a:b] do
    let mut blocks : Array (String × Nat × Nat) := #[]
    for (k, len) in pieces A.nk B do
      let nm := s!"a7_{j}_{k}"
      must (allFrom (A.rectI ix j) k len) nm
      body := body ++ s!"theorem {nm} : allFrom (a7Dat.rectI aIx {j}) {k} {len} = true := by\n  decide +kernel\n\n"
      blocks := blocks.push (nm, k, len)
    body := body ++ s!"theorem a7_row_{j} : a7Dat.rowI aIx {j} a7Dat.nk = true :=\n  (a7rowI_eq_allLt a7Dat aIx {j} a7Dat.nk).trans\n    {addChain s!"a7Dat.rectI aIx {j}" blocks}\n\n"
    rowNames := rowNames.push s!"a7_row_{j}"
  let blk := s!"a7_blk_{a}"
  body := body ++ s!"theorem {blk} : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) {a} {b - a} = true :=\n  " ++
    consChain "fun j => a7Dat.rowI aIx j a7Dat.nk" a rowNames ++ "\n\n"
  return (body, blk)

/-- The Hessian accumulator after the cells `i, …, i + n - 1` of row `a` (as `HessData.rowAuxG`). -/
def stepHess (H : HessData) (ctxf : Nat → Nat → Option DCtx2) (a i n : Nat) (acc : IV 128) : IV 128 := Id.run do
  let mut x := acc
  for c in [i:i + n] do
    match ctxf a c with
    | none => pure ()
    | some ctx => x := IV.add x (IV.mul (IV.ofNatPair (widthN H.sp c) (widthN H.sp c)) (gddOf ctx))
  return x

/-- The Hessian rows `a, …, b - 1` in segments of `B` cells (checked index `hIx`). -/
def hessModule (H : HessData) (ix : Nat → Nat → Nat × Nat) (B a b : Nat) : IO (String × String) := do
  let ctxf := H.ctxI ix
  let mut body := ""
  let mut rowNames : Array String := #[]
  for r in [a:b] do
    let mut acc : IV 128 := IV.ofNatPair 0 0
    let mut names : Array String := #[]
    for (i, len) in pieces H.nx B do
      let nm := s!"h_{r}_{i}"
      names := names.push nm
      if i + len == H.nx then
        must (H.rowAuxG ctxf r len i acc) nm
        body := body ++ s!"theorem {nm} : hessDat.rowAuxG (hessDat.ctxI hIx) {r} {len} {i} {ivS acc} = true := by\n  decide +kernel\n\n"
      else
        let acc' := stepHess H ctxf r i len acc
        must (hessSeg H ctxf r len i acc acc') nm
        body := body ++ s!"theorem {nm} : hessSeg hessDat (hessDat.ctxI hIx) {r} {len} {i} {ivS acc} {ivS acc'} = true := by\n  decide +kernel\n\n"
        acc := acc'
    must (Nat.ble (H.dp r) (H.dp (r + 1))) s!"h_row_{r} (d monotone)"
    body := body ++ s!"theorem h_row_{r} : hessDat.rowI hIx {r} = true :=\n  row_of_rowAux (by decide +kernel)\n    {segChain "rowAux_of_seg" names H.nx}\n\n"
    rowNames := rowNames.push s!"h_row_{r}"
  let blk := s!"h_blk_{a}"
  body := body ++ s!"theorem {blk} : allFrom (fun a => hessDat.rowI hIx a) {a} {b - a} = true :=\n  " ++
    consChain "fun a => hessDat.rowI hIx a" a rowNames ++ "\n\n"
  return (body, blk)

/-- The combined accumulators after the cells `k, …, k + n - 1` (values, negative parts). -/
def stepBoth (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (k n : Nat) (acc accN : SInt) :
    SInt × SInt := (stepAcc false E idx dm sm k n acc, stepAcc true E idx dm sm k n accN)

/-- A chain `lem (m := …) h₀ (lem (m := …) h₁ (… hₗ))` over segment proofs `hs` starting at the cells `starts`. -/
def segChainS (lem : String) (hs : Array String) (starts : Array Nat) (total : Nat) : String := Id.run do
  let mut t := hs[hs.size - 1]!
  for i in [1:hs.size] do
    let j := hs.size - 1 - i
    t := s!"({lem} (m := {total - starts[j + 1]!}) {hs[j]!} {t})"
  return t

/-- One module of rows of the common outer / negative-part grid (each value computed once, `bothSeg`): the
segments, the outer and the negative rows, the two blocks. -/
def bothModule (E : EvalData) (G : OuterGrid) (Gr : NegGrid) (L a b : Nat) : IO (String × String × String) := do
  let mut body := ""
  let mut oNames : Array String := #[]
  let mut nNames : Array String := #[]
  for j in [a:b] do
    let ps := pieces G.nx L
    let mut acc := SInt.zero
    let mut accN := SInt.zero
    let mut oh : Array String := #[]
    let mut nh : Array String := #[]
    let mut starts : Array Nat := #[]
    let inRow := inRowB G.jl G.jr j
    for (k, len) in ps do
      let nm := s!"b_{j}_{k}"
      starts := starts.push k
      let args := s!"evalE (oGrid.idx {j}) (oGrid.dm {j}) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr {j}) oGrid.kl oGrid.kr"
      if k + len == G.nx then
        must (bothLoop E (G.idx j) (G.dm j) G.sm G.thr inRow G.kl G.kr Gr.thr len k acc accN) nm
        body := body ++ s!"theorem {nm} : bothLoop {args} nGrid.thr {len} {k} {sintS acc} {sintS accN} = true := by\n  decide +kernel\n\n"
        oh := oh.push s!"(bothLoop_sound {nm}).1"
        nh := nh.push s!"(bothLoop_sound {nm}).2"
      else
        let (acc', accN') := stepBoth E (G.idx j) (G.dm j) G.sm k len acc accN
        must (bothSeg E (G.idx j) (G.dm j) G.sm G.thr inRow G.kl G.kr len k acc accN acc' accN') nm
        body := body ++ s!"theorem {nm} : bothSeg {args} {len} {k} {sintS acc} {sintS accN} {sintS acc'} {sintS accN'} = true := by\n  decide +kernel\n\n"
        oh := oh.push s!"(bothSeg_sound {nm}).1"
        nh := nh.push s!"(bothSeg_sound {nm}).2"
        acc := acc'
        accN := accN'
    body := body ++ s!"theorem o_row_{j} : oGrid.row evalE {j} = true :=\n  {segChainS "outerLoop_of_seg" oh starts G.nx}\n\n"
    body := body ++ s!"theorem n_row_{j} : nGrid.row evalE {j} = true :=\n  {segChainS "negLoop_of_seg" nh starts G.nx}\n\n"
    oNames := oNames.push s!"o_row_{j}"
    nNames := nNames.push s!"n_row_{j}"
  body := body ++ s!"theorem o_blk_{a} : allFrom (fun j => oGrid.row evalE j) {a} {b - a} = true :=\n  " ++
    consChain "fun j => oGrid.row evalE j" a oNames ++ "\n\n"
  body := body ++ s!"theorem n_blk_{a} : allFrom (fun j => nGrid.row evalE j) {a} {b - a} = true :=\n  " ++
    consChain "fun j => nGrid.row evalE j" a nNames ++ "\n\n"
  return (body, s!"o_blk_{a}", s!"n_blk_{a}")

/-- The modules `Both/Snnn` of the common grid (`per` rows each); the module names and the two block lists. -/
def emitBoth (out : String) (imports : List String) (E : EvalData) (G : OuterGrid) (Gr : NegGrid) (L per : Nat) :
    IO (List String × Array (String × Nat × Nat) × Array (String × Nat × Nat)) := do
  let n := G.nd + 1
  let mut mods := []
  let mut ob := #[]
  let mut nb := #[]
  let mut m := 0
  let mut a := 0
  while a < n do
    let b := min n (a + per)
    let (body, o, nn) ← bothModule E G Gr L a b
    let rel := s!"Both/S{pad m 3}"
    writeBox out rel (proofMod s!"The outer and negative-part rows (A8, A9), shard {m} (kernel)" imports
      s!"Segments of at most `{L}` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `{a}`–`{b - 1}`." body)
    mods := mods ++ [boxMod rel]
    ob := ob.push (o, a, b - a)
    nb := nb.push (nn, a, b - a)
    a := b
    m := m + 1
  return (mods, ob, nb)

/-- Writes a group of shard modules; returns the module names and the block theorems `(name, first row)`. -/
def emitGroup (out dir title doc : String) (imports : List String) (n per : Nat)
    (mk : Nat → Nat → IO (String × String)) : IO (List String × Array (String × Nat × Nat)) := do
  let mut mods := []
  let mut blks := #[]
  let mut m := 0
  let mut a := 0
  while a < n do
    let b := min n (a + per)
    let (body, blk) ← mk a b
    let rel := s!"{dir}/S{pad m 3}"
    writeBox out rel (proofMod s!"{title}, shard {m} (kernel)" imports s!"{doc} Rows `{a}`–`{b - 1}`." body)
    mods := mods ++ [boxMod rel]
    blks := blks.push (blk, a, b - a)
    a := b
    m := m + 1
  return (mods, blks)

end CertGen.Box
