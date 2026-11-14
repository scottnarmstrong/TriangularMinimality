/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Shards

/-!
# Emission driver of the box modules (untrusted)

`emitAll` writes every data and shard module of the box assertions (`CertGen.Box`, `Gen/Emit.lean`) and the
aggregation module `Box/Final` stating the Booleans of `Box.certificateGoal_of_checks` (`a7B`, `outerGridB`,
`negGridB`, `kRowB`, `hessB`) and the `cellCheck` conjunction of the query cells from the shards; the scalar
checks (`kcB`, `outThrB`, `negThrB`, `deltaB`, `evalCheckOf`) and the non-row conjuncts are in `Box/Checks`.
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

def tableData : String := "SandierSerfaty.CertData.Table.Data"
def extData : String := "SandierSerfaty.CertData.Exterior.Data"

def emitAll (out : String) (r : BoxOut) (nodes : Array (IV 128)) (cts nts : Array Tup) : IO Unit := do
  let S := r.S
  let (G, Gr, KG) := nativeGrids r
  let E := r.E
  let same := r.gO == r.gN
  -- data
  let qMods ← emitQCells out r.Q
  must (r.rO.all fun x => x.idx.all (· < 4096)) "cell indices < 4096"
  let oMods ← emitIdx out "o" (r.rO.map (·.idx)) S.idxPage
  let nMods ← if same then pure [] else emitIdx out "n" (r.rN.map (·.idx)) S.idxPage
  -- the index ranges of the checked-index lookup (A7 rectangles, Hessian cells)
  let ixA := ixTable r.A.nj r.A.nk (a7Ix r.A)
  let ixH := ixTable r.H.nd r.H.nx (hessIx r.H)
  must (ixA.all fun x => x.all fun (a, b) => a < 4096 && b < 4096) "A7 index ranges < 4096"
  must (ixH.all fun x => x.all fun (a, b) => a < 4096 && b < 4096) "Hessian index ranges < 4096"
  let aIxMods ← emitIdx2 out "a" ixA S.idxPage
  let hIxMods ← emitIdx2 out "h" ixH S.idxPage
  let consts := boxMod "Consts"
  emitConsts out r ([boxMod "QCells", boxMod "Idx/O"] ++ (if same then [] else [boxMod "Idx/N"]) ++
    [boxMod "Idx/A", boxMod "Idx/H", "SandierSerfaty.CertData.Box.Nodes", "SandierSerfaty.Certificate.Box.NumCheckIdx",
      extData, "SandierSerfaty.CertData.Lam.Data"])
  let shardImp := [consts, "SandierSerfaty.CertData.Box.Split"]
  -- value rows
  let (outerMods, outerBlks, negMods, negBlks) ← if same then do
      let (mods, ob, nb) ← emitBoth out shardImp E G Gr S.seg S.oMod
      pure (mods, ob, ([] : List String), nb)
    else do
      let (outerMods, outerBlks) ← emitGroup out "Outer" "The outer rows (A8)"
        "Segments of at most the `seg` queries of a row with literal checkpoints (`outerSeg`), the rows, the block."
        shardImp (G.nd + 1) S.oMod fun a b => valueModule "o" E G Gr S.seg a b
      let (negMods, negBlks) ← emitGroup out "Neg" "The negative-part rows (A9)"
        "Segments with literal checkpoints (`negSeg`), the rows, the block."
        shardImp (Gr.nd + 1) S.oMod fun a b => valueModule "n" E G Gr S.seg a b
      pure (outerMods, outerBlks, negMods, negBlks)
  -- the K row
  let mut kb := ""
  let mut acc := SInt.zero
  let mut kn : Array String := #[]
  for (k, len) in pieces KG.nx S.seg do
    let nm := s!"k_{k}"
    kn := kn.push nm
    if k + len == KG.nx then
      must (sumLoop E KG.idx KG.dm KG.sm KG.thr len k acc) nm
      kb := kb ++ s!"theorem {nm} : sumLoop evalE kGrid.idx kGrid.dm kGrid.sm kGrid.thr {len} {k} {sintS acc} = true := by\n  decide +kernel\n\n"
    else
      let acc' := stepAcc false E KG.idx KG.dm KG.sm k len acc
      must (sumSeg E KG.idx KG.dm KG.sm len k acc acc') nm
      kb := kb ++ s!"theorem {nm} : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm {len} {k} {sintS acc} {sintS acc'} = true := by\n  decide +kernel\n\n"
      acc := acc'
  kb := kb ++ s!"theorem k_row : kGrid.row evalE = true :=\n  {segChain "sumLoop_of_seg" kn KG.nx}\n\n"
  writeBox out "KRow" (proofMod "The `K` row (kernel)" shardImp
    "The sum row at the dyadic node near `p` (`Box.KBound`): segments with literal checkpoints (`sumSeg`)." kb)
  -- A7 and the Hessian
  let (a7Mods, a7Blks) ← emitGroup out "A7" "The A7 rectangles"
    "Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block." shardImp r.A.nj S.aMod
    fun a b => a7Module r.A (a7Ix r.A) S.aSeg a b
  let (hMods, hBlks) ← emitGroup out "Hess" "The Hessian rows (A10)"
    "Segments of `hSeg` cells with interval checkpoints (`hessSeg`, checked index), the rows, the block." shardImp r.H.nd S.hMod
    fun a b => hessModule r.H (hessIx r.H) S.hSeg a b
  -- the query cells against the table
  let nQ := r.Q.cells.size
  let cellF : Nat → Bool := fun i => cellCheck nodes[i]! nodes[i + 1]! cts[i]! nts[i]! r.Q.cells[i]! r.Q.rf r.Q.re
  let fq := "fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe"
  let mut qMods2 := []
  let mut qBlks : Array (String × Nat × Nat) := #[]
  let mut m := 0
  let qps := pieces nQ S.qSeg
  let mut g := 0
  while g < qps.size do
    let mut body := ""
    for (a, len) in qps.extract g (g + S.qMod) do
      must (allFrom cellF a len) s!"qc_{a}"
      body := body ++ s!"theorem qc_{a} : allFrom ({fq}) {a} {len} = true := by\n  decide +kernel\n\n"
      qBlks := qBlks.push (s!"qc_{a}", a, len)
    let rel := s!"QCheck/S{pad m 2}"
    writeBox out rel (proofMod s!"The query cells against the table, shard {m} (kernel)"
      [boxMod "QCells", tableData, "SandierSerfaty.CertData.Box.Split"]
      "`Query.cellCheck` of the query cells against the table nodes and tuples (`QRealizes`)." body)
    qMods2 := qMods2 ++ [boxMod rel]
    g := g + S.qMod
    m := m + 1
  -- the non-row conjuncts and the scalar checks
  let L := litsOf r
  let d := r.P
  let cl := [("f0l_ok", "ivEq f0lLit (IV.addRad (ntAt " ++ toString d.iL ++ ").f0 lamRad)", ivEq L.f0l (IV.addRad nts[d.iL]!.f0 d.rad)),
    ("f0R_ok", s!"ivEq f0RLit (IV.addRad (ntAt {d.iR}).f0 lamRad)", ivEq L.f0R (IV.addRad nts[d.iR]!.f0 d.rad)),
    ("eR_ok", s!"ivEq eRLit (IV.addRad (ntAt {d.iR}).e0 lamRad)", ivEq L.eR (IV.addRad nts[d.iR]!.e0 d.rad)),
    ("bl_ok", "ivEq blLit (IV.addRad (basis dLit 5 (knotIV dLit 6)).bsum.c0 lamRad)", ivEq L.bl d.blI),
    ("lsq_ok", "ivEq lsqLit (IV.sq (knotIV dLit 6))", ivEq L.lsq d.lsqI),
    ("l_ok", "ivEq lLit (knotIV dLit 6)", ivEq L.l d.lI),
    ("k0_ok", "ivEq k0Lit (IV.neg (IV.mul dLit.pi blLit))", ivEq L.k0 (IV.neg (IV.mul d.piI L.bl))),
    ("mu_ok", "ivEq muLit (muEnc dLit.r0 f0RLit eRLit lamBox)", ivEq L.mu (muEnc d.r0I L.f0R L.eR r.lamI)),
    ("outer_pre", "outerPre a7Dat oGrid parLit", outerPre r.A G r.par),
    ("neg_pre", "negPre a7Dat nGrid parLit", negPre r.A Gr r.par),
    ("k_pre", "kPre kGrid parLit", kPre KG r.par),
    ("a7_pre", "a7Pre a7Dat", a7Pre r.A),
    ("hess_pre", "hessPre hessDat", hessPre r.H),
    ("eval_ok", "evalCheckOf evalE lamBox dLit.pi dLit.r0 f0lLit f0RLit eRLit blLit lsqLit qRf qRe",
      evalCheckOfN E d r.lamI r.Q.rf r.Q.re)]
  let mut cb := ""
  for (nm, st, ok) in cl do
    must ok nm
    cb := cb ++ s!"theorem {nm} : {st} = true := by\n  decide +kernel\n\n"
  let (δ1, δ2) := deltaParts r.Q.rf r.Q.re d r.lamI
  let A := r.A
  let scal := [("kc_ok", "kcB a7Dat.L1 a7Dat.L2 a7Dat.L3 a7Dat.L4 kGrid.thr.toInt (kGrid.sm kGrid.nx) parLit.kSh parLit.kRd parLit.kRx deltaLit kcLit",
      decide (kcLhs A.L1 A.L2 A.L3 A.L4 KG.thr.toInt (KG.sm KG.nx) r.par.kSh r.par.kRd r.par.kRx r.δ ≤ r.Kc)),
    ("thr_ok", "outThrB a7Dat.L1 a7Dat.L2 a7Dat.L3 a7Dat.L4 oGrid.thr.toInt (oGrid.sm oGrid.nx) parLit.oSh parLit.oDh parLit.oRho deltaLit kcLit",
      decide (r.Kc + outErr A.L1 A.L2 A.L3 A.L4 (G.sm G.nx) r.par.oSh r.par.oDh r.par.oRho r.δ ≤ qInt G.thr.toInt 256)),
    ("nthr_ok", "negThrB a7Dat.L1 a7Dat.L2 nGrid.thr.toInt (nGrid.sm nGrid.nx) parLit.nSh parLit.nDh deltaLit kcLit",
      decide (qInt Gr.thr.toInt 256 + negErr A.L1 A.L2 (Gr.sm Gr.nx) r.par.nSh r.par.nDh r.δ + r.Kc ≤ 0)),
    ("delta_ok", "deltaB qRf qRe lamBox dLit.pi dLit.r0 f0lLit f0RLit eRLit blLit lsqLit deltaLit",
      decide (0 ≤ r.δ) && decide (δ1 ≤ r.δ) && decide (δ2 ≤ r.δ))]
  let mut failing : List String := []
  for (nm, st, ok) in scal do
    if !ok then failing := failing ++ [nm]
    cb := cb ++ (if ok then "" else "-- FAILS natively (emitted with `--force`): this declaration does not check.\n") ++
      s!"theorem {nm} : {st} = true := by\n  decide +kernel\n\n"
  writeBox out "Checks" (proofMod "The non-row conjuncts and the scalar checks of the box (kernel)"
    [boxMod "Consts", "SandierSerfaty.CertData.Box.Split",
      "SandierSerfaty.Certificate.Box.NumScalar", extData]
    ("The enclosure literals against their definitions (`ivEq`), the conjuncts of `outerGridB`, `negGridB`, `kRowB`,\n" ++
     "`a7B`, `hessB` other than the rows (`outerPre`, …), the evaluator test and the scalar checks.") cb)
  -- the aggregation
  let fb := "theorem a7B_ok : a7BI a7Dat aIx = true :=\n  a7BI_of a7_pre\n    " ++ addChain "fun j => a7Dat.rowI aIx j a7Dat.nk" a7Blks ++ "\n\n" ++
    "theorem outer_ok : outerGridB a7Dat oGrid evalE parLit = true :=\n  outerGridB_of outer_pre\n    " ++
      addChain "fun j => oGrid.row evalE j" outerBlks ++ "\n\n" ++
    "theorem neg_ok : negGridB a7Dat nGrid evalE parLit = true :=\n  negGridB_of neg_pre\n    " ++
      addChain "fun j => nGrid.row evalE j" negBlks ++ "\n\n" ++
    "theorem k_ok : kRowB kGrid evalE parLit = true := kRowB_of k_pre k_row\n\n" ++
    "theorem hess_ok : hessBI hessDat hIx = true :=\n  hessBI_of hess_pre\n    " ++ addChain "fun a => hessDat.rowI hIx a" hBlks ++ "\n\n" ++
    s!"theorem qcells_ok : allLt ({fq}) qTbl.n = true :=\n  " ++ addChain fq qBlks ++ "\n\n"
  writeBox out "Final" (proofMod "The Boolean checks of the box assertions, assembled"
    ([boxMod "Checks", boxMod "KRow"] ++ outerMods ++ negMods ++ a7Mods ++ hMods ++ qMods2)
    ("`a7BI`, `outerGridB`, `negGridB`, `kRowB`, `hessBI` of `Lambda.certificateGoal_of_checks''` on the literal data, and the\n" ++
     "`cellCheck` conjunction of the query cells (for `QRealizes`), from the shards. With `Box.Checks` these are all the\n" ++
     "Boolean hypotheses of the box layer of `certificateGoal_of_checks''`; its remaining premises are the table model\n" ++
     "(`Table.Encl.tbl_model`) and the enclosures of the constants (`ExteriorSigns`).") fb)
  let nO := (pieces G.nx S.seg).size * (G.nd + 1)
  IO.println s!"emitted: {qMods.length} query-cell data modules, {oMods.length + nMods.length} index modules, {aIxMods.length + hIxMods.length} index-range modules, Consts; shards: {outerMods.length} outer ({nO} segment theorems), {negMods.length} negative, KRow, {a7Mods.length} A7, {hMods.length} Hessian, {qMods2.length} query-cell checks, Checks, Final"
  if !failing.isEmpty then IO.println s!"WARNING: emitted with failing scalar checks {failing} (--force)"

end CertGen.Box
