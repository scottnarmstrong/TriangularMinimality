/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Shards

/-!
# Kernel regression probes on real box data (untrusted)

`emitProbes dir r …` writes self-contained Lean files (Mathlib-free imports, the real query cells, table and
evaluator data inlined) with `decide +kernel` statements on a few real rows: `base` (data only), `val` (one outer
row and one negative-part row in segments of `seg` queries), `a7` (one block of A7 rectangles), `hess` (one
segment of Hessian cells). Timing them (`base` subtracted) measures the kernel cost per query of each kind before
any shard is built. Probe files are written outside the library (`.lake/probes/…`).
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

def tupS (t : Tup) : String :=
  s!"⟨{ivS t.f0}, {ivS t.f1}, {ivS t.f2}, {ivS t.e0}, {ivS t.e1}, {ivS t.e2}⟩"

/-- A two-level tree (blocks of `64`) as one definition per block plus a dispatch. -/
def bigTree (name ty : String) (leaves : Array String) : String := Id.run do
  let nb := (leaves.size + 63) / 64
  let mut s := ""
  for b in [0:nb] do
    let ls := leaves.extract (64 * b) (64 * b + 64)
    s := s ++ s!"def {name}B_{b} (k : Nat) : {ty} :=\n  " ++ treeS "k" (fun i => ls[i]!) 64 0 ls.size ++ "\n\n"
  s := s ++ s!"def {name}Blk (b k : Nat) : {ty} :=\n  " ++ treeS "b" (fun i => s!"{name}B_{i} k") 64 0 nb ++ "\n\n"
  return s ++ s!"def {name} (i : Nat) : {ty} := {name}Blk (Nat.div i 64) (Nat.mod i 64)\n\n"

def probeHead : String :=
  "import SandierSerfaty.CertData.Box.Split\nimport SandierSerfaty.CertData.Box.Nodes\n\n" ++ opensS ++
  "\nnamespace Probe\n\n"

def emitProbes (dir : String) (r : BoxOut) (nodes : Array (IV 128)) (cts : Array Tup) (j a hr : Nat) : IO Unit := do
  let (G, Gr, _) := nativeGrids r
  let E := r.E
  let L := r.S.seg
  let mut data := bigTree "pQ" "QCell" (r.Q.cells.map qcellS)
  data := data ++ s!"def pE : EvalData := ⟨⟨{r.Q.cells.size}, pQ⟩, {fxS E.lam}, {fxS E.mu}, {fxS E.kap}, {fxS E.cc}, {fxS E.lsq}⟩\n\n"
  data := data ++ s!"def pIdxO : Nat := {packHex r.rO[j]!.idx}\n\ndef pIdxN : Nat := {packHex r.rN[j]!.idx}\n\n"
  data := data ++ "def pIO (k : Nat) : Nat := Nat.land (Nat.shiftRight pIdxO (Nat.mul 12 k)) 4095\n\n"
  data := data ++ "def pIN (k : Nat) : Nat := Nat.land (Nat.shiftRight pIdxN (Nat.mul 12 k)) 4095\n\n"
  data := data ++ s!"def pThrO : SInt := {sintS G.thr}\n\ndef pThrN : SInt := {sintS Gr.thr}\n\n"
  let tbl := bigTree "pNode" "IV 128" (nodes.map ivS) ++ bigTree "pCt" "Tup" (cts.map tupS) ++
    s!"def pT : ITable := ⟨{cts.size}, pNode, pCt⟩\n\n"
  let A := r.A
  let H := r.H
  let LL := litsOf r
  let consts := s!"def pA : A7Data := ⟨pT, {ivS LL.f0l}, {ivS LL.k0}, {ivS LL.lsq}, {ivS LL.l}, {ivS r.lamI}, {ivS LL.mu}, {A.rad}, {A.L1}, {A.L2}, {A.L3}, {A.L4}, {A.nj}, {A.nk}, a7D {A.nj}, a7S {A.nk}⟩\n\n" ++
    s!"def pH : HessData := ⟨pT, {ivS LL.f0l}, {ivS LL.k0}, {ivS LL.lsq}, {ivS LL.l}, {ivS r.lamI}, {ivS LL.mu}, {H.rad}, {H.nd}, {H.nx}, {H.jmin}, hessD {H.nd}, hessS {H.jmin} {H.nx - H.jmin}⟩\n\n"
  let g := r.gO
  let dmS := s!"(gridD3 {g.d1} {g.d2} {g.d3} {j})"
  let smS := s!"(gridS3 {g.s1} {g.s2} {g.s3})"
  -- the value rows
  let mut v := ""
  let mut acc := SInt.zero
  let mut accN := SInt.zero
  let inRow := inRowB G.jl G.jr j
  for (k, len) in pieces G.nx L do
    if k + len == G.nx then
      must (outerLoop E (G.idx j) (G.dm j) G.sm G.thr inRow G.kl G.kr len k acc) "probe outer"
      must (negLoop E (Gr.idx j) (Gr.dm j) Gr.sm Gr.thr len k accN) "probe neg"
      v := v ++ s!"theorem o_{k} : outerLoop pE pIO {dmS} {smS} pThrO {inRow} {G.kl} {G.kr} {len} {k} {sintS acc} = true := by\n  decide +kernel\n\n"
      v := v ++ s!"theorem n_{k} : negLoop pE pIN {dmS} {smS} pThrN {len} {k} {sintS accN} = true := by\n  decide +kernel\n\n"
    else
      let acc' := stepAcc false E (G.idx j) (G.dm j) G.sm k len acc
      let accN' := stepAcc true E (Gr.idx j) (Gr.dm j) Gr.sm k len accN
      must (outerSeg E (G.idx j) (G.dm j) G.sm G.thr inRow G.kl G.kr len k acc acc') "probe outer seg"
      must (negSeg E (Gr.idx j) (Gr.dm j) Gr.sm len k accN accN') "probe neg seg"
      v := v ++ s!"theorem o_{k} : outerSeg pE pIO {dmS} {smS} pThrO {inRow} {G.kl} {G.kr} {len} {k} {sintS acc} {sintS acc'} = true := by\n  decide +kernel\n\n"
      v := v ++ s!"theorem n_{k} : negSeg pE pIN {dmS} {smS} {len} {k} {sintS accN} {sintS accN'} = true := by\n  decide +kernel\n\n"
      acc := acc'
      accN := accN'
  -- one A7 block, one Hessian segment
  let B := r.S.aSeg
  must (allFrom (A.rect a) 0 B) "probe a7"
  let a7 := s!"theorem a7blk : allFrom (pA.rect {a}) 0 {B} = true := by\n  decide +kernel\n\n"
  let hB := r.S.hSeg
  let i0 := H.jmin
  let accH := stepHess H H.ctx hr 0 i0 (IV.ofNatPair 0 0)
  let accH' := stepHess H H.ctx hr i0 hB accH
  must (hessSeg H H.ctx hr hB i0 accH accH') "probe hess"
  let hs := s!"theorem hseg : hessSeg pH pH.ctx {hr} {hB} {i0} {ivS accH} {ivS accH'} = true := by\n  decide +kernel\n\n"
  let w := fun (nm body : String) => IO.FS.writeFile ((dir : System.FilePath) / s!"{nm}.lean") (probeHead ++ body ++ "end Probe\n")
  IO.FS.createDirAll dir
  -- the scalar checks of `Box.NumScalar` / `Box.Cert` (Mathlib modules), stated `= native result`
  let (_, _, KG) := nativeGrids r
  let P := r.P
  let (δ1, δ2) := deltaParts r.Q.rf r.Q.re P r.lamI
  let bkc := decide (kcLhs A.L1 A.L2 A.L3 A.L4 KG.thr.toInt (KG.sm KG.nx) r.par.kSh r.par.kRd r.par.kRx r.δ ≤ r.Kc)
  let bthr := decide (r.Kc + outErr A.L1 A.L2 A.L3 A.L4 (G.sm G.nx) r.par.oSh r.par.oDh r.par.oRho r.δ ≤ qInt G.thr.toInt 256)
  let bnthr := decide (qInt Gr.thr.toInt 256 + negErr A.L1 A.L2 (Gr.sm Gr.nx) r.par.nSh r.par.nDh r.δ + r.Kc ≤ 0)
  let bdel := decide (0 ≤ r.δ) && decide (δ1 ≤ r.δ) && decide (δ2 ≤ r.δ)
  let bev := evalCheckOfN E P r.lamI r.Q.rf r.Q.re
  let sc := "import SandierSerfaty.Certificate.Box.NumScalar\n\n" ++ opensS ++ "\nnamespace Probe\n\n" ++
    s!"theorem kc : kcB {A.L1} {A.L2} {A.L3} {A.L4} ({KG.thr.toInt}) {KG.sm KG.nx} {r.par.kSh} {r.par.kRd} {r.par.kRx} {ratS r.δ} {ratS r.Kc} = {bkc} := by\n  decide +kernel\n\n" ++
    s!"theorem thr : outThrB {A.L1} {A.L2} {A.L3} {A.L4} ({G.thr.toInt}) {G.sm G.nx} {r.par.oSh} {r.par.oDh} {r.par.oRho} {ratS r.δ} {ratS r.Kc} = {bthr} := by\n  decide +kernel\n\n" ++
    s!"theorem nthr : negThrB {A.L1} {A.L2} ({Gr.thr.toInt}) {Gr.sm Gr.nx} {r.par.nSh} {r.par.nDh} {ratS r.δ} {ratS r.Kc} = {bnthr} := by\n  decide +kernel\n\n" ++
    s!"theorem del : deltaB {r.Q.rf} {r.Q.re} {ivS r.lamI} {ivS P.piI} {ivS P.r0I} {ivS P.f0lI} {ivS P.f0RI} {ivS P.eRI} {ivS P.blI} {ivS P.lsqI} {ratS r.δ} = {bdel} := by\n  decide +kernel\n\n" ++
    s!"theorem ev : evalCheckOf ⟨⟨0, fun _ => default⟩, {fxS E.lam}, {fxS E.mu}, {fxS E.kap}, {fxS E.cc}, {fxS E.lsq}⟩ {ivS r.lamI} {ivS P.piI} {ivS P.r0I} {ivS P.f0lI} {ivS P.f0RI} {ivS P.eRI} {ivS P.blI} {ivS P.lsqI} {r.Q.rf} {r.Q.re} = {bev} := by\n  decide +kernel\n\n" ++
    "end Probe\n"
  IO.FS.writeFile ((dir : System.FilePath) / "scalar.lean") sc
  w "base" (data ++ tbl ++ consts)
  w "val" (data ++ v)
  w "valbase" data
  w "a7" (data ++ tbl ++ consts ++ a7)
  w "hess" (data ++ tbl ++ consts ++ hs)
  IO.println s!"probes written to {dir}: outer/negative row {j} ({G.nx} queries each, segments of {L}), A7 row {a} block of {B}, Hessian row {hr} cells {i0}..{i0 + hB - 1}"

end CertGen.Box
