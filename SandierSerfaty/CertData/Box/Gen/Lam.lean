/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Emit
public import SandierSerfaty.Certificate.Lambda.Shard

/-!
# The shards of the fine `λ` (untrusted)

`emitLam` writes the kernel shards of `Lambda.lamFine flTbl dLit lamPar = some lamFLit` under `OUT/SandierSerfaty/
CertData/Lam/`: the literal prelude (`Data`: the root `lh` of `t₀²`, the two lookup tuples, the four point values,
the two integrand contexts, the checkpoints `qCk c`, `eCk c` after every `L` steps, the result), its checks (`Pre`),
the segments of the two sums (`Q*`, `E*`: `Lambda.runSeg`, one declaration per segment) and the composition
(`Final`: `Lambda.qSum_of_chain`, `Lambda.eSum_of_chain`, `Lambda.lamFine_eq_of`). Every value is computed natively
by the same definitions (`Lambda.Eval`, `Lambda.Shard`), and every emitted check is first run natively.
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

def tupLS (t : Tup) : String :=
  s!"⟨{ivS t.f0}, {ivS t.f1}, {ivS t.f2}, {ivS t.e0}, {ivS t.e1}, {ivS t.e2}⟩"

def qctxS (c : QCtx) : String :=
  s!"⟨{ivS c.p}, {ivS c.p2}, {ivS c.A}, {ivS c.W}, {c.N}, {c.rad}, {ivS c.F0}, {ivS c.B1}, {ivS c.B2}⟩"

def lamPath (out rel : String) : System.FilePath :=
  (out : System.FilePath) / "SandierSerfaty" / "CertData" / "Lam" / (rel ++ ".lean")

def lamMod (rel : String) : String := "SandierSerfaty.CertData.Lam." ++ rel

def lamOpens : String :=
  "open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table\n" ++
  "open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble\n"

def lamFile (data : Bool) (title : String) (imports : List String) (doc body : String) : String :=
  header title imports doc ++ (if data then "@[expose] public section\n\n" else "public section\n\n") ++
    "namespace SandierSerfaty.CertData\n\n" ++ lamOpens ++ "\n" ++ body ++ "end SandierSerfaty.CertData\n"

def writeLam (out rel s : String) : IO Unit := do
  let p := lamPath out rel
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p s

/-- The checkpoints of a sum: the states after `0, L, 2L, …, C L` steps. -/
def lamCks (step : Nat → Nat → Option (Nat × IV 128)) (L C : Nat) : IO (Array (Nat × IV 128)) := do
  let mut st : Nat × IV 128 := (0, IV.ofNat 0)
  let mut out := #[st]
  for c in [0:C] do
    match runLoopSt step L (L * c) st.1 st.2 with
    | none => throw (IO.userError s!"λ sum fails in segment {c}")
    | some s => st := s; out := out.push s
  return out

/-- Emit the `λ` shards; returns the module names of the segment shards. `L` steps per declaration, `per`
declarations per module. -/
def emitLam (out : String) (F : FTable) (d : BasisData) (P : LamPar) (L per : Nat) : IO (Option (IV 128)) := do
  let S0 := s0Of P
  let lh := IV.sqrtProposal (IV.add d.p2 (IV.sq S0))
  must (IV.sqrtCheck (IV.add d.p2 (IV.sq S0)) lh.1 lh.2) "λ: root t₀"
  let some cB := lookup F.T (IV.hull d.p d.r0) | throw (IO.userError "λ: lookup [p, R₀]")
  let some cY := lookup F.T (IV.hull d.p (IV.ofNatPair lh.1 lh.2)) | throw (IO.userError "λ: lookup [p, t₀]")
  let some FP := fPt F P.rad d.p | throw (IO.userError "λ: f₀(p)")
  let some FP1 := f1Pt F P.rad d.p | throw (IO.userError "λ: f₀'(p)")
  let some FR := fPt F P.rad d.r0 | throw (IO.userError "λ: f₀(R₀)")
  let some ER := ePt F P.rad d.r0 | throw (IO.userError "λ: e(R₀)")
  let cQ := qCtxOf d P.Nq P.rad S0 cB FP
  let cE := eCtxOf d P.Ne P.rad cB
  must (P.Nq % L == 0 && P.Ne % L == 0) "λ: L divides Nq, Ne"
  let CQ := P.Nq / L
  let CE := P.Ne / L
  let qck ← lamCks (qTerm F cQ) L CQ
  let eck ← lamCks (eTerm F cE) L CE
  let some I := lamFineS d P S0 (IV.ofNatPair lh.1 lh.2) cY FP FP1 FR ER (some qck[CQ]!.2) (some eck[CE]!.2)
    | throw (IO.userError "λ: last stage")
  must (optEqB (lamFine F d P) I) "λ: the composition equals lamFine"
  -- data
  let ckS : (Nat × IV 128) → String := fun s => s!"({s.1}, {ivS s.2})"
  let body :=
    "/-- The table with its node tuples. -/\ndef flTbl : FTable := ⟨iTbl, ntAt⟩\n\n" ++
    s!"/-- The parameters of the fine `λ` (`Nq`, `Ne`, the widening, `s₀ = {P.s0n}/{P.s0d}`). -/\n" ++
    s!"def lamPar : LamPar := ⟨{P.Nq}, {P.Ne}, lamRad, {P.s0n}, {P.s0d}⟩\n\n" ++
    s!"/-- Steps per segment. -/\ndef lamL : Nat := {L}\n\n" ++
    s!"/-- The proposed root of `t₀² = p² + s₀²`. -/\ndef lhLit : Nat × Nat := ({lh.1}, {lh.2})\n\n" ++
    s!"/-- The lookup over `[p, R₀]`. -/\ndef cBLit : Tup := {tupLS cB}\n\n" ++
    s!"/-- The lookup over `[p, t₀]`. -/\ndef cYLit : Tup := {tupLS cY}\n\n" ++
    s!"/-- `f₀(p)`. -/\ndef fpLit : IV 128 := {ivS FP}\n\n/-- `f₀'(p)`. -/\ndef fp1Lit : IV 128 := {ivS FP1}\n\n" ++
    s!"/-- `f₀(R₀)`. -/\ndef frLit : IV 128 := {ivS FR}\n\n/-- `e(R₀)`. -/\ndef erLit : IV 128 := {ivS ER}\n\n" ++
    s!"/-- The context of the first integrand. -/\ndef cQLit : QCtx := {qctxS cQ}\n\n" ++
    s!"/-- The context of the second integrand. -/\ndef cELit : QCtx := {qctxS cE}\n\n" ++
    "/-- The checkpoints of the first sum (after `lamL c` steps). -/\ndef qCk (c : Nat) : Nat × IV 128 :=\n  " ++
      treeS "c" (fun i => ckS qck[i]!) 64 0 qck.size ++ "\n\n" ++
    "/-- The checkpoints of the second sum. -/\ndef eCk (c : Nat) : Nat × IV 128 :=\n  " ++
      treeS "c" (fun i => ckS eck[i]!) 64 0 eck.size ++ "\n\n" ++
    s!"/-- The fine enclosure of `λ`. -/\ndef lamFLit : IV 128 := {ivS I}\n\n"
  writeLam out "Data" (lamFile true "The fine enclosure of λ (data)"
    ["SandierSerfaty.CertData.Table.Data", "SandierSerfaty.CertData.Exterior.Data",
      "SandierSerfaty.Certificate.Lambda.Shard"]
    "The literal prelude, checkpoints and result of `Lambda.lamFine flTbl dLit lamPar` (generated by `lake exe certgen`; untrusted until checked)." body)
  -- the prelude checks
  let X2 := "(IV.add dLit.p2 (IV.sq (s0Of lamPar)))"
  let pre := [
    ("lh_ok", s!"and (Nat.beq (IV.sqrtProposal {X2}).1 lhLit.1) (Nat.beq (IV.sqrtProposal {X2}).2 lhLit.2)"),
    ("sq_ok", s!"IV.sqrtCheck {X2} lhLit.1 lhLit.2"),
    ("cB_ok", "optTupEqB (lookup flTbl.T (IV.hull dLit.p dLit.r0)) cBLit"),
    ("cY_ok", "optTupEqB (lookup flTbl.T (IV.hull dLit.p (IV.ofNatPair lhLit.1 lhLit.2))) cYLit"),
    ("fp_ok", "optEqB (fPt flTbl lamPar.rad dLit.p) fpLit"),
    ("fp1_ok", "optEqB (f1Pt flTbl lamPar.rad dLit.p) fp1Lit"),
    ("fr_ok", "optEqB (fPt flTbl lamPar.rad dLit.r0) frLit"),
    ("er_ok", "optEqB (ePt flTbl lamPar.rad dLit.r0) erLit"),
    ("cQ_ok", "qctxEqB (qCtxOf dLit lamPar.Nq lamPar.rad (s0Of lamPar) cBLit fpLit) cQLit"),
    ("cE_ok", "qctxEqB (eCtxOf dLit lamPar.Ne lamPar.rad cBLit) cELit"),
    ("q0_ok", "and (Nat.beq (qCk 0).1 0) (ivEqB (qCk 0).2 (IV.ofNat 0))"),
    ("e0_ok", "and (Nat.beq (eCk 0).1 0) (ivEqB (eCk 0).2 (IV.ofNat 0))"),
    ("fin_ok", s!"optEqB (lamFineS dLit lamPar (s0Of lamPar) (IV.ofNatPair lhLit.1 lhLit.2) cYLit fpLit fp1Lit frLit erLit (some (qCk {CQ}).2) (some (eCk {CE}).2)) lamFLit")]
  let mut pb := ""
  for (nm, st) in pre do
    pb := pb ++ s!"theorem {nm} : {st} = true := by\n  decide +kernel\n\n"
  writeLam out "Pre" (lamFile false "The prelude of the fine λ (kernel shard)" [lamMod "Data"]
    "`decide +kernel` checks of the literal prelude of `lamFine`: the root `t₀`, the two lookups, the four point values, the two contexts, the initial checkpoints and the last stage." pb)
  -- the segments
  let mut mods : List String := []
  for (kind, C, cks, step) in [("Q", CQ, qck, "qTerm flTbl cQLit"), ("E", CE, eck, "eTerm flTbl cELit")] do
    let ckName := if kind == "Q" then "qCk" else "eCk"
    let mut m := 0
    let mut c := 0
    while c < C do
      let mut sb := ""
      for c' in [c:min C (c + per)] do
        -- native check of the emitted statement
        let stepF := if kind == "Q" then qTerm F cQ else eTerm F cE
        must (runSeg stepF L (L * c') cks[c']!.1 cks[c']!.2 cks[c' + 1]!.1 cks[c' + 1]!.2) s!"λ segment {kind} {c'}"
        sb := sb ++ s!"theorem {kind.toLower}_{c'} : runSeg ({step}) lamL (lamL * {c'}) ({ckName} {c'}).1 ({ckName} {c'}).2\n" ++
          s!"    ({ckName} ({c'} + 1)).1 ({ckName} ({c'} + 1)).2 = true := by\n  decide +kernel\n\n"
      let rel := s!"{kind}{pad m 2}"
      writeLam out rel (lamFile false s!"The fine λ, sum {kind}, shard {m} (kernel)" [lamMod "Data"]
        s!"`decide +kernel` segments of {L} steps of the {if kind == "Q" then "first" else "second"} midpoint sum, from literal checkpoints (`Lambda.runSeg`)." sb)
      mods := mods ++ [lamMod rel]
      c := c + per
      m := m + 1
  -- the composition
  let mut fb := ""
  for (kind, C, step, ckName) in [("Q", CQ, "qTerm flTbl cQLit", "qCk"), ("E", CE, "eTerm flTbl cELit", "eCk")] do
    let k := kind.toLower
    fb := fb ++ s!"/-- The segment `c` of the sum {kind}. -/\nabbrev Seg{kind} (c : Nat) : Prop :=\n  runSeg ({step}) lamL (lamL * c) ({ckName} c).1 ({ckName} c).2 ({ckName} (c + 1)).1 ({ckName} (c + 1)).2 = true\n\n"
    fb := fb ++ s!"theorem {k}_all : ∀ c, c < {C} → Seg{kind} c := by\n  have h0 : ∀ c, c < 0 → Seg{kind} c := forall_lt_zero'\n"
    for c in [0:C] do
      fb := fb ++ s!"  have h{c + 1} : ∀ c, c < {c + 1} → Seg{kind} c := forall_lt_succ_of h{c} {k}_{c}\n"
    fb := fb ++ s!"  exact h{C}\n\n"
  fb := fb ++ s!"/-- The first sum. -/\ntheorem qsum_ok : qSum flTbl cQLit = some (qCk {CQ}).2 :=\n  qSum_of_chain (L := lamL) (C := {CQ}) rfl q0_ok q_all\n\n"
  fb := fb ++ s!"/-- The second sum. -/\ntheorem esum_ok : eSum flTbl cELit = some (eCk {CE}).2 :=\n  eSum_of_chain (L := lamL) (C := {CE}) rfl e0_ok e_all\n\n"
  fb := fb ++ "/-- **The fine `λ` evaluates to the literal enclosure.** -/\ntheorem lamFine_ok : lamFine flTbl dLit lamPar = some lamFLit :=\n" ++
    "  lamFine_eq_of lh_ok sq_ok cB_ok cY_ok fp_ok fp1_ok fr_ok er_ok cQ_ok cE_ok qsum_ok esum_ok fin_ok\n\n"
  writeLam out "Final" (lamFile false "The fine λ, assembled" (mods ++ [lamMod "Pre"])
    "The segments joined (`Assemble.forall_lt_succ_of`, `Lambda.qSum_of_chain`, `Lambda.eSum_of_chain`) and `Lambda.lamFine_eq_of`: `lamFine flTbl dLit lamPar = some lamFLit`." fb)
  IO.println s!"λ shards: {mods.length} segment modules ({CQ} + {CE} segments of {L} steps), Data, Pre, Final; λ ∈ {ivS I}"
  return some I

end CertGen.Box
