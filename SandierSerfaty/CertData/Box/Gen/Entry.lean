/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.EmitAll
public import SandierSerfaty.CertData.Box.Gen.Probe
public import SandierSerfaty.CertData.Box.Gen.Lam

/-!
# The entry point of the box generator (untrusted)

Hook in `CertGen.Main.run` (after the table is built): `lake exe certgen OUT --quick` with a file `OUT/BOX` (or
the environment variable `CERTGEN_BOX`) holding the options of `CertGen.Box.Spec` separated by spaces or newlines
(`threads=6`, `dens=1000,6000,…`, `lamW=1/10000000`, `--noderiv`, `--emit`, `--force`, …). Runs the dry run
(`CertGen.Box.dryRun`) and, with `--emit`, writes the box data and shard modules under `OUT` and, when the emitted
scenario is the certified fine `λ`, the `λ` shards (`CertGen.Box.emitLam`).
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table

/-- The box mode is requested by the environment variable `CERTGEN_BOX` or by a file `OUT/BOX`. -/
def request (out : String) : IO (Option String) := do
  if let some o := ← IO.getEnv "CERTGEN_BOX" then return some o
  let f : System.FilePath := (out : System.FilePath) / "BOX"
  if ← f.pathExists then return some ((← IO.FS.readFile f).replace "\n" " ") else return none

/-- The entry point. -/
def entry (out : String) (opts : Option String) (d : BasisData) (nodes : Array (IV 128)) (cts nts : Array Tup)
    (knot : List Nat) : IO Bool := do
  let S := Spec.parse (((opts.getD "").splitOn " ").filter (· ≠ ""))
  let (nodes, cts, nts, knot) ← if S.dens.isEmpty then pure (nodes, cts, nts, knot) else do
    IO.println s!"what-if table densities {S.dens} (not the table of CertGen.Main; no emission)"
    let t := tableD S.dens d
    IO.println s!"what-if table: {t.2.1.size} cells, knot cells {t.2.2.2}"
    pure t
  match ← dryRun S d nodes cts nts knot with
  | none => return false
  | some r =>
    if S.probe && S.dens.isEmpty then
      emitProbes (((out : System.FilePath) / "kprobe").toString) r nodes cts (r.gO.d1 + r.gO.d2 / 2) 40 75
    if S.emit && S.dens.isEmpty && (r.pass || S.force) then
      if r.certLam then
        let FL : SandierSerfaty.Certificate.Lambda.FTable := ⟨⟨cts.size, fun i => nodes[i]!, fun i => cts[i]!⟩, fun i => nts[i]!⟩
        match ← emitLam out FL d r.lamPar S.lamL S.lamPer with
        | some I => must (SandierSerfaty.Certificate.Assemble.ivEqB I r.lamI) "λ shards: the emitted enclosure is the box enclosure"
        | none => throw (IO.userError "λ shards failed")
      emitAll out r nodes cts nts
    return r.pass

end CertGen.Box
