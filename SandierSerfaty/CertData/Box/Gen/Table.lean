/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Gen.Grid

/-!
# What-if tables for the box dry run (untrusted)

The radial table of `CertGen.Main` (`buildTable`, the C++ node scheme `κ_j + (κ_{j+1} - κ_j) i/n` with `n` the
cell count of segment `j` rounded up to a multiple of `8`) rebuilt here for *other* per-segment densities, to
measure what the query-cell radii `rf`, `re` and the box margins would be. It propagates the sector state node
by node exactly as `buildTable` does (the chunking of `buildTable` only places checkpoints; the values are the
same). Used only by the dry run with `dens=…`; the emitted shards always use the table of `CertGen.Main`.
-/

public section

namespace CertGen.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table

def roundUp8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- The cell count of segment `j` at the densities `dens`. -/
def segCellsD (dens : List Nat) (d : BasisData) (j : Nat) : Nat :=
  roundUp8 (((knotIV d (j + 1)).lo.mag - (knotIV d j).lo.mag) * dens.getD j 24000 / 2 ^ 128 + 1)

def segNodeD (d : BasisData) (j n i : Nat) : IV 128 :=
  if i = 0 then knotIV d j
  else IV.add (knotIV d j) (IV.divNat (IV.mulNat (IV.sub (knotIV d (j + 1)) (knotIV d j)) i) n)

/-- Nodes, cell tuples, node tuples and the knot cell indices of the table at the densities `dens`. -/
def tableD (dens : List Nat) (d : BasisData) : Array (IV 128) × Array Tup × Array Tup × List Nat := Id.run do
  let mut nodes : Array (IV 128) := #[]
  for j in [0:6] do
    let n := segCellsD dens d j
    for i in [0:n] do
      nodes := nodes.push (segNodeD d j n i)
  nodes := nodes.push (knotIV d 6)
  let mut cts : Array Tup := #[]
  let mut nts : Array Tup := #[]
  let mut S : SState := ⟨⟨SInt.zero, SInt.zero⟩, ⟨SInt.zero, SInt.zero⟩, []⟩
  let mut i := 0
  let mut knots : List Nat := [0]
  for j in [0:6] do
    let n := segCellsD dens d j
    if j = 1 then
      S := initStateOf d d.pc (initTerms d d.pc)
    for _ in [0:n] do
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
    knots := knots ++ [i]
  return (nodes, cts, nts, knots)

end CertGen.Box
