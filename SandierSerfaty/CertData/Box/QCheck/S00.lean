/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.QCells
public import SandierSerfaty.CertData.Table.Data
public import SandierSerfaty.CertData.Box.Split

/-!
# The query cells against the table, shard 0 (kernel)

`Query.cellCheck` of the query cells against the table nodes and tuples (`QRealizes`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem qc_0 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 0 64 = true := by
  decide +kernel

theorem qc_64 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 64 64 = true := by
  decide +kernel

theorem qc_128 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 128 64 = true := by
  decide +kernel

theorem qc_192 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 192 64 = true := by
  decide +kernel

theorem qc_256 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 256 64 = true := by
  decide +kernel

theorem qc_320 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 320 64 = true := by
  decide +kernel

theorem qc_384 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 384 64 = true := by
  decide +kernel

theorem qc_448 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 448 64 = true := by
  decide +kernel

end SandierSerfaty.CertData.Box
