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
# The query cells against the table, shard 4 (kernel)

`Query.cellCheck` of the query cells against the table nodes and tuples (`QRealizes`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem qc_2048 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2048 64 = true := by
  decide +kernel

theorem qc_2112 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2112 64 = true := by
  decide +kernel

theorem qc_2176 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2176 64 = true := by
  decide +kernel

theorem qc_2240 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2240 64 = true := by
  decide +kernel

theorem qc_2304 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2304 64 = true := by
  decide +kernel

theorem qc_2368 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2368 64 = true := by
  decide +kernel

theorem qc_2432 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2432 64 = true := by
  decide +kernel

theorem qc_2496 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2496 64 = true := by
  decide +kernel

end SandierSerfaty.CertData.Box
