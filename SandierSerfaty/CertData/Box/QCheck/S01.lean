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
# The query cells against the table, shard 1 (kernel)

`Query.cellCheck` of the query cells against the table nodes and tuples (`QRealizes`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem qc_512 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 512 64 = true := by
  decide +kernel

theorem qc_576 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 576 64 = true := by
  decide +kernel

theorem qc_640 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 640 64 = true := by
  decide +kernel

theorem qc_704 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 704 64 = true := by
  decide +kernel

theorem qc_768 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 768 64 = true := by
  decide +kernel

theorem qc_832 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 832 64 = true := by
  decide +kernel

theorem qc_896 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 896 64 = true := by
  decide +kernel

theorem qc_960 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 960 64 = true := by
  decide +kernel

end SandierSerfaty.CertData.Box
