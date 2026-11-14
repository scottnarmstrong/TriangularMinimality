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
# The query cells against the table, shard 6 (kernel)

`Query.cellCheck` of the query cells against the table nodes and tuples (`QRealizes`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem qc_3072 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3072 64 = true := by
  decide +kernel

theorem qc_3136 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3136 64 = true := by
  decide +kernel

theorem qc_3200 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3200 64 = true := by
  decide +kernel

theorem qc_3264 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3264 64 = true := by
  decide +kernel

theorem qc_3328 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3328 64 = true := by
  decide +kernel

theorem qc_3392 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3392 64 = true := by
  decide +kernel

theorem qc_3456 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3456 64 = true := by
  decide +kernel

theorem qc_3520 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3520 64 = true := by
  decide +kernel

end SandierSerfaty.CertData.Box
