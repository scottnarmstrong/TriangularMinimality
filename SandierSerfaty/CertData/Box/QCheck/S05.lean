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
# The query cells against the table, shard 5 (kernel)

`Query.cellCheck` of the query cells against the table nodes and tuples (`QRealizes`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem qc_2560 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2560 64 = true := by
  decide +kernel

theorem qc_2624 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2624 64 = true := by
  decide +kernel

theorem qc_2688 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2688 64 = true := by
  decide +kernel

theorem qc_2752 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2752 64 = true := by
  decide +kernel

theorem qc_2816 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2816 64 = true := by
  decide +kernel

theorem qc_2880 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2880 64 = true := by
  decide +kernel

theorem qc_2944 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 2944 64 = true := by
  decide +kernel

theorem qc_3008 : allFrom (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) 3008 64 = true := by
  decide +kernel

end SandierSerfaty.CertData.Box
