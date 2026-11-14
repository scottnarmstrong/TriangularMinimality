/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 12 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_33_ok : allCells dLit 2 core_2_33 = true := by
  decide +kernel

theorem core_2_34_ok : allCells dLit 2 core_2_34 = true := by
  decide +kernel

theorem core_2_35_ok : allCells dLit 2 core_2_35 = true := by
  decide +kernel

theorem core_2_36_ok : allCells dLit 2 core_2_36 = true := by
  decide +kernel

theorem core_2_37_ok : allCells dLit 2 core_2_37 = true := by
  decide +kernel

theorem core_2_38_ok : allCells dLit 2 core_2_38 = true := by
  decide +kernel

theorem core_2_39_ok : allCells dLit 2 core_2_39 = true := by
  decide +kernel

theorem core_2_40_ok : allCells dLit 2 core_2_40 = true := by
  decide +kernel

end SandierSerfaty.CertData
