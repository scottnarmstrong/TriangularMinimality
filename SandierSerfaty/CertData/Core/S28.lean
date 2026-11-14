/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 28 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_4_34_ok : allCells dLit 4 core_4_34 = true := by
  decide +kernel

theorem core_4_35_ok : allCells dLit 4 core_4_35 = true := by
  decide +kernel

theorem core_4_36_ok : allCells dLit 4 core_4_36 = true := by
  decide +kernel

theorem core_4_37_ok : allCells dLit 4 core_4_37 = true := by
  decide +kernel

theorem core_4_38_ok : allCells dLit 4 core_4_38 = true := by
  decide +kernel

theorem core_4_39_ok : allCells dLit 4 core_4_39 = true := by
  decide +kernel

theorem core_4_40_ok : allCells dLit 4 core_4_40 = true := by
  decide +kernel

theorem core_4_41_ok : allCells dLit 4 core_4_41 = true := by
  decide +kernel

end SandierSerfaty.CertData
