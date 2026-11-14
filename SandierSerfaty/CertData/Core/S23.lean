/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 23 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_121_ok : allCells dLit 2 core_2_121 = true := by
  decide +kernel

theorem core_2_122_ok : allCells dLit 2 core_2_122 = true := by
  decide +kernel

theorem core_2_123_ok : allCells dLit 2 core_2_123 = true := by
  decide +kernel

theorem core_2_124_ok : allCells dLit 2 core_2_124 = true := by
  decide +kernel

theorem core_2_125_ok : allCells dLit 2 core_2_125 = true := by
  decide +kernel

theorem core_3_0_ok : allCells dLit 3 core_3_0 = true := by
  decide +kernel

theorem core_4_0_ok : allCells dLit 4 core_4_0 = true := by
  decide +kernel

theorem core_4_1_ok : allCells dLit 4 core_4_1 = true := by
  decide +kernel

end SandierSerfaty.CertData
