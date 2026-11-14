/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 22 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_113_ok : allCells dLit 2 core_2_113 = true := by
  decide +kernel

theorem core_2_114_ok : allCells dLit 2 core_2_114 = true := by
  decide +kernel

theorem core_2_115_ok : allCells dLit 2 core_2_115 = true := by
  decide +kernel

theorem core_2_116_ok : allCells dLit 2 core_2_116 = true := by
  decide +kernel

theorem core_2_117_ok : allCells dLit 2 core_2_117 = true := by
  decide +kernel

theorem core_2_118_ok : allCells dLit 2 core_2_118 = true := by
  decide +kernel

theorem core_2_119_ok : allCells dLit 2 core_2_119 = true := by
  decide +kernel

theorem core_2_120_ok : allCells dLit 2 core_2_120 = true := by
  decide +kernel

end SandierSerfaty.CertData
