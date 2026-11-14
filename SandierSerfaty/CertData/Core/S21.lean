/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 21 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_105_ok : allCells dLit 2 core_2_105 = true := by
  decide +kernel

theorem core_2_106_ok : allCells dLit 2 core_2_106 = true := by
  decide +kernel

theorem core_2_107_ok : allCells dLit 2 core_2_107 = true := by
  decide +kernel

theorem core_2_108_ok : allCells dLit 2 core_2_108 = true := by
  decide +kernel

theorem core_2_109_ok : allCells dLit 2 core_2_109 = true := by
  decide +kernel

theorem core_2_110_ok : allCells dLit 2 core_2_110 = true := by
  decide +kernel

theorem core_2_111_ok : allCells dLit 2 core_2_111 = true := by
  decide +kernel

theorem core_2_112_ok : allCells dLit 2 core_2_112 = true := by
  decide +kernel

end SandierSerfaty.CertData
