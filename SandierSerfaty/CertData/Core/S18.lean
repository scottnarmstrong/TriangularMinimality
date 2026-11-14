/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 18 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_81_ok : allCells dLit 2 core_2_81 = true := by
  decide +kernel

theorem core_2_82_ok : allCells dLit 2 core_2_82 = true := by
  decide +kernel

theorem core_2_83_ok : allCells dLit 2 core_2_83 = true := by
  decide +kernel

theorem core_2_84_ok : allCells dLit 2 core_2_84 = true := by
  decide +kernel

theorem core_2_85_ok : allCells dLit 2 core_2_85 = true := by
  decide +kernel

theorem core_2_86_ok : allCells dLit 2 core_2_86 = true := by
  decide +kernel

theorem core_2_87_ok : allCells dLit 2 core_2_87 = true := by
  decide +kernel

theorem core_2_88_ok : allCells dLit 2 core_2_88 = true := by
  decide +kernel

end SandierSerfaty.CertData
