/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 0 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_0_0_ok : allCells dLit 0 core_0_0 = true := by
  decide +kernel

theorem core_0_1_ok : allCells dLit 0 core_0_1 = true := by
  decide +kernel

theorem core_0_2_ok : allCells dLit 0 core_0_2 = true := by
  decide +kernel

theorem core_0_3_ok : allCells dLit 0 core_0_3 = true := by
  decide +kernel

theorem core_0_4_ok : allCells dLit 0 core_0_4 = true := by
  decide +kernel

theorem core_0_5_ok : allCells dLit 0 core_0_5 = true := by
  decide +kernel

theorem core_0_6_ok : allCells dLit 0 core_0_6 = true := by
  decide +kernel

theorem core_0_7_ok : allCells dLit 0 core_0_7 = true := by
  decide +kernel

end SandierSerfaty.CertData
