/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 3 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_0_24_ok : allCells dLit 0 core_0_24 = true := by
  decide +kernel

theorem core_0_25_ok : allCells dLit 0 core_0_25 = true := by
  decide +kernel

theorem core_0_26_ok : allCells dLit 0 core_0_26 = true := by
  decide +kernel

theorem core_0_27_ok : allCells dLit 0 core_0_27 = true := by
  decide +kernel

theorem core_1_0_ok : allCells dLit 1 core_1_0 = true := by
  decide +kernel

theorem core_1_1_ok : allCells dLit 1 core_1_1 = true := by
  decide +kernel

theorem core_1_2_ok : allCells dLit 1 core_1_2 = true := by
  decide +kernel

theorem core_1_3_ok : allCells dLit 1 core_1_3 = true := by
  decide +kernel

end SandierSerfaty.CertData
