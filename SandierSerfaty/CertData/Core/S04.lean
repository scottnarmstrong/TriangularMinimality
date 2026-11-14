/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 4 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_1_4_ok : allCells dLit 1 core_1_4 = true := by
  decide +kernel

theorem core_1_5_ok : allCells dLit 1 core_1_5 = true := by
  decide +kernel

theorem core_1_6_ok : allCells dLit 1 core_1_6 = true := by
  decide +kernel

theorem core_1_7_ok : allCells dLit 1 core_1_7 = true := by
  decide +kernel

theorem core_1_8_ok : allCells dLit 1 core_1_8 = true := by
  decide +kernel

theorem core_1_9_ok : allCells dLit 1 core_1_9 = true := by
  decide +kernel

theorem core_1_10_ok : allCells dLit 1 core_1_10 = true := by
  decide +kernel

theorem core_1_11_ok : allCells dLit 1 core_1_11 = true := by
  decide +kernel

end SandierSerfaty.CertData
