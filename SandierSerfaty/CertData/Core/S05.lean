/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 5 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_1_12_ok : allCells dLit 1 core_1_12 = true := by
  decide +kernel

theorem core_1_13_ok : allCells dLit 1 core_1_13 = true := by
  decide +kernel

theorem core_1_14_ok : allCells dLit 1 core_1_14 = true := by
  decide +kernel

theorem core_1_15_ok : allCells dLit 1 core_1_15 = true := by
  decide +kernel

theorem core_1_16_ok : allCells dLit 1 core_1_16 = true := by
  decide +kernel

theorem core_1_17_ok : allCells dLit 1 core_1_17 = true := by
  decide +kernel

theorem core_1_18_ok : allCells dLit 1 core_1_18 = true := by
  decide +kernel

theorem core_1_19_ok : allCells dLit 1 core_1_19 = true := by
  decide +kernel

end SandierSerfaty.CertData
