/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 1 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_0_8_ok : allCells dLit 0 core_0_8 = true := by
  decide +kernel

theorem core_0_9_ok : allCells dLit 0 core_0_9 = true := by
  decide +kernel

theorem core_0_10_ok : allCells dLit 0 core_0_10 = true := by
  decide +kernel

theorem core_0_11_ok : allCells dLit 0 core_0_11 = true := by
  decide +kernel

theorem core_0_12_ok : allCells dLit 0 core_0_12 = true := by
  decide +kernel

theorem core_0_13_ok : allCells dLit 0 core_0_13 = true := by
  decide +kernel

theorem core_0_14_ok : allCells dLit 0 core_0_14 = true := by
  decide +kernel

theorem core_0_15_ok : allCells dLit 0 core_0_15 = true := by
  decide +kernel

end SandierSerfaty.CertData
