/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 9 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_9_ok : allCells dLit 2 core_2_9 = true := by
  decide +kernel

theorem core_2_10_ok : allCells dLit 2 core_2_10 = true := by
  decide +kernel

theorem core_2_11_ok : allCells dLit 2 core_2_11 = true := by
  decide +kernel

theorem core_2_12_ok : allCells dLit 2 core_2_12 = true := by
  decide +kernel

theorem core_2_13_ok : allCells dLit 2 core_2_13 = true := by
  decide +kernel

theorem core_2_14_ok : allCells dLit 2 core_2_14 = true := by
  decide +kernel

theorem core_2_15_ok : allCells dLit 2 core_2_15 = true := by
  decide +kernel

theorem core_2_16_ok : allCells dLit 2 core_2_16 = true := by
  decide +kernel

end SandierSerfaty.CertData
