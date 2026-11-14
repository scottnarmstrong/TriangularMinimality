/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 25 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_4_10_ok : allCells dLit 4 core_4_10 = true := by
  decide +kernel

theorem core_4_11_ok : allCells dLit 4 core_4_11 = true := by
  decide +kernel

theorem core_4_12_ok : allCells dLit 4 core_4_12 = true := by
  decide +kernel

theorem core_4_13_ok : allCells dLit 4 core_4_13 = true := by
  decide +kernel

theorem core_4_14_ok : allCells dLit 4 core_4_14 = true := by
  decide +kernel

theorem core_4_15_ok : allCells dLit 4 core_4_15 = true := by
  decide +kernel

theorem core_4_16_ok : allCells dLit 4 core_4_16 = true := by
  decide +kernel

theorem core_4_17_ok : allCells dLit 4 core_4_17 = true := by
  decide +kernel

end SandierSerfaty.CertData
