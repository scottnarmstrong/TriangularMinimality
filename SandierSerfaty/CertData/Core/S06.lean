/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 6 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_1_20_ok : allCells dLit 1 core_1_20 = true := by
  decide +kernel

theorem core_1_21_ok : allCells dLit 1 core_1_21 = true := by
  decide +kernel

theorem core_1_22_ok : allCells dLit 1 core_1_22 = true := by
  decide +kernel

theorem core_1_23_ok : allCells dLit 1 core_1_23 = true := by
  decide +kernel

theorem core_1_24_ok : allCells dLit 1 core_1_24 = true := by
  decide +kernel

theorem core_1_25_ok : allCells dLit 1 core_1_25 = true := by
  decide +kernel

theorem core_1_26_ok : allCells dLit 1 core_1_26 = true := by
  decide +kernel

theorem core_1_27_ok : allCells dLit 1 core_1_27 = true := by
  decide +kernel

end SandierSerfaty.CertData
