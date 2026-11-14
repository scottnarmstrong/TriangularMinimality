/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 8 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_1_ok : allCells dLit 2 core_2_1 = true := by
  decide +kernel

theorem core_2_2_ok : allCells dLit 2 core_2_2 = true := by
  decide +kernel

theorem core_2_3_ok : allCells dLit 2 core_2_3 = true := by
  decide +kernel

theorem core_2_4_ok : allCells dLit 2 core_2_4 = true := by
  decide +kernel

theorem core_2_5_ok : allCells dLit 2 core_2_5 = true := by
  decide +kernel

theorem core_2_6_ok : allCells dLit 2 core_2_6 = true := by
  decide +kernel

theorem core_2_7_ok : allCells dLit 2 core_2_7 = true := by
  decide +kernel

theorem core_2_8_ok : allCells dLit 2 core_2_8 = true := by
  decide +kernel

end SandierSerfaty.CertData
