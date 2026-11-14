/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 24 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_4_2_ok : allCells dLit 4 core_4_2 = true := by
  decide +kernel

theorem core_4_3_ok : allCells dLit 4 core_4_3 = true := by
  decide +kernel

theorem core_4_4_ok : allCells dLit 4 core_4_4 = true := by
  decide +kernel

theorem core_4_5_ok : allCells dLit 4 core_4_5 = true := by
  decide +kernel

theorem core_4_6_ok : allCells dLit 4 core_4_6 = true := by
  decide +kernel

theorem core_4_7_ok : allCells dLit 4 core_4_7 = true := by
  decide +kernel

theorem core_4_8_ok : allCells dLit 4 core_4_8 = true := by
  decide +kernel

theorem core_4_9_ok : allCells dLit 4 core_4_9 = true := by
  decide +kernel

end SandierSerfaty.CertData
