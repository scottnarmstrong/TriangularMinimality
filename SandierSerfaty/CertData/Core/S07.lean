/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 7 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_1_28_ok : allCells dLit 1 core_1_28 = true := by
  decide +kernel

theorem core_1_29_ok : allCells dLit 1 core_1_29 = true := by
  decide +kernel

theorem core_1_30_ok : allCells dLit 1 core_1_30 = true := by
  decide +kernel

theorem core_1_31_ok : allCells dLit 1 core_1_31 = true := by
  decide +kernel

theorem core_1_32_ok : allCells dLit 1 core_1_32 = true := by
  decide +kernel

theorem core_1_33_ok : allCells dLit 1 core_1_33 = true := by
  decide +kernel

theorem core_1_34_ok : allCells dLit 1 core_1_34 = true := by
  decide +kernel

theorem core_2_0_ok : allCells dLit 2 core_2_0 = true := by
  decide +kernel

end SandierSerfaty.CertData
