/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 11 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_25_ok : allCells dLit 2 core_2_25 = true := by
  decide +kernel

theorem core_2_26_ok : allCells dLit 2 core_2_26 = true := by
  decide +kernel

theorem core_2_27_ok : allCells dLit 2 core_2_27 = true := by
  decide +kernel

theorem core_2_28_ok : allCells dLit 2 core_2_28 = true := by
  decide +kernel

theorem core_2_29_ok : allCells dLit 2 core_2_29 = true := by
  decide +kernel

theorem core_2_30_ok : allCells dLit 2 core_2_30 = true := by
  decide +kernel

theorem core_2_31_ok : allCells dLit 2 core_2_31 = true := by
  decide +kernel

theorem core_2_32_ok : allCells dLit 2 core_2_32 = true := by
  decide +kernel

end SandierSerfaty.CertData
