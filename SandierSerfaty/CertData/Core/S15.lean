/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 15 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_57_ok : allCells dLit 2 core_2_57 = true := by
  decide +kernel

theorem core_2_58_ok : allCells dLit 2 core_2_58 = true := by
  decide +kernel

theorem core_2_59_ok : allCells dLit 2 core_2_59 = true := by
  decide +kernel

theorem core_2_60_ok : allCells dLit 2 core_2_60 = true := by
  decide +kernel

theorem core_2_61_ok : allCells dLit 2 core_2_61 = true := by
  decide +kernel

theorem core_2_62_ok : allCells dLit 2 core_2_62 = true := by
  decide +kernel

theorem core_2_63_ok : allCells dLit 2 core_2_63 = true := by
  decide +kernel

theorem core_2_64_ok : allCells dLit 2 core_2_64 = true := by
  decide +kernel

end SandierSerfaty.CertData
