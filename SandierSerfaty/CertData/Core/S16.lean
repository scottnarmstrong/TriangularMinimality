/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 16 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_65_ok : allCells dLit 2 core_2_65 = true := by
  decide +kernel

theorem core_2_66_ok : allCells dLit 2 core_2_66 = true := by
  decide +kernel

theorem core_2_67_ok : allCells dLit 2 core_2_67 = true := by
  decide +kernel

theorem core_2_68_ok : allCells dLit 2 core_2_68 = true := by
  decide +kernel

theorem core_2_69_ok : allCells dLit 2 core_2_69 = true := by
  decide +kernel

theorem core_2_70_ok : allCells dLit 2 core_2_70 = true := by
  decide +kernel

theorem core_2_71_ok : allCells dLit 2 core_2_71 = true := by
  decide +kernel

theorem core_2_72_ok : allCells dLit 2 core_2_72 = true := by
  decide +kernel

end SandierSerfaty.CertData
