/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 20 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_97_ok : allCells dLit 2 core_2_97 = true := by
  decide +kernel

theorem core_2_98_ok : allCells dLit 2 core_2_98 = true := by
  decide +kernel

theorem core_2_99_ok : allCells dLit 2 core_2_99 = true := by
  decide +kernel

theorem core_2_100_ok : allCells dLit 2 core_2_100 = true := by
  decide +kernel

theorem core_2_101_ok : allCells dLit 2 core_2_101 = true := by
  decide +kernel

theorem core_2_102_ok : allCells dLit 2 core_2_102 = true := by
  decide +kernel

theorem core_2_103_ok : allCells dLit 2 core_2_103 = true := by
  decide +kernel

theorem core_2_104_ok : allCells dLit 2 core_2_104 = true := by
  decide +kernel

end SandierSerfaty.CertData
