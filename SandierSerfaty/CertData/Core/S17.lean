/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 17 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_73_ok : allCells dLit 2 core_2_73 = true := by
  decide +kernel

theorem core_2_74_ok : allCells dLit 2 core_2_74 = true := by
  decide +kernel

theorem core_2_75_ok : allCells dLit 2 core_2_75 = true := by
  decide +kernel

theorem core_2_76_ok : allCells dLit 2 core_2_76 = true := by
  decide +kernel

theorem core_2_77_ok : allCells dLit 2 core_2_77 = true := by
  decide +kernel

theorem core_2_78_ok : allCells dLit 2 core_2_78 = true := by
  decide +kernel

theorem core_2_79_ok : allCells dLit 2 core_2_79 = true := by
  decide +kernel

theorem core_2_80_ok : allCells dLit 2 core_2_80 = true := by
  decide +kernel

end SandierSerfaty.CertData
