/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 19 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_89_ok : allCells dLit 2 core_2_89 = true := by
  decide +kernel

theorem core_2_90_ok : allCells dLit 2 core_2_90 = true := by
  decide +kernel

theorem core_2_91_ok : allCells dLit 2 core_2_91 = true := by
  decide +kernel

theorem core_2_92_ok : allCells dLit 2 core_2_92 = true := by
  decide +kernel

theorem core_2_93_ok : allCells dLit 2 core_2_93 = true := by
  decide +kernel

theorem core_2_94_ok : allCells dLit 2 core_2_94 = true := by
  decide +kernel

theorem core_2_95_ok : allCells dLit 2 core_2_95 = true := by
  decide +kernel

theorem core_2_96_ok : allCells dLit 2 core_2_96 = true := by
  decide +kernel

end SandierSerfaty.CertData
