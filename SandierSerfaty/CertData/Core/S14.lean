/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 14 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_49_ok : allCells dLit 2 core_2_49 = true := by
  decide +kernel

theorem core_2_50_ok : allCells dLit 2 core_2_50 = true := by
  decide +kernel

theorem core_2_51_ok : allCells dLit 2 core_2_51 = true := by
  decide +kernel

theorem core_2_52_ok : allCells dLit 2 core_2_52 = true := by
  decide +kernel

theorem core_2_53_ok : allCells dLit 2 core_2_53 = true := by
  decide +kernel

theorem core_2_54_ok : allCells dLit 2 core_2_54 = true := by
  decide +kernel

theorem core_2_55_ok : allCells dLit 2 core_2_55 = true := by
  decide +kernel

theorem core_2_56_ok : allCells dLit 2 core_2_56 = true := by
  decide +kernel

end SandierSerfaty.CertData
