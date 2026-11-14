/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 13 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_2_41_ok : allCells dLit 2 core_2_41 = true := by
  decide +kernel

theorem core_2_42_ok : allCells dLit 2 core_2_42 = true := by
  decide +kernel

theorem core_2_43_ok : allCells dLit 2 core_2_43 = true := by
  decide +kernel

theorem core_2_44_ok : allCells dLit 2 core_2_44 = true := by
  decide +kernel

theorem core_2_45_ok : allCells dLit 2 core_2_45 = true := by
  decide +kernel

theorem core_2_46_ok : allCells dLit 2 core_2_46 = true := by
  decide +kernel

theorem core_2_47_ok : allCells dLit 2 core_2_47 = true := by
  decide +kernel

theorem core_2_48_ok : allCells dLit 2 core_2_48 = true := by
  decide +kernel

end SandierSerfaty.CertData
