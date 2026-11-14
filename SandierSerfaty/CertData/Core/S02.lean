/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 2 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_0_16_ok : allCells dLit 0 core_0_16 = true := by
  decide +kernel

theorem core_0_17_ok : allCells dLit 0 core_0_17 = true := by
  decide +kernel

theorem core_0_18_ok : allCells dLit 0 core_0_18 = true := by
  decide +kernel

theorem core_0_19_ok : allCells dLit 0 core_0_19 = true := by
  decide +kernel

theorem core_0_20_ok : allCells dLit 0 core_0_20 = true := by
  decide +kernel

theorem core_0_21_ok : allCells dLit 0 core_0_21 = true := by
  decide +kernel

theorem core_0_22_ok : allCells dLit 0 core_0_22 = true := by
  decide +kernel

theorem core_0_23_ok : allCells dLit 0 core_0_23 = true := by
  decide +kernel

end SandierSerfaty.CertData
