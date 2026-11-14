/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 26 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_4_18_ok : allCells dLit 4 core_4_18 = true := by
  decide +kernel

theorem core_4_19_ok : allCells dLit 4 core_4_19 = true := by
  decide +kernel

theorem core_4_20_ok : allCells dLit 4 core_4_20 = true := by
  decide +kernel

theorem core_4_21_ok : allCells dLit 4 core_4_21 = true := by
  decide +kernel

theorem core_4_22_ok : allCells dLit 4 core_4_22 = true := by
  decide +kernel

theorem core_4_23_ok : allCells dLit 4 core_4_23 = true := by
  decide +kernel

theorem core_4_24_ok : allCells dLit 4 core_4_24 = true := by
  decide +kernel

theorem core_4_25_ok : allCells dLit 4 core_4_25 = true := by
  decide +kernel

end SandierSerfaty.CertData
