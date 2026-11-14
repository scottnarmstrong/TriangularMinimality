/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.Cells

/-!
# Assertion A2, shard 27 (kernel)

`decide +kernel` shards of the finite-core test on pieces of the core cells.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem core_4_26_ok : allCells dLit 4 core_4_26 = true := by
  decide +kernel

theorem core_4_27_ok : allCells dLit 4 core_4_27 = true := by
  decide +kernel

theorem core_4_28_ok : allCells dLit 4 core_4_28 = true := by
  decide +kernel

theorem core_4_29_ok : allCells dLit 4 core_4_29 = true := by
  decide +kernel

theorem core_4_30_ok : allCells dLit 4 core_4_30 = true := by
  decide +kernel

theorem core_4_31_ok : allCells dLit 4 core_4_31 = true := by
  decide +kernel

theorem core_4_32_ok : allCells dLit 4 core_4_32 = true := by
  decide +kernel

theorem core_4_33_ok : allCells dLit 4 core_4_33 = true := by
  decide +kernel

end SandierSerfaty.CertData
