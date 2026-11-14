/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 37 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1603, …, 1615` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1603 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1603 = true := by
  decide +kernel

theorem chunk_1604 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1604 = true := by
  decide +kernel

theorem chunk_1605 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1605 = true := by
  decide +kernel

theorem chunk_1606 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1606 = true := by
  decide +kernel

theorem chunk_1607 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1607 = true := by
  decide +kernel

theorem chunk_1608 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1608 = true := by
  decide +kernel

theorem chunk_1609 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1609 = true := by
  decide +kernel

theorem chunk_1610 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1610 = true := by
  decide +kernel

theorem chunk_1611 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1611 = true := by
  decide +kernel

theorem chunk_1612 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1612 = true := by
  decide +kernel

theorem chunk_1613 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1613 = true := by
  decide +kernel

theorem chunk_1614 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1614 = true := by
  decide +kernel

theorem chunk_1615 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1615 = true := by
  decide +kernel

end SandierSerfaty.CertData
