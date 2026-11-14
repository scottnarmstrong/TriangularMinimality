/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 33 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1551, …, 1563` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1551 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1551 = true := by
  decide +kernel

theorem chunk_1552 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1552 = true := by
  decide +kernel

theorem chunk_1553 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1553 = true := by
  decide +kernel

theorem chunk_1554 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1554 = true := by
  decide +kernel

theorem chunk_1555 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1555 = true := by
  decide +kernel

theorem chunk_1556 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1556 = true := by
  decide +kernel

theorem chunk_1557 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1557 = true := by
  decide +kernel

theorem chunk_1558 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1558 = true := by
  decide +kernel

theorem chunk_1559 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1559 = true := by
  decide +kernel

theorem chunk_1560 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1560 = true := by
  decide +kernel

theorem chunk_1561 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1561 = true := by
  decide +kernel

theorem chunk_1562 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1562 = true := by
  decide +kernel

theorem chunk_1563 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1563 = true := by
  decide +kernel

end SandierSerfaty.CertData
