/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 34 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1564, …, 1576` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1564 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1564 = true := by
  decide +kernel

theorem chunk_1565 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1565 = true := by
  decide +kernel

theorem chunk_1566 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1566 = true := by
  decide +kernel

theorem chunk_1567 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1567 = true := by
  decide +kernel

theorem chunk_1568 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1568 = true := by
  decide +kernel

theorem chunk_1569 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1569 = true := by
  decide +kernel

theorem chunk_1570 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1570 = true := by
  decide +kernel

theorem chunk_1571 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1571 = true := by
  decide +kernel

theorem chunk_1572 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1572 = true := by
  decide +kernel

theorem chunk_1573 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1573 = true := by
  decide +kernel

theorem chunk_1574 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1574 = true := by
  decide +kernel

theorem chunk_1575 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1575 = true := by
  decide +kernel

theorem chunk_1576 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1576 = true := by
  decide +kernel

end SandierSerfaty.CertData
