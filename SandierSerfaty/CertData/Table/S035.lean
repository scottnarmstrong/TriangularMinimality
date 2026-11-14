/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 35 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1577, …, 1589` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1577 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1577 = true := by
  decide +kernel

theorem chunk_1578 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1578 = true := by
  decide +kernel

theorem chunk_1579 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1579 = true := by
  decide +kernel

theorem chunk_1580 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1580 = true := by
  decide +kernel

theorem chunk_1581 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1581 = true := by
  decide +kernel

theorem chunk_1582 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1582 = true := by
  decide +kernel

theorem chunk_1583 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1583 = true := by
  decide +kernel

theorem chunk_1584 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1584 = true := by
  decide +kernel

theorem chunk_1585 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1585 = true := by
  decide +kernel

theorem chunk_1586 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1586 = true := by
  decide +kernel

theorem chunk_1587 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1587 = true := by
  decide +kernel

theorem chunk_1588 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1588 = true := by
  decide +kernel

theorem chunk_1589 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1589 = true := by
  decide +kernel

end SandierSerfaty.CertData
