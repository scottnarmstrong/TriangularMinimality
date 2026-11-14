/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 36 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1590, …, 1602` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1590 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1590 = true := by
  decide +kernel

theorem chunk_1591 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1591 = true := by
  decide +kernel

theorem chunk_1592 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1592 = true := by
  decide +kernel

theorem chunk_1593 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1593 = true := by
  decide +kernel

theorem chunk_1594 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1594 = true := by
  decide +kernel

theorem chunk_1595 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1595 = true := by
  decide +kernel

theorem chunk_1596 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1596 = true := by
  decide +kernel

theorem chunk_1597 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1597 = true := by
  decide +kernel

theorem chunk_1598 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1598 = true := by
  decide +kernel

theorem chunk_1599 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1599 = true := by
  decide +kernel

theorem chunk_1600 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1600 = true := by
  decide +kernel

theorem chunk_1601 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1601 = true := by
  decide +kernel

theorem chunk_1602 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1602 = true := by
  decide +kernel

end SandierSerfaty.CertData
