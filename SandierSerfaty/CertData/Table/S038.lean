/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 38 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1616, …, 1628` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1616 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1616 = true := by
  decide +kernel

theorem chunk_1617 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1617 = true := by
  decide +kernel

theorem chunk_1618 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1618 = true := by
  decide +kernel

theorem chunk_1619 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1619 = true := by
  decide +kernel

theorem chunk_1620 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1620 = true := by
  decide +kernel

theorem chunk_1621 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1621 = true := by
  decide +kernel

theorem chunk_1622 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1622 = true := by
  decide +kernel

theorem chunk_1623 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1623 = true := by
  decide +kernel

theorem chunk_1624 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1624 = true := by
  decide +kernel

theorem chunk_1625 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1625 = true := by
  decide +kernel

theorem chunk_1626 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1626 = true := by
  decide +kernel

theorem chunk_1627 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1627 = true := by
  decide +kernel

theorem chunk_1628 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1628 = true := by
  decide +kernel

end SandierSerfaty.CertData
