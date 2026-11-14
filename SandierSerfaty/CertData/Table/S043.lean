/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 43 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1681, …, 1693` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1681 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1681 = true := by
  decide +kernel

theorem chunk_1682 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1682 = true := by
  decide +kernel

theorem chunk_1683 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1683 = true := by
  decide +kernel

theorem chunk_1684 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1684 = true := by
  decide +kernel

theorem chunk_1685 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1685 = true := by
  decide +kernel

theorem chunk_1686 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1686 = true := by
  decide +kernel

theorem chunk_1687 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1687 = true := by
  decide +kernel

theorem chunk_1688 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1688 = true := by
  decide +kernel

theorem chunk_1689 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1689 = true := by
  decide +kernel

theorem chunk_1690 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1690 = true := by
  decide +kernel

theorem chunk_1691 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1691 = true := by
  decide +kernel

theorem chunk_1692 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1692 = true := by
  decide +kernel

theorem chunk_1693 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1693 = true := by
  decide +kernel

end SandierSerfaty.CertData
