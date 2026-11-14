/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 44 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1694, …, 1706` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1694 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1694 = true := by
  decide +kernel

theorem chunk_1695 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1695 = true := by
  decide +kernel

theorem chunk_1696 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1696 = true := by
  decide +kernel

theorem chunk_1697 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1697 = true := by
  decide +kernel

theorem chunk_1698 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1698 = true := by
  decide +kernel

theorem chunk_1699 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1699 = true := by
  decide +kernel

theorem chunk_1700 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1700 = true := by
  decide +kernel

theorem chunk_1701 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1701 = true := by
  decide +kernel

theorem chunk_1702 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1702 = true := by
  decide +kernel

theorem chunk_1703 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1703 = true := by
  decide +kernel

theorem chunk_1704 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1704 = true := by
  decide +kernel

theorem chunk_1705 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1705 = true := by
  decide +kernel

theorem chunk_1706 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1706 = true := by
  decide +kernel

end SandierSerfaty.CertData
