/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 40 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1642, …, 1654` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1642 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1642 = true := by
  decide +kernel

theorem chunk_1643 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1643 = true := by
  decide +kernel

theorem chunk_1644 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1644 = true := by
  decide +kernel

theorem chunk_1645 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1645 = true := by
  decide +kernel

theorem chunk_1646 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1646 = true := by
  decide +kernel

theorem chunk_1647 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1647 = true := by
  decide +kernel

theorem chunk_1648 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1648 = true := by
  decide +kernel

theorem chunk_1649 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1649 = true := by
  decide +kernel

theorem chunk_1650 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1650 = true := by
  decide +kernel

theorem chunk_1651 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1651 = true := by
  decide +kernel

theorem chunk_1652 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1652 = true := by
  decide +kernel

theorem chunk_1653 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1653 = true := by
  decide +kernel

theorem chunk_1654 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1654 = true := by
  decide +kernel

end SandierSerfaty.CertData
