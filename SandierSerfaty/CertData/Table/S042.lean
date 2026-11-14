/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 42 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1668, …, 1680` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1668 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1668 = true := by
  decide +kernel

theorem chunk_1669 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1669 = true := by
  decide +kernel

theorem chunk_1670 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1670 = true := by
  decide +kernel

theorem chunk_1671 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1671 = true := by
  decide +kernel

theorem chunk_1672 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1672 = true := by
  decide +kernel

theorem chunk_1673 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1673 = true := by
  decide +kernel

theorem chunk_1674 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1674 = true := by
  decide +kernel

theorem chunk_1675 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1675 = true := by
  decide +kernel

theorem chunk_1676 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1676 = true := by
  decide +kernel

theorem chunk_1677 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1677 = true := by
  decide +kernel

theorem chunk_1678 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1678 = true := by
  decide +kernel

theorem chunk_1679 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1679 = true := by
  decide +kernel

theorem chunk_1680 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1680 = true := by
  decide +kernel

end SandierSerfaty.CertData
