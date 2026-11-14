/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 48 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1746, …, 1758` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1746 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1746 = true := by
  decide +kernel

theorem chunk_1747 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1747 = true := by
  decide +kernel

theorem chunk_1748 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1748 = true := by
  decide +kernel

theorem chunk_1749 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1749 = true := by
  decide +kernel

theorem chunk_1750 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1750 = true := by
  decide +kernel

theorem chunk_1751 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1751 = true := by
  decide +kernel

theorem chunk_1752 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1752 = true := by
  decide +kernel

theorem chunk_1753 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1753 = true := by
  decide +kernel

theorem chunk_1754 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1754 = true := by
  decide +kernel

theorem chunk_1755 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1755 = true := by
  decide +kernel

theorem chunk_1756 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1756 = true := by
  decide +kernel

theorem chunk_1757 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1757 = true := by
  decide +kernel

theorem chunk_1758 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1758 = true := by
  decide +kernel

end SandierSerfaty.CertData
