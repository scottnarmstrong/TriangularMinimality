/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 45 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1707, …, 1719` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1707 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1707 = true := by
  decide +kernel

theorem chunk_1708 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1708 = true := by
  decide +kernel

theorem chunk_1709 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1709 = true := by
  decide +kernel

theorem chunk_1710 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1710 = true := by
  decide +kernel

theorem chunk_1711 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1711 = true := by
  decide +kernel

theorem chunk_1712 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1712 = true := by
  decide +kernel

theorem chunk_1713 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1713 = true := by
  decide +kernel

theorem chunk_1714 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1714 = true := by
  decide +kernel

theorem chunk_1715 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1715 = true := by
  decide +kernel

theorem chunk_1716 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1716 = true := by
  decide +kernel

theorem chunk_1717 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1717 = true := by
  decide +kernel

theorem chunk_1718 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1718 = true := by
  decide +kernel

theorem chunk_1719 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1719 = true := by
  decide +kernel

end SandierSerfaty.CertData
