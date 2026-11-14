/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 46 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1720, …, 1732` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1720 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1720 = true := by
  decide +kernel

theorem chunk_1721 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1721 = true := by
  decide +kernel

theorem chunk_1722 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1722 = true := by
  decide +kernel

theorem chunk_1723 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1723 = true := by
  decide +kernel

theorem chunk_1724 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1724 = true := by
  decide +kernel

theorem chunk_1725 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1725 = true := by
  decide +kernel

theorem chunk_1726 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1726 = true := by
  decide +kernel

theorem chunk_1727 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1727 = true := by
  decide +kernel

theorem chunk_1728 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1728 = true := by
  decide +kernel

theorem chunk_1729 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1729 = true := by
  decide +kernel

theorem chunk_1730 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1730 = true := by
  decide +kernel

theorem chunk_1731 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1731 = true := by
  decide +kernel

theorem chunk_1732 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1732 = true := by
  decide +kernel

end SandierSerfaty.CertData
