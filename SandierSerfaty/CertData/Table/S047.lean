/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 47 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1733, …, 1745` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1733 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1733 = true := by
  decide +kernel

theorem chunk_1734 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1734 = true := by
  decide +kernel

theorem chunk_1735 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1735 = true := by
  decide +kernel

theorem chunk_1736 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1736 = true := by
  decide +kernel

theorem chunk_1737 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1737 = true := by
  decide +kernel

theorem chunk_1738 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1738 = true := by
  decide +kernel

theorem chunk_1739 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1739 = true := by
  decide +kernel

theorem chunk_1740 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1740 = true := by
  decide +kernel

theorem chunk_1741 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1741 = true := by
  decide +kernel

theorem chunk_1742 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1742 = true := by
  decide +kernel

theorem chunk_1743 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1743 = true := by
  decide +kernel

theorem chunk_1744 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1744 = true := by
  decide +kernel

theorem chunk_1745 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1745 = true := by
  decide +kernel

end SandierSerfaty.CertData
