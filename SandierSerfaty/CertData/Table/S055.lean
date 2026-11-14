/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 55 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1837, …, 1849` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1837 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1837 = true := by
  decide +kernel

theorem chunk_1838 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1838 = true := by
  decide +kernel

theorem chunk_1839 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1839 = true := by
  decide +kernel

theorem chunk_1840 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1840 = true := by
  decide +kernel

theorem chunk_1841 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1841 = true := by
  decide +kernel

theorem chunk_1842 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1842 = true := by
  decide +kernel

theorem chunk_1843 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1843 = true := by
  decide +kernel

theorem chunk_1844 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1844 = true := by
  decide +kernel

theorem chunk_1845 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1845 = true := by
  decide +kernel

theorem chunk_1846 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1846 = true := by
  decide +kernel

theorem chunk_1847 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1847 = true := by
  decide +kernel

theorem chunk_1848 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1848 = true := by
  decide +kernel

theorem chunk_1849 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1849 = true := by
  decide +kernel

end SandierSerfaty.CertData
