/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 56 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1850, …, 1862` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1850 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1850 = true := by
  decide +kernel

theorem chunk_1851 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1851 = true := by
  decide +kernel

theorem chunk_1852 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1852 = true := by
  decide +kernel

theorem chunk_1853 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1853 = true := by
  decide +kernel

theorem chunk_1854 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1854 = true := by
  decide +kernel

theorem chunk_1855 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1855 = true := by
  decide +kernel

theorem chunk_1856 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1856 = true := by
  decide +kernel

theorem chunk_1857 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1857 = true := by
  decide +kernel

theorem chunk_1858 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1858 = true := by
  decide +kernel

theorem chunk_1859 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1859 = true := by
  decide +kernel

theorem chunk_1860 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1860 = true := by
  decide +kernel

theorem chunk_1861 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1861 = true := by
  decide +kernel

theorem chunk_1862 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1862 = true := by
  decide +kernel

end SandierSerfaty.CertData
