/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 58 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1876, …, 1888` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1876 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1876 = true := by
  decide +kernel

theorem chunk_1877 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1877 = true := by
  decide +kernel

theorem chunk_1878 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1878 = true := by
  decide +kernel

theorem chunk_1879 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1879 = true := by
  decide +kernel

theorem chunk_1880 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1880 = true := by
  decide +kernel

theorem chunk_1881 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1881 = true := by
  decide +kernel

theorem chunk_1882 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1882 = true := by
  decide +kernel

theorem chunk_1883 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1883 = true := by
  decide +kernel

theorem chunk_1884 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1884 = true := by
  decide +kernel

theorem chunk_1885 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1885 = true := by
  decide +kernel

theorem chunk_1886 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1886 = true := by
  decide +kernel

theorem chunk_1887 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1887 = true := by
  decide +kernel

theorem chunk_1888 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1888 = true := by
  decide +kernel

end SandierSerfaty.CertData
