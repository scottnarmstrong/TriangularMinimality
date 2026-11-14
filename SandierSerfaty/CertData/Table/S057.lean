/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 57 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1863, …, 1875` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1863 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1863 = true := by
  decide +kernel

theorem chunk_1864 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1864 = true := by
  decide +kernel

theorem chunk_1865 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1865 = true := by
  decide +kernel

theorem chunk_1866 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1866 = true := by
  decide +kernel

theorem chunk_1867 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1867 = true := by
  decide +kernel

theorem chunk_1868 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1868 = true := by
  decide +kernel

theorem chunk_1869 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1869 = true := by
  decide +kernel

theorem chunk_1870 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1870 = true := by
  decide +kernel

theorem chunk_1871 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1871 = true := by
  decide +kernel

theorem chunk_1872 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1872 = true := by
  decide +kernel

theorem chunk_1873 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1873 = true := by
  decide +kernel

theorem chunk_1874 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1874 = true := by
  decide +kernel

theorem chunk_1875 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1875 = true := by
  decide +kernel

end SandierSerfaty.CertData
