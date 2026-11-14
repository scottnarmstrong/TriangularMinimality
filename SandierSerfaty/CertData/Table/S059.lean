/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 59 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1889, …, 1901` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1889 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1889 = true := by
  decide +kernel

theorem chunk_1890 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1890 = true := by
  decide +kernel

theorem chunk_1891 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1891 = true := by
  decide +kernel

theorem chunk_1892 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1892 = true := by
  decide +kernel

theorem chunk_1893 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1893 = true := by
  decide +kernel

theorem chunk_1894 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1894 = true := by
  decide +kernel

theorem chunk_1895 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1895 = true := by
  decide +kernel

theorem chunk_1896 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1896 = true := by
  decide +kernel

theorem chunk_1897 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1897 = true := by
  decide +kernel

theorem chunk_1898 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1898 = true := by
  decide +kernel

theorem chunk_1899 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1899 = true := by
  decide +kernel

theorem chunk_1900 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1900 = true := by
  decide +kernel

theorem chunk_1901 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1901 = true := by
  decide +kernel

end SandierSerfaty.CertData
