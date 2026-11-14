/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 71 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2070, …, 2099` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2070 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2070 = true := by
  decide +kernel

theorem chunk_2072 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2072 = true := by
  decide +kernel

theorem chunk_2074 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2074 = true := by
  decide +kernel

theorem chunk_2076 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2076 = true := by
  decide +kernel

theorem chunk_2078 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2078 = true := by
  decide +kernel

theorem chunk_2080 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2080 = true := by
  decide +kernel

theorem chunk_2082 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2082 = true := by
  decide +kernel

theorem chunk_2084 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2084 = true := by
  decide +kernel

theorem chunk_2086 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2086 = true := by
  decide +kernel

theorem chunk_2088 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2088 = true := by
  decide +kernel

theorem chunk_2090 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2090 = true := by
  decide +kernel

theorem chunk_2092 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2092 = true := by
  decide +kernel

theorem chunk_2094 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2094 = true := by
  decide +kernel

theorem chunk_2096 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2096 = true := by
  decide +kernel

theorem chunk_2098 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2098 = true := by
  decide +kernel

end SandierSerfaty.CertData
