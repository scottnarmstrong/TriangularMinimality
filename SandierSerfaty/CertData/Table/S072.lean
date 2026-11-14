/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 72 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2100, …, 2129` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2100 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2100 = true := by
  decide +kernel

theorem chunk_2102 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2102 = true := by
  decide +kernel

theorem chunk_2104 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2104 = true := by
  decide +kernel

theorem chunk_2106 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2106 = true := by
  decide +kernel

theorem chunk_2108 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2108 = true := by
  decide +kernel

theorem chunk_2110 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2110 = true := by
  decide +kernel

theorem chunk_2112 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2112 = true := by
  decide +kernel

theorem chunk_2114 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2114 = true := by
  decide +kernel

theorem chunk_2116 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2116 = true := by
  decide +kernel

theorem chunk_2118 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2118 = true := by
  decide +kernel

theorem chunk_2120 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2120 = true := by
  decide +kernel

theorem chunk_2122 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2122 = true := by
  decide +kernel

theorem chunk_2124 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2124 = true := by
  decide +kernel

theorem chunk_2126 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2126 = true := by
  decide +kernel

theorem chunk_2128 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2128 = true := by
  decide +kernel

end SandierSerfaty.CertData
