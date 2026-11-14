/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 74 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2160, …, 2189` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2160 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2160 = true := by
  decide +kernel

theorem chunk_2162 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2162 = true := by
  decide +kernel

theorem chunk_2164 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2164 = true := by
  decide +kernel

theorem chunk_2166 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2166 = true := by
  decide +kernel

theorem chunk_2168 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2168 = true := by
  decide +kernel

theorem chunk_2170 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2170 = true := by
  decide +kernel

theorem chunk_2172 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2172 = true := by
  decide +kernel

theorem chunk_2174 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2174 = true := by
  decide +kernel

theorem chunk_2176 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2176 = true := by
  decide +kernel

theorem chunk_2178 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2178 = true := by
  decide +kernel

theorem chunk_2180 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2180 = true := by
  decide +kernel

theorem chunk_2182 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2182 = true := by
  decide +kernel

theorem chunk_2184 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2184 = true := by
  decide +kernel

theorem chunk_2186 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2186 = true := by
  decide +kernel

theorem chunk_2188 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2188 = true := by
  decide +kernel

end SandierSerfaty.CertData
