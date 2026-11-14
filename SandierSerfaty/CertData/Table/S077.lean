/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 77 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2250, …, 2279` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2250 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2250 = true := by
  decide +kernel

theorem chunk_2252 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2252 = true := by
  decide +kernel

theorem chunk_2254 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2254 = true := by
  decide +kernel

theorem chunk_2256 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2256 = true := by
  decide +kernel

theorem chunk_2258 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2258 = true := by
  decide +kernel

theorem chunk_2260 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2260 = true := by
  decide +kernel

theorem chunk_2262 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2262 = true := by
  decide +kernel

theorem chunk_2264 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2264 = true := by
  decide +kernel

theorem chunk_2266 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2266 = true := by
  decide +kernel

theorem chunk_2268 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2268 = true := by
  decide +kernel

theorem chunk_2270 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2270 = true := by
  decide +kernel

theorem chunk_2272 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2272 = true := by
  decide +kernel

theorem chunk_2274 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2274 = true := by
  decide +kernel

theorem chunk_2276 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2276 = true := by
  decide +kernel

theorem chunk_2278 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2278 = true := by
  decide +kernel

end SandierSerfaty.CertData
