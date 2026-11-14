/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 78 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2280, …, 2309` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2280 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2280 = true := by
  decide +kernel

theorem chunk_2282 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2282 = true := by
  decide +kernel

theorem chunk_2284 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2284 = true := by
  decide +kernel

theorem chunk_2286 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2286 = true := by
  decide +kernel

theorem chunk_2288 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2288 = true := by
  decide +kernel

theorem chunk_2290 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2290 = true := by
  decide +kernel

theorem chunk_2292 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2292 = true := by
  decide +kernel

theorem chunk_2294 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2294 = true := by
  decide +kernel

theorem chunk_2296 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2296 = true := by
  decide +kernel

theorem chunk_2298 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2298 = true := by
  decide +kernel

theorem chunk_2300 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2300 = true := by
  decide +kernel

theorem chunk_2302 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2302 = true := by
  decide +kernel

theorem chunk_2304 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2304 = true := by
  decide +kernel

theorem chunk_2306 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2306 = true := by
  decide +kernel

theorem chunk_2308 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2308 = true := by
  decide +kernel

end SandierSerfaty.CertData
