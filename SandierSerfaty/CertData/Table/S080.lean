/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 80 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2340, …, 2369` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2340 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2340 = true := by
  decide +kernel

theorem chunk_2342 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2342 = true := by
  decide +kernel

theorem chunk_2344 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2344 = true := by
  decide +kernel

theorem chunk_2346 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2346 = true := by
  decide +kernel

theorem chunk_2348 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2348 = true := by
  decide +kernel

theorem chunk_2350 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2350 = true := by
  decide +kernel

theorem chunk_2352 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2352 = true := by
  decide +kernel

theorem chunk_2354 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2354 = true := by
  decide +kernel

theorem chunk_2356 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2356 = true := by
  decide +kernel

theorem chunk_2358 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2358 = true := by
  decide +kernel

theorem chunk_2360 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2360 = true := by
  decide +kernel

theorem chunk_2362 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2362 = true := by
  decide +kernel

theorem chunk_2364 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2364 = true := by
  decide +kernel

theorem chunk_2366 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2366 = true := by
  decide +kernel

theorem chunk_2368 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2368 = true := by
  decide +kernel

end SandierSerfaty.CertData
