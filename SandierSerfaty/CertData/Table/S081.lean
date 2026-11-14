/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 81 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2370, …, 2399` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2370 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2370 = true := by
  decide +kernel

theorem chunk_2372 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2372 = true := by
  decide +kernel

theorem chunk_2374 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2374 = true := by
  decide +kernel

theorem chunk_2376 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2376 = true := by
  decide +kernel

theorem chunk_2378 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2378 = true := by
  decide +kernel

theorem chunk_2380 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2380 = true := by
  decide +kernel

theorem chunk_2382 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2382 = true := by
  decide +kernel

theorem chunk_2384 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2384 = true := by
  decide +kernel

theorem chunk_2386 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2386 = true := by
  decide +kernel

theorem chunk_2388 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2388 = true := by
  decide +kernel

theorem chunk_2390 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2390 = true := by
  decide +kernel

theorem chunk_2392 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2392 = true := by
  decide +kernel

theorem chunk_2394 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2394 = true := by
  decide +kernel

theorem chunk_2396 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2396 = true := by
  decide +kernel

theorem chunk_2398 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2398 = true := by
  decide +kernel

end SandierSerfaty.CertData
