/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 111 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3270, …, 3299` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3270 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3270 = true := by
  decide +kernel

theorem chunk_3272 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3272 = true := by
  decide +kernel

theorem chunk_3274 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3274 = true := by
  decide +kernel

theorem chunk_3276 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3276 = true := by
  decide +kernel

theorem chunk_3278 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3278 = true := by
  decide +kernel

theorem chunk_3280 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3280 = true := by
  decide +kernel

theorem chunk_3282 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3282 = true := by
  decide +kernel

theorem chunk_3284 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3284 = true := by
  decide +kernel

theorem chunk_3286 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3286 = true := by
  decide +kernel

theorem chunk_3288 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3288 = true := by
  decide +kernel

theorem chunk_3290 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3290 = true := by
  decide +kernel

theorem chunk_3292 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3292 = true := by
  decide +kernel

theorem chunk_3294 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3294 = true := by
  decide +kernel

theorem chunk_3296 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3296 = true := by
  decide +kernel

theorem chunk_3298 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3298 = true := by
  decide +kernel

end SandierSerfaty.CertData
