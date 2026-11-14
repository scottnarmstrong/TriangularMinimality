/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 113 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3330, …, 3359` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3330 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3330 = true := by
  decide +kernel

theorem chunk_3332 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3332 = true := by
  decide +kernel

theorem chunk_3334 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3334 = true := by
  decide +kernel

theorem chunk_3336 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3336 = true := by
  decide +kernel

theorem chunk_3338 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3338 = true := by
  decide +kernel

theorem chunk_3340 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3340 = true := by
  decide +kernel

theorem chunk_3342 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3342 = true := by
  decide +kernel

theorem chunk_3344 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3344 = true := by
  decide +kernel

theorem chunk_3346 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3346 = true := by
  decide +kernel

theorem chunk_3348 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3348 = true := by
  decide +kernel

theorem chunk_3350 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3350 = true := by
  decide +kernel

theorem chunk_3352 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3352 = true := by
  decide +kernel

theorem chunk_3354 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3354 = true := by
  decide +kernel

theorem chunk_3356 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3356 = true := by
  decide +kernel

theorem chunk_3358 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3358 = true := by
  decide +kernel

end SandierSerfaty.CertData
