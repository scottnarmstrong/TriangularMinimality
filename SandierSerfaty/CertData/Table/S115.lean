/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 115 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3390, …, 3419` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3390 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3390 = true := by
  decide +kernel

theorem chunk_3392 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3392 = true := by
  decide +kernel

theorem chunk_3394 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3394 = true := by
  decide +kernel

theorem chunk_3396 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3396 = true := by
  decide +kernel

theorem chunk_3398 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3398 = true := by
  decide +kernel

theorem chunk_3400 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3400 = true := by
  decide +kernel

theorem chunk_3402 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3402 = true := by
  decide +kernel

theorem chunk_3404 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3404 = true := by
  decide +kernel

theorem chunk_3406 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3406 = true := by
  decide +kernel

theorem chunk_3408 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3408 = true := by
  decide +kernel

theorem chunk_3410 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3410 = true := by
  decide +kernel

theorem chunk_3412 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3412 = true := by
  decide +kernel

theorem chunk_3414 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3414 = true := by
  decide +kernel

theorem chunk_3416 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3416 = true := by
  decide +kernel

theorem chunk_3418 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3418 = true := by
  decide +kernel

end SandierSerfaty.CertData
