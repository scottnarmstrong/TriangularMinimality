/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 114 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3360, …, 3389` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3360 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3360 = true := by
  decide +kernel

theorem chunk_3362 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3362 = true := by
  decide +kernel

theorem chunk_3364 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3364 = true := by
  decide +kernel

theorem chunk_3366 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3366 = true := by
  decide +kernel

theorem chunk_3368 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3368 = true := by
  decide +kernel

theorem chunk_3370 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3370 = true := by
  decide +kernel

theorem chunk_3372 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3372 = true := by
  decide +kernel

theorem chunk_3374 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3374 = true := by
  decide +kernel

theorem chunk_3376 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3376 = true := by
  decide +kernel

theorem chunk_3378 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3378 = true := by
  decide +kernel

theorem chunk_3380 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3380 = true := by
  decide +kernel

theorem chunk_3382 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3382 = true := by
  decide +kernel

theorem chunk_3384 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3384 = true := by
  decide +kernel

theorem chunk_3386 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3386 = true := by
  decide +kernel

theorem chunk_3388 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3388 = true := by
  decide +kernel

end SandierSerfaty.CertData
