/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 116 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3420, …, 3449` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3420 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3420 = true := by
  decide +kernel

theorem chunk_3422 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3422 = true := by
  decide +kernel

theorem chunk_3424 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3424 = true := by
  decide +kernel

theorem chunk_3426 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3426 = true := by
  decide +kernel

theorem chunk_3428 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3428 = true := by
  decide +kernel

theorem chunk_3430 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3430 = true := by
  decide +kernel

theorem chunk_3432 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3432 = true := by
  decide +kernel

theorem chunk_3434 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3434 = true := by
  decide +kernel

theorem chunk_3436 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3436 = true := by
  decide +kernel

theorem chunk_3438 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3438 = true := by
  decide +kernel

theorem chunk_3440 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3440 = true := by
  decide +kernel

theorem chunk_3442 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3442 = true := by
  decide +kernel

theorem chunk_3444 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3444 = true := by
  decide +kernel

theorem chunk_3446 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3446 = true := by
  decide +kernel

theorem chunk_3448 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3448 = true := by
  decide +kernel

end SandierSerfaty.CertData
