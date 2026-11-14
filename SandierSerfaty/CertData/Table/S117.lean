/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 117 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3450, …, 3479` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3450 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3450 = true := by
  decide +kernel

theorem chunk_3452 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3452 = true := by
  decide +kernel

theorem chunk_3454 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3454 = true := by
  decide +kernel

theorem chunk_3456 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3456 = true := by
  decide +kernel

theorem chunk_3458 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3458 = true := by
  decide +kernel

theorem chunk_3460 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3460 = true := by
  decide +kernel

theorem chunk_3462 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3462 = true := by
  decide +kernel

theorem chunk_3464 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3464 = true := by
  decide +kernel

theorem chunk_3466 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3466 = true := by
  decide +kernel

theorem chunk_3468 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3468 = true := by
  decide +kernel

theorem chunk_3470 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3470 = true := by
  decide +kernel

theorem chunk_3472 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3472 = true := by
  decide +kernel

theorem chunk_3474 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3474 = true := by
  decide +kernel

theorem chunk_3476 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3476 = true := by
  decide +kernel

theorem chunk_3478 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3478 = true := by
  decide +kernel

end SandierSerfaty.CertData
