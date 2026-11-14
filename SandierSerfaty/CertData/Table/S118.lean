/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 118 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3480, …, 3509` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3480 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3480 = true := by
  decide +kernel

theorem chunk_3482 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3482 = true := by
  decide +kernel

theorem chunk_3484 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3484 = true := by
  decide +kernel

theorem chunk_3486 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3486 = true := by
  decide +kernel

theorem chunk_3488 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3488 = true := by
  decide +kernel

theorem chunk_3490 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3490 = true := by
  decide +kernel

theorem chunk_3492 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3492 = true := by
  decide +kernel

theorem chunk_3494 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3494 = true := by
  decide +kernel

theorem chunk_3496 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3496 = true := by
  decide +kernel

theorem chunk_3498 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3498 = true := by
  decide +kernel

theorem chunk_3500 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3500 = true := by
  decide +kernel

theorem chunk_3502 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3502 = true := by
  decide +kernel

theorem chunk_3504 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3504 = true := by
  decide +kernel

theorem chunk_3506 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3506 = true := by
  decide +kernel

theorem chunk_3508 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3508 = true := by
  decide +kernel

end SandierSerfaty.CertData
