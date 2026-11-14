/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 119 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3510, …, 3539` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3510 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3510 = true := by
  decide +kernel

theorem chunk_3512 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3512 = true := by
  decide +kernel

theorem chunk_3514 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3514 = true := by
  decide +kernel

theorem chunk_3516 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3516 = true := by
  decide +kernel

theorem chunk_3518 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3518 = true := by
  decide +kernel

theorem chunk_3520 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3520 = true := by
  decide +kernel

theorem chunk_3522 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3522 = true := by
  decide +kernel

theorem chunk_3524 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3524 = true := by
  decide +kernel

theorem chunk_3526 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3526 = true := by
  decide +kernel

theorem chunk_3528 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3528 = true := by
  decide +kernel

theorem chunk_3530 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3530 = true := by
  decide +kernel

theorem chunk_3532 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3532 = true := by
  decide +kernel

theorem chunk_3534 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3534 = true := by
  decide +kernel

theorem chunk_3536 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3536 = true := by
  decide +kernel

theorem chunk_3538 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3538 = true := by
  decide +kernel

end SandierSerfaty.CertData
