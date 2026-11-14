/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 120 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3540, …, 3569` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3540 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3540 = true := by
  decide +kernel

theorem chunk_3542 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3542 = true := by
  decide +kernel

theorem chunk_3544 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3544 = true := by
  decide +kernel

theorem chunk_3546 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3546 = true := by
  decide +kernel

theorem chunk_3548 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3548 = true := by
  decide +kernel

theorem chunk_3550 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3550 = true := by
  decide +kernel

theorem chunk_3552 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3552 = true := by
  decide +kernel

theorem chunk_3554 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3554 = true := by
  decide +kernel

theorem chunk_3556 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3556 = true := by
  decide +kernel

theorem chunk_3558 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3558 = true := by
  decide +kernel

theorem chunk_3560 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3560 = true := by
  decide +kernel

theorem chunk_3562 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3562 = true := by
  decide +kernel

theorem chunk_3564 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3564 = true := by
  decide +kernel

theorem chunk_3566 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3566 = true := by
  decide +kernel

theorem chunk_3568 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3568 = true := by
  decide +kernel

end SandierSerfaty.CertData
