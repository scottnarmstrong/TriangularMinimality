/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 28 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1474, …, 1503` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1474 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1474 = true := by
  decide +kernel

theorem chunk_1476 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1476 = true := by
  decide +kernel

theorem chunk_1478 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1478 = true := by
  decide +kernel

theorem chunk_1480 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1480 = true := by
  decide +kernel

theorem chunk_1482 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1482 = true := by
  decide +kernel

theorem chunk_1484 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1484 = true := by
  decide +kernel

theorem chunk_1486 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1486 = true := by
  decide +kernel

theorem chunk_1488 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1488 = true := by
  decide +kernel

theorem chunk_1490 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1490 = true := by
  decide +kernel

theorem chunk_1492 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1492 = true := by
  decide +kernel

theorem chunk_1494 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1494 = true := by
  decide +kernel

theorem chunk_1496 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1496 = true := by
  decide +kernel

theorem chunk_1498 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1498 = true := by
  decide +kernel

theorem chunk_1500 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1500 = true := by
  decide +kernel

theorem chunk_1502 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1502 = true := by
  decide +kernel

end SandierSerfaty.CertData
