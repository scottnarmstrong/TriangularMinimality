/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 30 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1512, …, 1524` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1512 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1512 = true := by
  decide +kernel

theorem chunk_1513 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1513 = true := by
  decide +kernel

theorem chunk_1514 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1514 = true := by
  decide +kernel

theorem chunk_1515 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1515 = true := by
  decide +kernel

theorem chunk_1516 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1516 = true := by
  decide +kernel

theorem chunk_1517 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1517 = true := by
  decide +kernel

theorem chunk_1518 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1518 = true := by
  decide +kernel

theorem chunk_1519 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1519 = true := by
  decide +kernel

theorem chunk_1520 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1520 = true := by
  decide +kernel

theorem chunk_1521 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1521 = true := by
  decide +kernel

theorem chunk_1522 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1522 = true := by
  decide +kernel

theorem chunk_1523 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1523 = true := by
  decide +kernel

theorem chunk_1524 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1524 = true := by
  decide +kernel

end SandierSerfaty.CertData
