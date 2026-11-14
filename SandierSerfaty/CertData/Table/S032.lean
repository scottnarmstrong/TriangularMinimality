/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 32 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1538, …, 1550` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1538 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1538 = true := by
  decide +kernel

theorem chunk_1539 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1539 = true := by
  decide +kernel

theorem chunk_1540 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1540 = true := by
  decide +kernel

theorem chunk_1541 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1541 = true := by
  decide +kernel

theorem chunk_1542 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1542 = true := by
  decide +kernel

theorem chunk_1543 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1543 = true := by
  decide +kernel

theorem chunk_1544 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1544 = true := by
  decide +kernel

theorem chunk_1545 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1545 = true := by
  decide +kernel

theorem chunk_1546 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1546 = true := by
  decide +kernel

theorem chunk_1547 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1547 = true := by
  decide +kernel

theorem chunk_1548 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1548 = true := by
  decide +kernel

theorem chunk_1549 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1549 = true := by
  decide +kernel

theorem chunk_1550 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1550 = true := by
  decide +kernel

end SandierSerfaty.CertData
