/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 31 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1525, …, 1537` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1525 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1525 = true := by
  decide +kernel

theorem chunk_1526 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1526 = true := by
  decide +kernel

theorem chunk_1527 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1527 = true := by
  decide +kernel

theorem chunk_1528 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1528 = true := by
  decide +kernel

theorem chunk_1529 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1529 = true := by
  decide +kernel

theorem chunk_1530 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1530 = true := by
  decide +kernel

theorem chunk_1531 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1531 = true := by
  decide +kernel

theorem chunk_1532 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1532 = true := by
  decide +kernel

theorem chunk_1533 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1533 = true := by
  decide +kernel

theorem chunk_1534 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1534 = true := by
  decide +kernel

theorem chunk_1535 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1535 = true := by
  decide +kernel

theorem chunk_1536 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1536 = true := by
  decide +kernel

theorem chunk_1537 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1537 = true := by
  decide +kernel

end SandierSerfaty.CertData
