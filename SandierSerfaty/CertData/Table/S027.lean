/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 27 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1444, …, 1473` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1444 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1444 = true := by
  decide +kernel

theorem chunk_1446 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1446 = true := by
  decide +kernel

theorem chunk_1448 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1448 = true := by
  decide +kernel

theorem chunk_1450 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1450 = true := by
  decide +kernel

theorem chunk_1452 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1452 = true := by
  decide +kernel

theorem chunk_1454 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1454 = true := by
  decide +kernel

theorem chunk_1456 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1456 = true := by
  decide +kernel

theorem chunk_1458 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1458 = true := by
  decide +kernel

theorem chunk_1460 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1460 = true := by
  decide +kernel

theorem chunk_1462 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1462 = true := by
  decide +kernel

theorem chunk_1464 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1464 = true := by
  decide +kernel

theorem chunk_1466 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1466 = true := by
  decide +kernel

theorem chunk_1468 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1468 = true := by
  decide +kernel

theorem chunk_1470 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1470 = true := by
  decide +kernel

theorem chunk_1472 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1472 = true := by
  decide +kernel

end SandierSerfaty.CertData
