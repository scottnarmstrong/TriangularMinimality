/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 26 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1414, …, 1443` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1414 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1414 = true := by
  decide +kernel

theorem chunk_1416 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1416 = true := by
  decide +kernel

theorem chunk_1418 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1418 = true := by
  decide +kernel

theorem chunk_1420 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1420 = true := by
  decide +kernel

theorem chunk_1422 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1422 = true := by
  decide +kernel

theorem chunk_1424 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1424 = true := by
  decide +kernel

theorem chunk_1426 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1426 = true := by
  decide +kernel

theorem chunk_1428 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1428 = true := by
  decide +kernel

theorem chunk_1430 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1430 = true := by
  decide +kernel

theorem chunk_1432 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1432 = true := by
  decide +kernel

theorem chunk_1434 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1434 = true := by
  decide +kernel

theorem chunk_1436 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1436 = true := by
  decide +kernel

theorem chunk_1438 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1438 = true := by
  decide +kernel

theorem chunk_1440 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1440 = true := by
  decide +kernel

theorem chunk_1442 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1442 = true := by
  decide +kernel

end SandierSerfaty.CertData
