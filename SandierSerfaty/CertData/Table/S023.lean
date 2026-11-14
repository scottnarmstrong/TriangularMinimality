/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 23 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1324, …, 1353` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1324 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1324 = true := by
  decide +kernel

theorem chunk_1326 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1326 = true := by
  decide +kernel

theorem chunk_1328 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1328 = true := by
  decide +kernel

theorem chunk_1330 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1330 = true := by
  decide +kernel

theorem chunk_1332 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1332 = true := by
  decide +kernel

theorem chunk_1334 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1334 = true := by
  decide +kernel

theorem chunk_1336 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1336 = true := by
  decide +kernel

theorem chunk_1338 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1338 = true := by
  decide +kernel

theorem chunk_1340 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1340 = true := by
  decide +kernel

theorem chunk_1342 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1342 = true := by
  decide +kernel

theorem chunk_1344 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1344 = true := by
  decide +kernel

theorem chunk_1346 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1346 = true := by
  decide +kernel

theorem chunk_1348 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1348 = true := by
  decide +kernel

theorem chunk_1350 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1350 = true := by
  decide +kernel

theorem chunk_1352 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1352 = true := by
  decide +kernel

end SandierSerfaty.CertData
