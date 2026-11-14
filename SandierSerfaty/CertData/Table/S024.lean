/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 24 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1354, …, 1383` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1354 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1354 = true := by
  decide +kernel

theorem chunk_1356 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1356 = true := by
  decide +kernel

theorem chunk_1358 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1358 = true := by
  decide +kernel

theorem chunk_1360 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1360 = true := by
  decide +kernel

theorem chunk_1362 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1362 = true := by
  decide +kernel

theorem chunk_1364 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1364 = true := by
  decide +kernel

theorem chunk_1366 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1366 = true := by
  decide +kernel

theorem chunk_1368 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1368 = true := by
  decide +kernel

theorem chunk_1370 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1370 = true := by
  decide +kernel

theorem chunk_1372 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1372 = true := by
  decide +kernel

theorem chunk_1374 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1374 = true := by
  decide +kernel

theorem chunk_1376 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1376 = true := by
  decide +kernel

theorem chunk_1378 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1378 = true := by
  decide +kernel

theorem chunk_1380 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1380 = true := by
  decide +kernel

theorem chunk_1382 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1382 = true := by
  decide +kernel

end SandierSerfaty.CertData
