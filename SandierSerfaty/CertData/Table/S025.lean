/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 25 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1384, …, 1413` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1384 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1384 = true := by
  decide +kernel

theorem chunk_1386 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1386 = true := by
  decide +kernel

theorem chunk_1388 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1388 = true := by
  decide +kernel

theorem chunk_1390 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1390 = true := by
  decide +kernel

theorem chunk_1392 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1392 = true := by
  decide +kernel

theorem chunk_1394 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1394 = true := by
  decide +kernel

theorem chunk_1396 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1396 = true := by
  decide +kernel

theorem chunk_1398 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1398 = true := by
  decide +kernel

theorem chunk_1400 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1400 = true := by
  decide +kernel

theorem chunk_1402 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1402 = true := by
  decide +kernel

theorem chunk_1404 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1404 = true := by
  decide +kernel

theorem chunk_1406 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1406 = true := by
  decide +kernel

theorem chunk_1408 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1408 = true := by
  decide +kernel

theorem chunk_1410 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1410 = true := by
  decide +kernel

theorem chunk_1412 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1412 = true := by
  decide +kernel

end SandierSerfaty.CertData
