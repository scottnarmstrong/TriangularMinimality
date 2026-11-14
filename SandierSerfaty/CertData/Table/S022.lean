/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 22 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1294, …, 1323` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1294 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1294 = true := by
  decide +kernel

theorem chunk_1296 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1296 = true := by
  decide +kernel

theorem chunk_1298 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1298 = true := by
  decide +kernel

theorem chunk_1300 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1300 = true := by
  decide +kernel

theorem chunk_1302 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1302 = true := by
  decide +kernel

theorem chunk_1304 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1304 = true := by
  decide +kernel

theorem chunk_1306 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1306 = true := by
  decide +kernel

theorem chunk_1308 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1308 = true := by
  decide +kernel

theorem chunk_1310 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1310 = true := by
  decide +kernel

theorem chunk_1312 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1312 = true := by
  decide +kernel

theorem chunk_1314 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1314 = true := by
  decide +kernel

theorem chunk_1316 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1316 = true := by
  decide +kernel

theorem chunk_1318 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1318 = true := by
  decide +kernel

theorem chunk_1320 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1320 = true := by
  decide +kernel

theorem chunk_1322 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1322 = true := by
  decide +kernel

end SandierSerfaty.CertData
