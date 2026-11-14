/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 21 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1264, …, 1293` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1264 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1264 = true := by
  decide +kernel

theorem chunk_1266 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1266 = true := by
  decide +kernel

theorem chunk_1268 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1268 = true := by
  decide +kernel

theorem chunk_1270 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1270 = true := by
  decide +kernel

theorem chunk_1272 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1272 = true := by
  decide +kernel

theorem chunk_1274 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1274 = true := by
  decide +kernel

theorem chunk_1276 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1276 = true := by
  decide +kernel

theorem chunk_1278 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1278 = true := by
  decide +kernel

theorem chunk_1280 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1280 = true := by
  decide +kernel

theorem chunk_1282 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1282 = true := by
  decide +kernel

theorem chunk_1284 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1284 = true := by
  decide +kernel

theorem chunk_1286 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1286 = true := by
  decide +kernel

theorem chunk_1288 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1288 = true := by
  decide +kernel

theorem chunk_1290 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1290 = true := by
  decide +kernel

theorem chunk_1292 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1292 = true := by
  decide +kernel

end SandierSerfaty.CertData
