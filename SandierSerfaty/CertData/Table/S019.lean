/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 19 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1204, …, 1233` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1204 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1204 = true := by
  decide +kernel

theorem chunk_1206 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1206 = true := by
  decide +kernel

theorem chunk_1208 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1208 = true := by
  decide +kernel

theorem chunk_1210 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1210 = true := by
  decide +kernel

theorem chunk_1212 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1212 = true := by
  decide +kernel

theorem chunk_1214 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1214 = true := by
  decide +kernel

theorem chunk_1216 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1216 = true := by
  decide +kernel

theorem chunk_1218 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1218 = true := by
  decide +kernel

theorem chunk_1220 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1220 = true := by
  decide +kernel

theorem chunk_1222 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1222 = true := by
  decide +kernel

theorem chunk_1224 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1224 = true := by
  decide +kernel

theorem chunk_1226 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1226 = true := by
  decide +kernel

theorem chunk_1228 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1228 = true := by
  decide +kernel

theorem chunk_1230 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1230 = true := by
  decide +kernel

theorem chunk_1232 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1232 = true := by
  decide +kernel

end SandierSerfaty.CertData
