/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 20 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1234, …, 1263` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1234 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1234 = true := by
  decide +kernel

theorem chunk_1236 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1236 = true := by
  decide +kernel

theorem chunk_1238 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1238 = true := by
  decide +kernel

theorem chunk_1240 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1240 = true := by
  decide +kernel

theorem chunk_1242 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1242 = true := by
  decide +kernel

theorem chunk_1244 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1244 = true := by
  decide +kernel

theorem chunk_1246 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1246 = true := by
  decide +kernel

theorem chunk_1248 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1248 = true := by
  decide +kernel

theorem chunk_1250 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1250 = true := by
  decide +kernel

theorem chunk_1252 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1252 = true := by
  decide +kernel

theorem chunk_1254 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1254 = true := by
  decide +kernel

theorem chunk_1256 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1256 = true := by
  decide +kernel

theorem chunk_1258 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1258 = true := by
  decide +kernel

theorem chunk_1260 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1260 = true := by
  decide +kernel

theorem chunk_1262 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1262 = true := by
  decide +kernel

end SandierSerfaty.CertData
