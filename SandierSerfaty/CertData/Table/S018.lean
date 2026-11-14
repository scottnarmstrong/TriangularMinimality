/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 18 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1174, …, 1203` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1174 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1174 = true := by
  decide +kernel

theorem chunk_1176 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1176 = true := by
  decide +kernel

theorem chunk_1178 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1178 = true := by
  decide +kernel

theorem chunk_1180 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1180 = true := by
  decide +kernel

theorem chunk_1182 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1182 = true := by
  decide +kernel

theorem chunk_1184 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1184 = true := by
  decide +kernel

theorem chunk_1186 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1186 = true := by
  decide +kernel

theorem chunk_1188 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1188 = true := by
  decide +kernel

theorem chunk_1190 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1190 = true := by
  decide +kernel

theorem chunk_1192 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1192 = true := by
  decide +kernel

theorem chunk_1194 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1194 = true := by
  decide +kernel

theorem chunk_1196 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1196 = true := by
  decide +kernel

theorem chunk_1198 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1198 = true := by
  decide +kernel

theorem chunk_1200 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1200 = true := by
  decide +kernel

theorem chunk_1202 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1202 = true := by
  decide +kernel

end SandierSerfaty.CertData
