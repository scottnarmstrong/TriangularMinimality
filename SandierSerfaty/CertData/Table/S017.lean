/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 17 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1144, …, 1173` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1144 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1144 = true := by
  decide +kernel

theorem chunk_1146 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1146 = true := by
  decide +kernel

theorem chunk_1148 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1148 = true := by
  decide +kernel

theorem chunk_1150 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1150 = true := by
  decide +kernel

theorem chunk_1152 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1152 = true := by
  decide +kernel

theorem chunk_1154 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1154 = true := by
  decide +kernel

theorem chunk_1156 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1156 = true := by
  decide +kernel

theorem chunk_1158 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1158 = true := by
  decide +kernel

theorem chunk_1160 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1160 = true := by
  decide +kernel

theorem chunk_1162 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1162 = true := by
  decide +kernel

theorem chunk_1164 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1164 = true := by
  decide +kernel

theorem chunk_1166 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1166 = true := by
  decide +kernel

theorem chunk_1168 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1168 = true := by
  decide +kernel

theorem chunk_1170 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1170 = true := by
  decide +kernel

theorem chunk_1172 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1172 = true := by
  decide +kernel

end SandierSerfaty.CertData
