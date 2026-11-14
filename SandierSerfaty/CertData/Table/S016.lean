/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 16 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1114, …, 1143` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1114 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1114 = true := by
  decide +kernel

theorem chunk_1116 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1116 = true := by
  decide +kernel

theorem chunk_1118 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1118 = true := by
  decide +kernel

theorem chunk_1120 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1120 = true := by
  decide +kernel

theorem chunk_1122 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1122 = true := by
  decide +kernel

theorem chunk_1124 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1124 = true := by
  decide +kernel

theorem chunk_1126 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1126 = true := by
  decide +kernel

theorem chunk_1128 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1128 = true := by
  decide +kernel

theorem chunk_1130 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1130 = true := by
  decide +kernel

theorem chunk_1132 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1132 = true := by
  decide +kernel

theorem chunk_1134 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1134 = true := by
  decide +kernel

theorem chunk_1136 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1136 = true := by
  decide +kernel

theorem chunk_1138 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1138 = true := by
  decide +kernel

theorem chunk_1140 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1140 = true := by
  decide +kernel

theorem chunk_1142 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1142 = true := by
  decide +kernel

end SandierSerfaty.CertData
