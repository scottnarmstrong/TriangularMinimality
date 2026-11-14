/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 15 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1084, …, 1113` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1084 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1084 = true := by
  decide +kernel

theorem chunk_1086 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1086 = true := by
  decide +kernel

theorem chunk_1088 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1088 = true := by
  decide +kernel

theorem chunk_1090 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1090 = true := by
  decide +kernel

theorem chunk_1092 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1092 = true := by
  decide +kernel

theorem chunk_1094 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1094 = true := by
  decide +kernel

theorem chunk_1096 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1096 = true := by
  decide +kernel

theorem chunk_1098 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1098 = true := by
  decide +kernel

theorem chunk_1100 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1100 = true := by
  decide +kernel

theorem chunk_1102 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1102 = true := by
  decide +kernel

theorem chunk_1104 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1104 = true := by
  decide +kernel

theorem chunk_1106 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1106 = true := by
  decide +kernel

theorem chunk_1108 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1108 = true := by
  decide +kernel

theorem chunk_1110 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1110 = true := by
  decide +kernel

theorem chunk_1112 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1112 = true := by
  decide +kernel

end SandierSerfaty.CertData
