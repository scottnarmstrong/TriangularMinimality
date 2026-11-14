/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 14 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1054, …, 1083` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1054 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1054 = true := by
  decide +kernel

theorem chunk_1056 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1056 = true := by
  decide +kernel

theorem chunk_1058 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1058 = true := by
  decide +kernel

theorem chunk_1060 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1060 = true := by
  decide +kernel

theorem chunk_1062 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1062 = true := by
  decide +kernel

theorem chunk_1064 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1064 = true := by
  decide +kernel

theorem chunk_1066 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1066 = true := by
  decide +kernel

theorem chunk_1068 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1068 = true := by
  decide +kernel

theorem chunk_1070 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1070 = true := by
  decide +kernel

theorem chunk_1072 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1072 = true := by
  decide +kernel

theorem chunk_1074 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1074 = true := by
  decide +kernel

theorem chunk_1076 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1076 = true := by
  decide +kernel

theorem chunk_1078 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1078 = true := by
  decide +kernel

theorem chunk_1080 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1080 = true := by
  decide +kernel

theorem chunk_1082 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1082 = true := by
  decide +kernel

end SandierSerfaty.CertData
