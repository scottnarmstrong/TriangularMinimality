/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 105 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3090, …, 3119` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3090 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3090 = true := by
  decide +kernel

theorem chunk_3092 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3092 = true := by
  decide +kernel

theorem chunk_3094 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3094 = true := by
  decide +kernel

theorem chunk_3096 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3096 = true := by
  decide +kernel

theorem chunk_3098 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3098 = true := by
  decide +kernel

theorem chunk_3100 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3100 = true := by
  decide +kernel

theorem chunk_3102 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3102 = true := by
  decide +kernel

theorem chunk_3104 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3104 = true := by
  decide +kernel

theorem chunk_3106 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3106 = true := by
  decide +kernel

theorem chunk_3108 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3108 = true := by
  decide +kernel

theorem chunk_3110 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3110 = true := by
  decide +kernel

theorem chunk_3112 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3112 = true := by
  decide +kernel

theorem chunk_3114 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3114 = true := by
  decide +kernel

theorem chunk_3116 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3116 = true := by
  decide +kernel

theorem chunk_3118 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3118 = true := by
  decide +kernel

end SandierSerfaty.CertData
