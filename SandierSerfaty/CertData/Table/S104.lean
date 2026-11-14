/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 104 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3060, …, 3089` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3060 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3060 = true := by
  decide +kernel

theorem chunk_3062 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3062 = true := by
  decide +kernel

theorem chunk_3064 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3064 = true := by
  decide +kernel

theorem chunk_3066 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3066 = true := by
  decide +kernel

theorem chunk_3068 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3068 = true := by
  decide +kernel

theorem chunk_3070 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3070 = true := by
  decide +kernel

theorem chunk_3072 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3072 = true := by
  decide +kernel

theorem chunk_3074 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3074 = true := by
  decide +kernel

theorem chunk_3076 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3076 = true := by
  decide +kernel

theorem chunk_3078 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3078 = true := by
  decide +kernel

theorem chunk_3080 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3080 = true := by
  decide +kernel

theorem chunk_3082 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3082 = true := by
  decide +kernel

theorem chunk_3084 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3084 = true := by
  decide +kernel

theorem chunk_3086 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3086 = true := by
  decide +kernel

theorem chunk_3088 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3088 = true := by
  decide +kernel

end SandierSerfaty.CertData
