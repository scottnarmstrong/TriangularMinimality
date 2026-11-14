/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 107 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3150, …, 3179` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3150 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3150 = true := by
  decide +kernel

theorem chunk_3152 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3152 = true := by
  decide +kernel

theorem chunk_3154 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3154 = true := by
  decide +kernel

theorem chunk_3156 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3156 = true := by
  decide +kernel

theorem chunk_3158 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3158 = true := by
  decide +kernel

theorem chunk_3160 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3160 = true := by
  decide +kernel

theorem chunk_3162 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3162 = true := by
  decide +kernel

theorem chunk_3164 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3164 = true := by
  decide +kernel

theorem chunk_3166 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3166 = true := by
  decide +kernel

theorem chunk_3168 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3168 = true := by
  decide +kernel

theorem chunk_3170 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3170 = true := by
  decide +kernel

theorem chunk_3172 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3172 = true := by
  decide +kernel

theorem chunk_3174 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3174 = true := by
  decide +kernel

theorem chunk_3176 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3176 = true := by
  decide +kernel

theorem chunk_3178 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3178 = true := by
  decide +kernel

end SandierSerfaty.CertData
