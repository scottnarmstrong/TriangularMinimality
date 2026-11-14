/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 109 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3210, …, 3239` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3210 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3210 = true := by
  decide +kernel

theorem chunk_3212 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3212 = true := by
  decide +kernel

theorem chunk_3214 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3214 = true := by
  decide +kernel

theorem chunk_3216 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3216 = true := by
  decide +kernel

theorem chunk_3218 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3218 = true := by
  decide +kernel

theorem chunk_3220 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3220 = true := by
  decide +kernel

theorem chunk_3222 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3222 = true := by
  decide +kernel

theorem chunk_3224 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3224 = true := by
  decide +kernel

theorem chunk_3226 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3226 = true := by
  decide +kernel

theorem chunk_3228 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3228 = true := by
  decide +kernel

theorem chunk_3230 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3230 = true := by
  decide +kernel

theorem chunk_3232 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3232 = true := by
  decide +kernel

theorem chunk_3234 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3234 = true := by
  decide +kernel

theorem chunk_3236 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3236 = true := by
  decide +kernel

theorem chunk_3238 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3238 = true := by
  decide +kernel

end SandierSerfaty.CertData
