/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 110 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3240, …, 3269` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3240 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3240 = true := by
  decide +kernel

theorem chunk_3242 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3242 = true := by
  decide +kernel

theorem chunk_3244 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3244 = true := by
  decide +kernel

theorem chunk_3246 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3246 = true := by
  decide +kernel

theorem chunk_3248 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3248 = true := by
  decide +kernel

theorem chunk_3250 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3250 = true := by
  decide +kernel

theorem chunk_3252 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3252 = true := by
  decide +kernel

theorem chunk_3254 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3254 = true := by
  decide +kernel

theorem chunk_3256 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3256 = true := by
  decide +kernel

theorem chunk_3258 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3258 = true := by
  decide +kernel

theorem chunk_3260 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3260 = true := by
  decide +kernel

theorem chunk_3262 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3262 = true := by
  decide +kernel

theorem chunk_3264 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3264 = true := by
  decide +kernel

theorem chunk_3266 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3266 = true := by
  decide +kernel

theorem chunk_3268 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3268 = true := by
  decide +kernel

end SandierSerfaty.CertData
