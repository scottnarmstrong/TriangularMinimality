/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 112 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3300, …, 3329` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3300 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3300 = true := by
  decide +kernel

theorem chunk_3302 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3302 = true := by
  decide +kernel

theorem chunk_3304 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3304 = true := by
  decide +kernel

theorem chunk_3306 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3306 = true := by
  decide +kernel

theorem chunk_3308 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3308 = true := by
  decide +kernel

theorem chunk_3310 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3310 = true := by
  decide +kernel

theorem chunk_3312 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3312 = true := by
  decide +kernel

theorem chunk_3314 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3314 = true := by
  decide +kernel

theorem chunk_3316 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3316 = true := by
  decide +kernel

theorem chunk_3318 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3318 = true := by
  decide +kernel

theorem chunk_3320 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3320 = true := by
  decide +kernel

theorem chunk_3322 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3322 = true := by
  decide +kernel

theorem chunk_3324 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3324 = true := by
  decide +kernel

theorem chunk_3326 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3326 = true := by
  decide +kernel

theorem chunk_3328 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3328 = true := by
  decide +kernel

end SandierSerfaty.CertData
