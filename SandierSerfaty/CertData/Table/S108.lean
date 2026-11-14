/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 108 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3180, …, 3209` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3180 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3180 = true := by
  decide +kernel

theorem chunk_3182 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3182 = true := by
  decide +kernel

theorem chunk_3184 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3184 = true := by
  decide +kernel

theorem chunk_3186 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3186 = true := by
  decide +kernel

theorem chunk_3188 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3188 = true := by
  decide +kernel

theorem chunk_3190 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3190 = true := by
  decide +kernel

theorem chunk_3192 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3192 = true := by
  decide +kernel

theorem chunk_3194 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3194 = true := by
  decide +kernel

theorem chunk_3196 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3196 = true := by
  decide +kernel

theorem chunk_3198 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3198 = true := by
  decide +kernel

theorem chunk_3200 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3200 = true := by
  decide +kernel

theorem chunk_3202 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3202 = true := by
  decide +kernel

theorem chunk_3204 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3204 = true := by
  decide +kernel

theorem chunk_3206 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3206 = true := by
  decide +kernel

theorem chunk_3208 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3208 = true := by
  decide +kernel

end SandierSerfaty.CertData
