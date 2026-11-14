/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 106 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3120, …, 3149` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3120 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3120 = true := by
  decide +kernel

theorem chunk_3122 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3122 = true := by
  decide +kernel

theorem chunk_3124 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3124 = true := by
  decide +kernel

theorem chunk_3126 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3126 = true := by
  decide +kernel

theorem chunk_3128 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3128 = true := by
  decide +kernel

theorem chunk_3130 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3130 = true := by
  decide +kernel

theorem chunk_3132 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3132 = true := by
  decide +kernel

theorem chunk_3134 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3134 = true := by
  decide +kernel

theorem chunk_3136 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3136 = true := by
  decide +kernel

theorem chunk_3138 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3138 = true := by
  decide +kernel

theorem chunk_3140 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3140 = true := by
  decide +kernel

theorem chunk_3142 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3142 = true := by
  decide +kernel

theorem chunk_3144 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3144 = true := by
  decide +kernel

theorem chunk_3146 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3146 = true := by
  decide +kernel

theorem chunk_3148 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3148 = true := by
  decide +kernel

end SandierSerfaty.CertData
