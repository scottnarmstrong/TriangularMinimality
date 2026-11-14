/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 76 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2220, …, 2249` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2220 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2220 = true := by
  decide +kernel

theorem chunk_2222 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2222 = true := by
  decide +kernel

theorem chunk_2224 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2224 = true := by
  decide +kernel

theorem chunk_2226 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2226 = true := by
  decide +kernel

theorem chunk_2228 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2228 = true := by
  decide +kernel

theorem chunk_2230 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2230 = true := by
  decide +kernel

theorem chunk_2232 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2232 = true := by
  decide +kernel

theorem chunk_2234 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2234 = true := by
  decide +kernel

theorem chunk_2236 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2236 = true := by
  decide +kernel

theorem chunk_2238 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2238 = true := by
  decide +kernel

theorem chunk_2240 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2240 = true := by
  decide +kernel

theorem chunk_2242 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2242 = true := by
  decide +kernel

theorem chunk_2244 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2244 = true := by
  decide +kernel

theorem chunk_2246 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2246 = true := by
  decide +kernel

theorem chunk_2248 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2248 = true := by
  decide +kernel

end SandierSerfaty.CertData
