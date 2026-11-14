/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 79 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2310, …, 2339` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2310 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2310 = true := by
  decide +kernel

theorem chunk_2312 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2312 = true := by
  decide +kernel

theorem chunk_2314 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2314 = true := by
  decide +kernel

theorem chunk_2316 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2316 = true := by
  decide +kernel

theorem chunk_2318 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2318 = true := by
  decide +kernel

theorem chunk_2320 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2320 = true := by
  decide +kernel

theorem chunk_2322 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2322 = true := by
  decide +kernel

theorem chunk_2324 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2324 = true := by
  decide +kernel

theorem chunk_2326 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2326 = true := by
  decide +kernel

theorem chunk_2328 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2328 = true := by
  decide +kernel

theorem chunk_2330 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2330 = true := by
  decide +kernel

theorem chunk_2332 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2332 = true := by
  decide +kernel

theorem chunk_2334 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2334 = true := by
  decide +kernel

theorem chunk_2336 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2336 = true := by
  decide +kernel

theorem chunk_2338 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2338 = true := by
  decide +kernel

end SandierSerfaty.CertData
