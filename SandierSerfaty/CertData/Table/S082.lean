/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 82 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2400, …, 2429` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2400 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2400 = true := by
  decide +kernel

theorem chunk_2402 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2402 = true := by
  decide +kernel

theorem chunk_2404 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2404 = true := by
  decide +kernel

theorem chunk_2406 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2406 = true := by
  decide +kernel

theorem chunk_2408 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2408 = true := by
  decide +kernel

theorem chunk_2410 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2410 = true := by
  decide +kernel

theorem chunk_2412 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2412 = true := by
  decide +kernel

theorem chunk_2414 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2414 = true := by
  decide +kernel

theorem chunk_2416 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2416 = true := by
  decide +kernel

theorem chunk_2418 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2418 = true := by
  decide +kernel

theorem chunk_2420 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2420 = true := by
  decide +kernel

theorem chunk_2422 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2422 = true := by
  decide +kernel

theorem chunk_2424 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2424 = true := by
  decide +kernel

theorem chunk_2426 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2426 = true := by
  decide +kernel

theorem chunk_2428 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2428 = true := by
  decide +kernel

end SandierSerfaty.CertData
