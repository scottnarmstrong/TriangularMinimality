/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 84 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2460, …, 2489` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2460 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2460 = true := by
  decide +kernel

theorem chunk_2462 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2462 = true := by
  decide +kernel

theorem chunk_2464 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2464 = true := by
  decide +kernel

theorem chunk_2466 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2466 = true := by
  decide +kernel

theorem chunk_2468 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2468 = true := by
  decide +kernel

theorem chunk_2470 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2470 = true := by
  decide +kernel

theorem chunk_2472 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2472 = true := by
  decide +kernel

theorem chunk_2474 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2474 = true := by
  decide +kernel

theorem chunk_2476 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2476 = true := by
  decide +kernel

theorem chunk_2478 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2478 = true := by
  decide +kernel

theorem chunk_2480 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2480 = true := by
  decide +kernel

theorem chunk_2482 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2482 = true := by
  decide +kernel

theorem chunk_2484 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2484 = true := by
  decide +kernel

theorem chunk_2486 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2486 = true := by
  decide +kernel

theorem chunk_2488 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2488 = true := by
  decide +kernel

end SandierSerfaty.CertData
