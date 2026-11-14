/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 86 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2520, …, 2549` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2520 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2520 = true := by
  decide +kernel

theorem chunk_2522 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2522 = true := by
  decide +kernel

theorem chunk_2524 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2524 = true := by
  decide +kernel

theorem chunk_2526 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2526 = true := by
  decide +kernel

theorem chunk_2528 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2528 = true := by
  decide +kernel

theorem chunk_2530 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2530 = true := by
  decide +kernel

theorem chunk_2532 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2532 = true := by
  decide +kernel

theorem chunk_2534 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2534 = true := by
  decide +kernel

theorem chunk_2536 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2536 = true := by
  decide +kernel

theorem chunk_2538 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2538 = true := by
  decide +kernel

theorem chunk_2540 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2540 = true := by
  decide +kernel

theorem chunk_2542 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2542 = true := by
  decide +kernel

theorem chunk_2544 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2544 = true := by
  decide +kernel

theorem chunk_2546 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2546 = true := by
  decide +kernel

theorem chunk_2548 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2548 = true := by
  decide +kernel

end SandierSerfaty.CertData
