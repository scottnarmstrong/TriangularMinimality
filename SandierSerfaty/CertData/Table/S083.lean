/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 83 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2430, …, 2459` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2430 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2430 = true := by
  decide +kernel

theorem chunk_2432 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2432 = true := by
  decide +kernel

theorem chunk_2434 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2434 = true := by
  decide +kernel

theorem chunk_2436 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2436 = true := by
  decide +kernel

theorem chunk_2438 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2438 = true := by
  decide +kernel

theorem chunk_2440 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2440 = true := by
  decide +kernel

theorem chunk_2442 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2442 = true := by
  decide +kernel

theorem chunk_2444 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2444 = true := by
  decide +kernel

theorem chunk_2446 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2446 = true := by
  decide +kernel

theorem chunk_2448 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2448 = true := by
  decide +kernel

theorem chunk_2450 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2450 = true := by
  decide +kernel

theorem chunk_2452 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2452 = true := by
  decide +kernel

theorem chunk_2454 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2454 = true := by
  decide +kernel

theorem chunk_2456 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2456 = true := by
  decide +kernel

theorem chunk_2458 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2458 = true := by
  decide +kernel

end SandierSerfaty.CertData
