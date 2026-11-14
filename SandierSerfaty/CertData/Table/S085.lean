/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 85 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2490, …, 2519` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2490 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2490 = true := by
  decide +kernel

theorem chunk_2492 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2492 = true := by
  decide +kernel

theorem chunk_2494 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2494 = true := by
  decide +kernel

theorem chunk_2496 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2496 = true := by
  decide +kernel

theorem chunk_2498 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2498 = true := by
  decide +kernel

theorem chunk_2500 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2500 = true := by
  decide +kernel

theorem chunk_2502 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2502 = true := by
  decide +kernel

theorem chunk_2504 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2504 = true := by
  decide +kernel

theorem chunk_2506 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2506 = true := by
  decide +kernel

theorem chunk_2508 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2508 = true := by
  decide +kernel

theorem chunk_2510 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2510 = true := by
  decide +kernel

theorem chunk_2512 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2512 = true := by
  decide +kernel

theorem chunk_2514 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2514 = true := by
  decide +kernel

theorem chunk_2516 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2516 = true := by
  decide +kernel

theorem chunk_2518 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2518 = true := by
  decide +kernel

end SandierSerfaty.CertData
