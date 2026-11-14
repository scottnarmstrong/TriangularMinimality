/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 87 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2550, …, 2579` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2550 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2550 = true := by
  decide +kernel

theorem chunk_2552 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2552 = true := by
  decide +kernel

theorem chunk_2554 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2554 = true := by
  decide +kernel

theorem chunk_2556 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2556 = true := by
  decide +kernel

theorem chunk_2558 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2558 = true := by
  decide +kernel

theorem chunk_2560 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2560 = true := by
  decide +kernel

theorem chunk_2562 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2562 = true := by
  decide +kernel

theorem chunk_2564 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2564 = true := by
  decide +kernel

theorem chunk_2566 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2566 = true := by
  decide +kernel

theorem chunk_2568 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2568 = true := by
  decide +kernel

theorem chunk_2570 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2570 = true := by
  decide +kernel

theorem chunk_2572 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2572 = true := by
  decide +kernel

theorem chunk_2574 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2574 = true := by
  decide +kernel

theorem chunk_2576 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2576 = true := by
  decide +kernel

theorem chunk_2578 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2578 = true := by
  decide +kernel

end SandierSerfaty.CertData
