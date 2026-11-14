/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 88 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2580, …, 2609` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2580 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2580 = true := by
  decide +kernel

theorem chunk_2582 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2582 = true := by
  decide +kernel

theorem chunk_2584 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2584 = true := by
  decide +kernel

theorem chunk_2586 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2586 = true := by
  decide +kernel

theorem chunk_2588 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2588 = true := by
  decide +kernel

theorem chunk_2590 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2590 = true := by
  decide +kernel

theorem chunk_2592 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2592 = true := by
  decide +kernel

theorem chunk_2594 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2594 = true := by
  decide +kernel

theorem chunk_2596 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2596 = true := by
  decide +kernel

theorem chunk_2598 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2598 = true := by
  decide +kernel

theorem chunk_2600 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2600 = true := by
  decide +kernel

theorem chunk_2602 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2602 = true := by
  decide +kernel

theorem chunk_2604 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2604 = true := by
  decide +kernel

theorem chunk_2606 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2606 = true := by
  decide +kernel

theorem chunk_2608 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2608 = true := by
  decide +kernel

end SandierSerfaty.CertData
