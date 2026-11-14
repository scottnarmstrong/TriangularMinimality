/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 90 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2640, …, 2669` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2640 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2640 = true := by
  decide +kernel

theorem chunk_2642 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2642 = true := by
  decide +kernel

theorem chunk_2644 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2644 = true := by
  decide +kernel

theorem chunk_2646 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2646 = true := by
  decide +kernel

theorem chunk_2648 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2648 = true := by
  decide +kernel

theorem chunk_2650 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2650 = true := by
  decide +kernel

theorem chunk_2652 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2652 = true := by
  decide +kernel

theorem chunk_2654 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2654 = true := by
  decide +kernel

theorem chunk_2656 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2656 = true := by
  decide +kernel

theorem chunk_2658 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2658 = true := by
  decide +kernel

theorem chunk_2660 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2660 = true := by
  decide +kernel

theorem chunk_2662 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2662 = true := by
  decide +kernel

theorem chunk_2664 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2664 = true := by
  decide +kernel

theorem chunk_2666 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2666 = true := by
  decide +kernel

theorem chunk_2668 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2668 = true := by
  decide +kernel

end SandierSerfaty.CertData
