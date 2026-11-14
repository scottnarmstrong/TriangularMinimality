/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 92 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2700, …, 2729` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2700 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2700 = true := by
  decide +kernel

theorem chunk_2702 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2702 = true := by
  decide +kernel

theorem chunk_2704 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2704 = true := by
  decide +kernel

theorem chunk_2706 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2706 = true := by
  decide +kernel

theorem chunk_2708 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2708 = true := by
  decide +kernel

theorem chunk_2710 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2710 = true := by
  decide +kernel

theorem chunk_2712 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2712 = true := by
  decide +kernel

theorem chunk_2714 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2714 = true := by
  decide +kernel

theorem chunk_2716 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2716 = true := by
  decide +kernel

theorem chunk_2718 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2718 = true := by
  decide +kernel

theorem chunk_2720 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2720 = true := by
  decide +kernel

theorem chunk_2722 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2722 = true := by
  decide +kernel

theorem chunk_2724 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2724 = true := by
  decide +kernel

theorem chunk_2726 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2726 = true := by
  decide +kernel

theorem chunk_2728 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2728 = true := by
  decide +kernel

end SandierSerfaty.CertData
