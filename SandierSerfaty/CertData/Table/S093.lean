/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 93 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2730, …, 2759` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2730 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2730 = true := by
  decide +kernel

theorem chunk_2732 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2732 = true := by
  decide +kernel

theorem chunk_2734 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2734 = true := by
  decide +kernel

theorem chunk_2736 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2736 = true := by
  decide +kernel

theorem chunk_2738 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2738 = true := by
  decide +kernel

theorem chunk_2740 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2740 = true := by
  decide +kernel

theorem chunk_2742 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2742 = true := by
  decide +kernel

theorem chunk_2744 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2744 = true := by
  decide +kernel

theorem chunk_2746 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2746 = true := by
  decide +kernel

theorem chunk_2748 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2748 = true := by
  decide +kernel

theorem chunk_2750 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2750 = true := by
  decide +kernel

theorem chunk_2752 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2752 = true := by
  decide +kernel

theorem chunk_2754 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2754 = true := by
  decide +kernel

theorem chunk_2756 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2756 = true := by
  decide +kernel

theorem chunk_2758 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2758 = true := by
  decide +kernel

end SandierSerfaty.CertData
