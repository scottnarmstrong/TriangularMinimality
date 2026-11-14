/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 91 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2670, …, 2699` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2670 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2670 = true := by
  decide +kernel

theorem chunk_2672 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2672 = true := by
  decide +kernel

theorem chunk_2674 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2674 = true := by
  decide +kernel

theorem chunk_2676 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2676 = true := by
  decide +kernel

theorem chunk_2678 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2678 = true := by
  decide +kernel

theorem chunk_2680 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2680 = true := by
  decide +kernel

theorem chunk_2682 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2682 = true := by
  decide +kernel

theorem chunk_2684 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2684 = true := by
  decide +kernel

theorem chunk_2686 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2686 = true := by
  decide +kernel

theorem chunk_2688 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2688 = true := by
  decide +kernel

theorem chunk_2690 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2690 = true := by
  decide +kernel

theorem chunk_2692 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2692 = true := by
  decide +kernel

theorem chunk_2694 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2694 = true := by
  decide +kernel

theorem chunk_2696 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2696 = true := by
  decide +kernel

theorem chunk_2698 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2698 = true := by
  decide +kernel

end SandierSerfaty.CertData
