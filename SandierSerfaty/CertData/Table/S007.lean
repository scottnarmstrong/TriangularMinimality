/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 7 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `844, …, 873` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_844 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 844 = true := by
  decide +kernel

theorem chunk_846 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 846 = true := by
  decide +kernel

theorem chunk_848 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 848 = true := by
  decide +kernel

theorem chunk_850 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 850 = true := by
  decide +kernel

theorem chunk_852 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 852 = true := by
  decide +kernel

theorem chunk_854 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 854 = true := by
  decide +kernel

theorem chunk_856 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 856 = true := by
  decide +kernel

theorem chunk_858 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 858 = true := by
  decide +kernel

theorem chunk_860 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 860 = true := by
  decide +kernel

theorem chunk_862 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 862 = true := by
  decide +kernel

theorem chunk_864 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 864 = true := by
  decide +kernel

theorem chunk_866 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 866 = true := by
  decide +kernel

theorem chunk_868 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 868 = true := by
  decide +kernel

theorem chunk_870 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 870 = true := by
  decide +kernel

theorem chunk_872 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 872 = true := by
  decide +kernel

end SandierSerfaty.CertData
