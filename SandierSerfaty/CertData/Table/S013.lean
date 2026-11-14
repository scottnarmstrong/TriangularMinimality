/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 13 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1024, …, 1053` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1024 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1024 = true := by
  decide +kernel

theorem chunk_1026 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1026 = true := by
  decide +kernel

theorem chunk_1028 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1028 = true := by
  decide +kernel

theorem chunk_1030 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1030 = true := by
  decide +kernel

theorem chunk_1032 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1032 = true := by
  decide +kernel

theorem chunk_1034 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1034 = true := by
  decide +kernel

theorem chunk_1036 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1036 = true := by
  decide +kernel

theorem chunk_1038 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1038 = true := by
  decide +kernel

theorem chunk_1040 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1040 = true := by
  decide +kernel

theorem chunk_1042 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1042 = true := by
  decide +kernel

theorem chunk_1044 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1044 = true := by
  decide +kernel

theorem chunk_1046 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1046 = true := by
  decide +kernel

theorem chunk_1048 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1048 = true := by
  decide +kernel

theorem chunk_1050 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1050 = true := by
  decide +kernel

theorem chunk_1052 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1052 = true := by
  decide +kernel

end SandierSerfaty.CertData
