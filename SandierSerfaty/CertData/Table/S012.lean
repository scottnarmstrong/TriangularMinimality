/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 12 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `994, …, 1023` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_994 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 994 = true := by
  decide +kernel

theorem chunk_996 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 996 = true := by
  decide +kernel

theorem chunk_998 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 998 = true := by
  decide +kernel

theorem chunk_1000 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1000 = true := by
  decide +kernel

theorem chunk_1002 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1002 = true := by
  decide +kernel

theorem chunk_1004 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1004 = true := by
  decide +kernel

theorem chunk_1006 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1006 = true := by
  decide +kernel

theorem chunk_1008 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1008 = true := by
  decide +kernel

theorem chunk_1010 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1010 = true := by
  decide +kernel

theorem chunk_1012 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1012 = true := by
  decide +kernel

theorem chunk_1014 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1014 = true := by
  decide +kernel

theorem chunk_1016 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1016 = true := by
  decide +kernel

theorem chunk_1018 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1018 = true := by
  decide +kernel

theorem chunk_1020 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1020 = true := by
  decide +kernel

theorem chunk_1022 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1022 = true := by
  decide +kernel

end SandierSerfaty.CertData
